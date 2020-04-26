(*
 * Copyright (c) 2020 Romain Liautaud <romain.liautaud@tarides.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

(** Suite of tests for the tracing algorithm used during garbage collection.

    The suite uses the basic backend from `backend.ml` because it needs to
    intercept the calls to [filter] on the backend to know whether tracing
    is working as expected. *)

open Lwt.Infix

module type KVS = Irmin.KV with type contents = string

(* Creates a new Irmin store which logs which calls to [filter] are made on its
   underlying commit, node and content stores. Since we can't add functions to
   the signature of the AO store which we will pass to Content_addressable, we
   use a [is_reporting] flag which changes the behavior of [mem] at runtime:
    - When [not is_reporting], [mem] behaves normally.
    - Otherwise, [mem] returns whether [k] was preserved by calls to filter. *)
let create_mocking_store () =
  let is_reporting = ref false in
  let enable_reporting () = is_reporting := true in
  let disable_reporting () = is_reporting := false in

  ( ( module struct
      module Mocked_AO (K : Irmin.Type.S) (V : Irmin.Type.S) = struct
        include Backend.Append_only (K) (V)

        let predicates = ref []

        let filter t p =
          predicates := p :: !predicates;
          filter t p

        let mem t k =
          (* When [is_reporting] is true, [mem t k] returns whether [p k] is true
             for every filtering predicates [p] that was previously passed to the
             [filter] function on the store. In other words, it returns whether
             the store has been instructed to preserve the key [k] until now. *)
          if !is_reporting then (
            Printf.printf "%d\n" (List.length !predicates);
            Lwt.return @@ List.fold_left (fun b p -> b && p k) true !predicates
            )
          else (* Otherwise, [mem t k] behaves normally. *)
            mem t k
      end

      include Irmin.Make
                (Irmin.Content_addressable (Mocked_AO)) (Backend.Atomic_write)
                (Irmin.Metadata.None)
                (Irmin.Contents.String)
                (Irmin.Path.String_list)
                (Irmin.Branch.String)
                (Irmin.Hash.BLAKE2B)
    end : KVS ),
    enable_reporting,
    disable_reporting )

let config = Backend.config ()

(** Creates a fresh Irmin store pre-filled with the following example graph,
    sets the master branch to a given commit, and runs the garbage collector on
    the resulting store. Returns the store and the [assert_preserved] and
    [assert_purged] functions to use for testing.

    {v
        +------------------------------+
        |                              |
      +-+--+     +----+              /+v-+\                  +---+
      | C5 +-----> C4 +--+-----------> N4 +---------+---(/d)-> D |
      +-+--+     +----+  |           \+--+/        (/a)      +---+
        |                |                          |
        |                |  +----+   /+--+\      /+-v+\      +---+
        |                +--> C3 +---> N3 +-(/a)-> N3'+-(/c)-> C |
        |                |  +----+   \+--+/      \+-++/      +---+
        |                |                         (/b)
        |                |  +----+   /+--+\         |        +---+
        +-------------------> C2 +---> N2 +-(/a)----+--------> B |
                         |  +-+--+   \+--+/                  +---+
                         |    |
                         |  +-v--+   /+--+\                  +---+
                         +--> C1 +---> N1 +-(/a)-------------> A |
                            +----+   \+--+/                  +---+
    v} *)
let setup_tests target_commit =
  let (module Store), enable_reporting, disable_reporting =
    create_mocking_store ()
  in

  disable_reporting ();
  Store.Repo.v config >>= fun repo ->
  Store.master repo >>= fun t ->
  let info = Irmin.Info.none in
  let last_commit () = Store.Branch.get repo Store.Branch.master in
  let _show_graph () =
    let module Dot = Irmin.Dot (Store) in
    let buffer = Buffer.create 256 in
    let date d =
      let tm = Unix.localtime (Int64.to_float d) in
      Printf.sprintf "%2d:%2d:%2d" tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec
    in
    Dot.output_buffer t ~full:true ~date buffer >|= fun () ->
    print_endline (Buffer.contents buffer)
  in

  (* Fill the graph. *)
  Store.set_exn t [ "a" ] "A" ~info >>= fun () ->
  last_commit () >>= fun c1 ->
  Store.set_exn t [ "a" ] "B" ~info ~parents:[ c1 ] >>= fun () ->
  last_commit () >>= fun c2 ->
  Store.with_tree_exn t [ "a" ] ~info ~parents:[] ~strategy:`Set (fun tree ->
      let tree = match tree with Some t -> t | None -> Store.Tree.empty in
      Store.Tree.add tree [ "b" ] "B" >>= fun tree ->
      Store.Tree.add tree [ "c" ] "C" >>= Lwt.return_some)
  >>= fun () ->
  last_commit () >>= fun c3 ->
  Store.set_exn t [ "d" ] "D" ~info ~parents:[ c1; c3 ] >>= fun () ->
  last_commit () >>= fun c4 ->
  (* Retrieve the nodes. *)
  let n1 = Store.Commit.tree c1 in
  let n2 = Store.Commit.tree c2 in
  let n3 = Store.Commit.tree c3 in
  let n4 = Store.Commit.tree c4 in
  Store.Tree.get_tree n3 [ "a" ] >>= fun n3' ->
  (* Add the last commit. *)
  Store.set_tree_exn t [] n4 ~info ~parents:[ c2; c4 ] ~allow_empty:true
  >>= fun () ->
  last_commit () >>= fun c5 ->
  (* Retrieve the contents. *)
  Store.Tree.get_tree n1 [ "a" ] >>= fun a ->
  Store.Tree.get_tree n2 [ "a" ] >>= fun b ->
  Store.Tree.get_tree n3' [ "c" ] >>= fun c ->
  Store.Tree.get_tree n4 [ "d" ] >>= fun d ->
  let open Store.Private in
  let commit_t = Repo.commit_t repo in
  let node_t = Repo.node_t repo in
  let contents_t = Repo.contents_t repo in

  (* Returns whether a graph object was preserved by the tracer. *)
  let was_preserved = function
    | `Commit c -> Commit.mem commit_t (Store.Commit.hash c)
    | `Node t -> Node.mem node_t (Store.Tree.hash t)
    | `Contents t -> Contents.mem contents_t (Store.Tree.hash t)
  in

  let find_object = function
    | `C1 -> `Commit c1
    | `C2 -> `Commit c2
    | `C3 -> `Commit c3
    | `C4 -> `Commit c4
    | `C5 -> `Commit c5
    | `N1 -> `Node n1
    | `N2 -> `Node n2
    | `N3 -> `Node n3
    | `N3' -> `Node n3'
    | `N4 -> `Node n4
    | `A -> `Contents a
    | `B -> `Contents b
    | `C -> `Contents c
    | `D -> `Contents d
  in

  let print_object = function
    | `C1 -> "`C1"
    | `C2 -> "`C2"
    | `C3 -> "`C3"
    | `C4 -> "`C4"
    | `C5 -> "`C5"
    | `N1 -> "`N1"
    | `N2 -> "`N2"
    | `N3 -> "`N3"
    | `N3' -> "`N3'"
    | `N4 -> "`N4"
    | `A -> "`A"
    | `B -> "`B"
    | `C -> "`C"
    | `D -> "`D"
  in

  (* Asserts that a graph object was preserved by the tracer. *)
  let assert_preserved id =
    let message = Printf.sprintf "Object %s was preserved" (print_object id) in
    find_object id |> was_preserved >|= Alcotest.(check bool) message true
  in

  (* Asserts that a graph object was purged by the tracer. *)
  let assert_purged id =
    let message = Printf.sprintf "Object %s was purged" (print_object id) in
    find_object id |> was_preserved >|= Alcotest.(check bool) message false
  in

  (* Sets the master branch of the store to the given commit. *)
  let set_master id =
    match find_object id with
    | `Commit c -> Store.Branch.set repo "master" c
    | _ -> Lwt.fail_with "Setting master to something other than a commit."
  in

  set_master target_commit >>= fun () ->
  (* Run the garbage collector. *)
  Store.Repo.cleanup repo >>= fun () ->
  enable_reporting ();

  Lwt.return ((module Store : KVS), assert_preserved, assert_purged)

let iter = Lwt_list.iter_p

let master_to_C1 () =
  setup_tests `C1 >>= fun (_, assert_preserved, assert_purged) ->
  iter assert_preserved [ `C1 ] >>= fun () ->
  iter assert_preserved [ `N1 ] >>= fun () ->
  iter assert_preserved [ `A ] >>= fun () ->
  iter assert_purged [ `C2; `C3; `C4; `C5 ] >>= fun () ->
  iter assert_purged [ `N2; `N3; `N4 ] >>= fun () ->
  iter assert_purged [ `B; `C; `D ]

let master_to_C2 () =
  setup_tests `C2 >>= fun (_, assert_preserved, assert_purged) ->
  iter assert_preserved [ `C1; `C2 ] >>= fun () ->
  iter assert_preserved [ `N1; `N2 ] >>= fun () ->
  iter assert_preserved [ `A; `B ] >>= fun () ->
  iter assert_purged [ `C3; `C4; `C5 ] >>= fun () ->
  iter assert_purged [ `N3; `N4; `C; `D ]

let master_to_C3 () =
  setup_tests `C3 >>= fun (_, assert_preserved, assert_purged) ->
  iter assert_preserved [ `C3 ] >>= fun () ->
  iter assert_preserved [ `N3; `N3' ] >>= fun () ->
  iter assert_preserved [ `B; `C ] >>= fun () ->
  iter assert_purged [ `C1; `C2; `C4; `C5 ] >>= fun () ->
  iter assert_purged [ `N1; `N2; `N4 ] >>= fun () ->
  iter assert_purged [ `A; `D ]

let master_to_C4 () =
  setup_tests `C4 >>= fun (_, assert_preserved, assert_purged) ->
  iter assert_preserved [ `C1; `C3; `C4 ] >>= fun () ->
  iter assert_preserved [ `N1; `N3; `N3'; `N4 ] >>= fun () ->
  iter assert_preserved [ `A; `B; `C; `D ] >>= fun () ->
  iter assert_purged [ `C2; `C5; `N2 ]

let master_to_C5 () =
  setup_tests `C5 >>= fun (_, assert_preserved, _assert_purged) ->
  iter assert_preserved [ `C1; `C2; `C3; `C4; `C5 ] >>= fun () ->
  iter assert_preserved [ `N1; `N2; `N3; `N3'; `N4 ] >>= fun () ->
  iter assert_preserved [ `A; `B; `C; `D ]

(* Turns a test returning a [unit Lwt.t] into a runnable test. *)
let runnable f () = Lwt_main.run (f ())

let suite =
  [
    ( "tracing",
      [
        ("master_to_C1", `Quick, runnable master_to_C1);
        ("master_to_C2", `Quick, runnable master_to_C2);
        ("master_to_C3", `Quick, runnable master_to_C3);
        ("master_to_C4", `Quick, runnable master_to_C4);
        ("master_to_C5", `Quick, runnable master_to_C5);
      ] );
  ]
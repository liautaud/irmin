.PHONY: all clean test fuzz doc examples

all:
	dune build

test:
	dune runtest

fuzz:
	dune build @fuzz --no-buffer

examples:
	dune build @examples

clean:
	dune clean

doc:
	dune build @doc

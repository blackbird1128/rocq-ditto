
all:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release 
	dune exec fcc -- --plugin=ditto-plugin ./test/fixtures/ex_comment4.v

test:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release
	dune runtest --profile=release

PREFIX := $(HOME)/.local

install:
	rm vendor/fcc 
	cp ./_opam/bin/fcc vendor/fcc
	dune install --prefix="$(PREFIX)"

uninstall:
	dune uninstall --prefix="$(PREFIX)"
	rm vendor/fcc

dump-json:
	dune build lib --profile=release
	dune build test/json_dump/ --profile=release 
	dune exec fcc -- --plugin=dump-json-plugin ./test/fixtures/ex_comment3.v

clean:
	dune clean 

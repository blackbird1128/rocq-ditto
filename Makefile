
all:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release
	dune exec fcc -- --plugin=ditto-plugin ./test/fixtures/ex3.v

test:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release
	dune runtest --profile=release

PREFIX := $(HOME)/.local

install:
	dune install --prefix="$(PREFIX)"

uninstall:
	dune uninstall --prefix="$(PREFIX)"

clean:
	dune clean

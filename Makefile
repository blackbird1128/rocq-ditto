all:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release
	dune exec fcc -- --plugin=ditto-plugin ./test/fixtures/ex3.v

test:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release
	dune runtest --profile=release


all:
	dune build lib --profile=release
	dune build fcc_plugin
	dune exec fcc -- --plugin=ditto-plugin ./test/fixtures/ex4.v


all:
	dune build lib --profile=release
	dune build fcc_plugin
	dune exec fcc -- --plugin=ditto-plugin example1.v

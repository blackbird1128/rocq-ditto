
.PHONY: all test install uninstall dump-json clean

all:
	dune build lib --profile=release
	dune build fcc_plugin --profile=release
	dune exec fcc -- --plugin=ditto-plugin ./test/fixtures/ex_intros_trans.v

test:
	dune build . --profile=release
	dune build lib --profile=release
	dune build test/test_plugin/ --profile=release
	find test/fixtures/ -name "*_target.v"	-exec dune exec fcc -- --plugin=dump-json-plugin {} 2>/dev/null \;
	find test/fixtures -not -name "*_target.v"  -not -path '*/ignore/*'  -name '*.v' -exec  dune exec fcc -- --plugin=ditto-test-plugin {} 2>/dev/null \;
	dune runtest --profile=release	

PREFIX := $$HOME/.local

install:
	mkdir -p vendor/
	rm -rf vendor/fcc 
	cp ./_opam/bin/fcc ./vendor/fcc
	dune build . --profile=release
	dune build . @install --profile=release
	dune install --prefix=$(PREFIX)

uninstall:
	dune uninstall --prefix=$(PREFIX)
	rm -rf vendor/fcc

dump-json:
	dune build test/json_dump/ --profile=release
	dune exec fcc -- --plugin=dump-json-plugin ./test/fixtures/ex_comment3.v

clean:
	dune clean

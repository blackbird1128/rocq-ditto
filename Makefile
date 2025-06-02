
.PHONY: all test install uninstall dump-json clean

all:
	dune build --profile=release
	dune exec fcc -- --root=../private-geocoq/  --plugin=constructive-plugin --diags_level=2 ../private-geocoq/theories/Main/Tarski_dev/Ch04_cong_bet.v
	dune exec fcc -- --root=../private-geocoq/  --plugin=neat-fcc-plugin --diags_level=2 ../private-geocoq/theories/Constructive/Ch04_cong_bet_bis.v

#	DITTO_TRANSFORMATION=MAKE_INTROS_EXPLICIT dune exec fcc --  --plugin=constructive-plugin --diags_level=2 ./test/fixtures/constructive/ex2.v




test: all 
	dune build test/test_plugin/ --profile=release
	dune build ./test/test_target_generator_plugin --profile=release
	find test/fixtures/ -name "*_target.v"	-exec dune exec fcc -- --plugin=target-generator-plugin {} 2>/dev/null \;
	find test/fixtures -not -name "*_target.v"  -not -path '*/ignore/*'  -name '*.v' -exec  dune exec fcc -- --plugin=ditto-test-plugin {} 2>/dev/null \;
	dune runtest --profile=release	

PREFIX := $(HOME)/.local

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

dump-json: all
	dune build ./test/json_dump_plugin/ --profile=release
	dune exec fcc -- --plugin=json-dump-plugin ./test/fixtures/ex_subtree1.v

clean:
	dune clean

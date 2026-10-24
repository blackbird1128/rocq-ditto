PATTERN ?= *
V_TARGET_SRC := $(shell find test/fixtures/unit_test_fixtures/ -name "$(PATTERN)" -name '*_target.v')
V_TARGET_GEN := $(V_TARGET_SRC:%=%.target.json)

.PHONY: all build test dump-json clean

all: build

build:
	dune build

# Rule to generate a .v.target.json from its .v source
%.v.target.json: %.v
	dune exec fcc -- --plugin=target-generator-plugin $< 2>/dev/null

TEST_FILES := $(shell find test/fixtures/unit_test_fixtures \
	-not -name '*_target.v' \
	-not -path '*/ignore/*' \
	-name '*.v' | sort)

test: $(V_TARGET_GEN)
	dune build
	@failed=0; \
	if ! FCC_TEST=1 DITTO_TEST_COUNT=$(words $(TEST_FILES)) \
	dune exec --profile=release fcc -- \
		--display=quiet \
		--plugin=ditto-test-plugin \
		$(TEST_FILES); then \
	failed=1; \
	fi; \
	if ! dune runtest; then \
	failed=1; \
	fi; \
	exit $$failed

dump-json:
	dune build ./test/json_dump_plugin/ --profile=release
	dune exec fcc -- --plugin=json-dump-plugin ./test/fixtures/unit_test_fixtures/ex_reconstructing_stuck_together.v

clean:
	dune clean
	dune cache clear
	cp ./_opam/bin/fcc ./vendor/fcc
	rm -f ./lib/rocq_version_optcomp.mlh
	rm -f test/fixtures/unit_test_fixtures/*.target.json

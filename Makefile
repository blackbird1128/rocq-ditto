
PATTERN ?= *
V_TARGET_SRC := $(shell find test/fixtures/unit_test_fixtures/ -name "$(PATTERN)" -name '*_target.v')

# Define their corresponding generated files
V_TARGET_GEN := $(V_TARGET_SRC:%=%.target.json)

GEOCOQ_INPUT_DIR ?= ../private-geocoq/
GEOCOQ_OUTPUT_DIR ?= ../constructivisation_result/
NORMALISED_DIR ?= ../normalised_third_pass/
DITTO ?= dune exec --profile=release rocq-ditto --

CONSTRUCTIVISATION_FILES ?= \
	Ch02_cong.v \
	Ch03_bet.v \
	Ch04_cong_bet.v \
	Ch04_col.v \
	Ch05_bet_le.v \
	Ch06_out_lines.v \
	Ch07_midpoint.v \
	Ch08_orthogonality.v \
	Ch09_plane.v \
	Ch10_line_reflexivity.v \
	Ch10_line_reflexivity_2.v \
	Ch11_angles.v \
	Ch12_parallel.v \
	Ch12_parallel_inter_dec.v \
	Ch13_1.v \
	Ch13_2_length.v \
	Ch13_3_angles.v \
	Ch13_4_cos.v \
	Ch13_5_Pappus_Pascal.v \
	Ch13_6_Desargues_Hessenberg.v \
	Ch14_sum.v \
	Ch14_prod.v \
	Ch14_order.v \

CHAPTER_PATHS := $(addprefix $(NORMALISED_DIR)/theories/Main/Tarski_dev/, \
                  $(CONSTRUCTIVISATION_CHAPTERS))

ALL_CHAPTERS ?= \
	Ch02_cong.v \
	Ch03_bet.v \
	Ch04_col.v \
	Ch04_cong_bet.v \
	Ch05_bet_le.v \
	Ch06_out_lines.v \
	Ch07_midpoint.v \
	Ch08_orthogonality.v \
	Ch09_plane.v \
	Ch10_line_reflexivity.v \
	Ch10_line_reflexivity_2.v \
	Ch11_angles.v \
	Ch12_parallel.v \
	Ch12_parallel_inter_dec.v \
	Ch13_1.v \
	Ch13_2_length.v \
	Ch13_3_angles.v \
	Ch13_4_cos.v \
	Ch13_5_Pappus_Pascal.v \
	Ch13_6_Desargues_Hessenberg.v \
	Ch14_order.v \
	Ch14_prod.v \
	Ch14_sum.v \
	Ch15_lengths.v \
	Ch15_pyth_rel.v \
	Ch16_coordinates.v \


PERCENTAGE_CHAPTERS ?= \
	Ch04_cong_bet.v \
	Ch05_bet_le.v \
	Ch06_out_lines.v \
	Ch07_midpoint.v \
	Ch08_orthogonality.v \
	Ch09_plane.v \
	Ch10_line_reflexivity.v \
	Ch10_line_reflexivity_2.v \
	Ch11_angles.v \
	Ch12_parallel.v \
	Ch12_parallel_inter_dec.v \
	Ch13_1.v \
	Ch13_2_length.v \
	Ch13_3_angles.v \
	Ch13_4_cos.v \
	Ch13_5_Pappus_Pascal.v \


.PHONY: all test install uninstall dump-json clean constructivisation-uniformise constructivisation-build constructivisation-compile build constructivisation-data constructivisation-get-percentage count-induction

all:
	dune build

build:
	dune exec fcc -- --plugin=constructivisation-data-generator-plugin $(GEOCOQ_INPUT_DIR)/theories/Axioms/Definitions.v --no_vo
	dune build 

count-induction:
	@grep -riow "induction" $(CHAPTER_PATHS) | wc -l

proof_repair:
	dune build --profile=release
	dune exec fcc -- --plugin=shelley-plugin ./test/fixtures/ex_this_or_that.v

constructivisation-get-dep: build
	$(foreach chapter,$(ALL_CHAPTERS),\
		dune exec get-dependencies $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/$(chapter))


constructivisation-uniformise-1: build
	$(DITTO) -i $(GEOCOQ_INPUT_DIR) -o ../normalised_first_pass/ -t replace_induction_with_destruct --save-vo

constructivisation-uniformise-2: build
	$(DITTO) -i ../normalised_first_pass/ -o ../normalised_second_pass/ -t explicit_apply --save-vo

constructivisation-uniformise-3: build
	$(DITTO) -i ../normalised_second_pass/ -o ../normalised_third_pass/ -t add_proof_node_if_missing --save-vo

constructivisation-axioms: build
	$(DITTO) -i $(NORMALISED_DIR)/theories/Axioms/continuity_axioms.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Prelude/continuity_axioms.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Axioms/parallel_postulates.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Prelude/parallel_postulates.v -t constructivise_geocoq -v

constructivisation-build: build
	mkdir -p $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactics/
	mkdir -p $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactic_instances/
	mkdir -p $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Dimension_axioms/
	mkdir -p $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/
	mkdir -p $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/
	$(DITTO) -i $(NORMALISED_DIR)/theories/Axioms/parallel_postulates.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Prelude/parallel_postulates.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch02_cong.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch02_cong.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Models/tarski_to_cong_theory.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactic_instances/tarski_to_cong_theory.v  -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tactics/CongR.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactics/CongR.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch03_bet.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch03_bet.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch04_cong_bet.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch04_cong_bet.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch04_col.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch04_col.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch05_bet_le.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch05_bet_le.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch06_out_lines.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch06_out_lines.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Models/tarski_to_col_theory.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactic_instances/tarski_to_col_theory.v  -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tactics/ColR.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactics/ColR.v  -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch07_midpoint.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch07_midpoint.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch08_orthogonality.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch08_orthogonality.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/coplanar.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/coplanar.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch09_plane.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch09_plane.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Models/tarski_to_coinc_theory_for_cop.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactic_instances/tarski_to_coinc_theory_for_cop.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tactics/CoincR_for_cop.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Tactics/CoincR_for_cop.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Dimension_axioms/upper_dim_2.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Dimension_axioms/upper_dim_2.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch10_line_reflexivity.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch10_line_reflexivity.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch10_line_reflexivity_2.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch10_line_reflexivity_2.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/perp_bisect.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/perp_bisect.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch11_angles.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch11_angles.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Dimension_axioms/upper_dim_3.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Dimension_axioms/upper_dim_3.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/suma.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/suma.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch12_parallel.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch12_parallel.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/quadrilaterals.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/quadrilaterals.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/Tagged_predicates.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/Tagged_predicates.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/playfair_par_trans.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/playfair_par_trans.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/par_perp_perp_par_perp_2_par.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/par_perp_perp_par_perp_2_par.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/parallel_postulates_2.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/parallel_postulates_2.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch12_parallel_inter_dec.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch12_parallel_inter_dec.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/quadrilaterals_inter_dec.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/quadrilaterals_inter_dec.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/midpoint_theorems.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/midpoint_theorems.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/vectors.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/vectors.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/project.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/project.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/saccheri.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/saccheri.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Annexes/defect.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Annexes/defect.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch13_1.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch13_1.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/playfair_alternate_interior_angles.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/playfair_alternate_interior_angles.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/playfair_universal_posidonius_postulate.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/playfair_universal_posidonius_postulate.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/rah_thales_postulate.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/rah_thales_postulate.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/thales_converse_postulate_weak_triangle_circumscription_principle.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/thales_converse_postulate_weak_triangle_circumscription_principle.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/thales_postulate_thales_converse_postulate.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/thales_postulate_thales_converse_postulate.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/bachmann_s_lotschnittaxiom_variant.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/bachmann_s_lotschnittaxiom_variant.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/par_trans_NID.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/par_trans_NID.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/universal_posidonius_postulate_par_perp_perp.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/universal_posidonius_postulate_par_perp_perp.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/playfair_midpoint.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/playfair_midpoint.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Meta_theory/Parallel_postulates/tarski_playfair.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Parallel_postulates/tarski_playfair.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch13_2_length.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch13_2_length.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch13_3_angles.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch13_3_angles.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch13_4_cos.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch13_4_cos.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch13_5_Pappus_Pascal.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch13_5_Pappus_Pascal.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch13_6_Desargues_Hessenberg.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch13_6_Desargues_Hessenberg.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch14_sum.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch14_sum.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch14_prod.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch14_prod.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch14_order.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch14_order.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch15_lengths.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch15_lengths.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch16_coordinates.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch16_coordinates.v -t constructivise_geocoq -v
	$(DITTO) -i $(NORMALISED_DIR)/theories/Main/Tarski_dev/Ch15_pyth_rel.v  -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Ch15_pyth_rel.v -t constructivise_geocoq -v

constructivisation-compile:
	$(DITTO) -i $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Prelude.v -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/Prelude.v -t id_doc_transformation -v --save-vo
	$(foreach chapter,$(CONSTRUCTIVISATION_CHAPTERS),\
		$(DITTO) -i $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/$(chapter) -o $(GEOCOQ_OUTPUT_DIR)/theories/Constructive/$(chapter) -t id_doc_transformation -v --save-vo;)

constructivisation-get-percentage: build
	$(foreach chapter,$(ALL_CHAPTERS),\
		$(DITTO) -i $(GEOCOQ_OUTPUT_DIR)/theories/Main/Tarski_dev/$(chapter) -o $(GEOCOQ_OUTPUT_DIR)/theories/Main/Tarski_dev/$(chapter) -t constructivisation_get_percentage_admitted -v;)

constructivisation-print-destruct-target: build
	$(foreach chapter,$(ALL_CHAPTERS),\
		$(DITTO) -i ../private-geocoq/theories/Main/Tarski_dev/$(chapter) -o ../geocoq_out/theories/Main/Tarski_dev/$(chapter) -t constructivisation_print_destruct_target -v;)

# Rule to generate a .v.target.json from its .v source
%.v.target.json: %.v
	dune exec fcc -- --plugin=target-generator-plugin $< 2>/dev/null

test: $(V_TARGET_GEN)
	dune build
	find test/fixtures/unit_test_fixtures/ -not -name "*_target.v"  -not -path '*/ignore/*'  -name "$(PATTERN)" -name '*.v' -exec  dune exec fcc -- --plugin=ditto-test-plugin {} 2>/dev/null \;
	dune runtest

PREFIX := $(HOME)/.local

dump-json:
	dune build ./test/json_dump_plugin/ --profile=release
	dune exec fcc -- --plugin=json-dump-plugin ./test/fixtures/unit_test_fixtures/ex_reconstructing_stuck_together.v

constructivisation-data:
	@if [ -z "$(DEFINITIONS_V)" ]; then \
		echo "Set DEFINITIONS_V=path/to/Definitions.v"; \
		exit 1; \
	fi
	dune exec fcc -- --plugin=constructivisation-data-generator-plugin $(DEFINITIONS_V)

clean:
	dune clean
	dune cache clear
	cp ./_opam/bin/fcc ./vendor/fcc
	rm -f ./lib/rocq_version_optcomp.mlh
	rm -f test/fixtures/unit_test_fixtures/*.target.json

(lang dune 3.15)

(name coq-ditto)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name")

(maintainers "Maintainer Name")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name ditto-config)
 (synopsis "ditto configuration package")
 (description "package used to deduce configuration values")
 (depends ocaml dune base-unix))

(package
 (name coq-ditto)
 (synopsis "Rocq ditto lib")
 (description "libraries used by the plugins")
 (depends ocaml dune ppx_import coq-lsp base-unix re alcotest uuidm ppx_deriving_yojson ppx_deriving ppx_sexp_message ppx_sexp_value ppx_variants_conv logs)
 (tags
  (topics "to describe" your project)))

(package
  (name ditto-plugin)
  (synopsis "Basic Fleche plugin used by rocq-ditto to run transformation" )
  (allow_empty)
  (depends ocaml dune coq-lsp base-unix re coq-ditto)
 )

(package
  (name shelley-plugin)
  (synopsis "Plugin used to test proof repairs methods" )
  (allow_empty)
  (depends ocaml dune coq-lsp base-unix re coq-ditto)
)

(package
  (name lens-query-plugin)
  (synopsis "Plugin used to test the lens datastructure as a theorem query" )
  (allow_empty)
  (depends ocaml dune coq-lsp base-unix re coq-ditto)
 )

(package
 (name constructive-plugin)
 (synopsis "Plugin to constructivise GeoCoq")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto)
 )

(package
 (name get-basic-tactics-plugin)
 (synopsis "Plugin to get the basics tactics in a file")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto)
 )

(package
 (name neat-fcc-plugin)
 (synopsis "Compile a file and display eventual errors")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto)
 )

(package
 (name target-generator-plugin)
 (synopsis "Generate the jsons result used to compare test to their result ")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto))

(package
 (name ditto-test-plugin)
 (synopsis "Run the tests")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto uuidm))

(package
 (name json-dump-plugin)
 (synopsis "dump a Rocq-AST to JSON to explore internal representation")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto))



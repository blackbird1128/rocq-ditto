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
 (name coq-ditto)
 (synopsis "Coq ditto lib")
 (description "libraries used by the plugins")
 (depends ocaml dune coq-lsp base-unix re alcotest)
 (tags
  (topics "to describe" your project)))

(package
  (name ditto-plugin)
  (synopsis "Base Fleche plugin used to run transformation" )
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
 (depends ocaml dune coq-lsp base-unix re coq-ditto))

(package
 (name json-dump-plugin)
 (synopsis "dump a Coq-AST to JSON to explore internal representation")
 (allow_empty)
 (depends ocaml dune coq-lsp base-unix re coq-ditto))



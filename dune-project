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
  (allow_empty)
  (depends ocaml dune lsp coq-lsp base-unix re coq-ditto))

(package
 (name dump-json-plugin)
 (allow_empty)
 (depends ocaml dune lsp coq-lsp base-unix re coq-ditto))
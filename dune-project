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
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune lsp coq-lsp base-unix re ppx_deriving ppx_assert ppx_inline_test (alcotest :with-test))
 (tags
  (topics "to describe" your project)))

(package
  (name ditto-plugin)
  (allow_empty)
  (depends ocaml dune lsp coq-lsp base-unix re ditto))


; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html

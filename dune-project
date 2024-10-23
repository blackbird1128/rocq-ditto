(lang dune 3.16)

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
 (depends ocaml dune lsp coq-lsp base-unix re ppx-deriving ppx-inline-test)
 (tags
  (topics "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html

# Coq ditto

## Description

`coq-ditto` is a plugin and a library allowing to write transformations of Rocq proof scripts using the Rocq AST.
It use [coq-lsp](https://github.com/ejgallego/coq-lsp) to extract and run the Rocq AST of a file.

`coq-ditto` then provide utilities to add, delete and replace nodes in the AST, as well as extract proofs and 
transform them into different representations.

## install


### prerequisites

To install `coq-ditto`, you will first need a working and initialized `opam` installation.
You will also need the `gmp-dev` and `linux-headers` library.

Then if you want to install `coq-ditto` with the latest version of Rocq, use the following instructions:
```shell
opam switch -y create . ocaml-base-compiler --deps-only
eval $(opam env)
mkdir -p vendor/
cp ./_opam/bin/fcc ./vendor/fcc
dune build --profile=release
```
Otherwise, to install with a specific Rocq version, use the following instructions:
```shell
opam switch create . --empty
opam pin add coq-core $ROCQ_VERSION_HERE # (ie 8.20.0)
opam install . --deps-only
mkdir -p vendor/
cp ./_opam/bin/fcc ./vendor/fcc
dune build --profile=release
```

To run `coq-ditto` on a project needing Rocq libraries, install them in the same switch as `coq-ditto`

## running on a simple file

To first know what transformations are available, you can run the following command:

``` shell
dune exec --profile=release coq-ditto -- -t help
```

Then, to run the plugin on a single file, run the following command:

```shell
dune exec --profile=release coq-ditto -- -i FILENAME -o OUTPUT_NAME -t turn_into_one_liner
```
Where each transformations is one listed with the previous command. You can run multiple transformations in sequence by separating them by ",".

## running on a project

To run the plugin on a project, you must first install the project dependencies inside the opam switch of coq-ditto.
Then, you can run the following command
```shell
dune exec --profile=release coq-ditto -- -i PROJECT_FOLDER -o OUTPUT_FOLDER -t make_intros_explicit
```


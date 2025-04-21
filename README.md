# Coq ditto

## Description

`coq-ditto` is a plugin and a library allowing to write transformations of Coq proof scripts using the Coq AST.
It use [coq-lsp](https://github.com/ejgallego/coq-lsp) to extract and run the Coq AST of a file.

`coq-ditto` then provide utilities to add, delete and replace nodes in the AST, as well as extract proofs and 
transform them into different representations.

## install


### prerequisites

To install `coq-ditto`, you will first need a working and initialized `opam` installation.
You will also need the `gmp-dev` and `linux-headers` library.

Then run the following instructions:
```shell
opam switch -y create . ocaml-base-compiler --deps-only
eval $(opam env)
mkdir -p vendor/
cp ./_opam/bin/fcc ./vendor/fcc
dune build --profile=release
```

## running on a simple file

To first know what transformations are available, you can run the following command:

``` shell
DITTO_TRANSFORMATION=HELP dune exec fcc -- --root=file_folder  --plugin=ditto-plugin --diags_level=2 file.v
```

Then, to run the plugin on a single file, run the following command:

```shell
DITTO_TRANSFORMATION=T1,T2 dune exec fcc -- --root=file_folder --plugin=ditto-plugin --diags_level=2 file.v
```
Where each transformations is one listed with the previous command. You can run multiple transformations in sequence by separating them by ",".

## running on a library

To run the plugin on a library, you must first install the library dependencies inside the opam switch of coq-ditto.
Then, you can run the following command
```shell
DITTO_TRANSFORMATION=T1 dune exec fcc -- --root=files_root_folder --plugin=ditto-plugin $(coqdep -sort -f files_root_folder/_CoqProject) 
```


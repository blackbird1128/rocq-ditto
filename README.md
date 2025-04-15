# Coq ditto



## install

### prerequisites

To install `coq-ditto`, you will first need a working and initialized `opam` installation.
You will also need the `gmp-dev` and `linux-headers` library.

Then run the following instructions:
```shell
opam switch create . ocaml-base-compiler
opam install . --deps-only
eval $(opam env)
dune build
make
```

## running on a simple file

To first know what transformations are available, you can run the following command:

``` shell
DITTO_TRANSFORMATION=HELP dune exec fcc -- --plugin=ditto-plugin --diags_level=2 file.v
```

Then, to run the plugin on a single file, run the following command:

```shell
DITTO_TRANSFORMATION=T1,T2 dune exec fcc -- --plugin=ditto-plugin --diags_level=2 file.v
```
Where each transformations is one listed with the previous command. You can run multiple transformations in sequence by separating them by ",".

## running on a library

To run the plugin on multiple files, like for example a library, use find like this:
```shell
DITTO_TRANSFORMATION=T1 find ./library_folder/ -not -name "*_bis.v" -name '*.v' -exec  dune exec fcc -- --plugin=ditto-plugin {}  \;
```

Example:
to run the plugin on each `*.v` file of Geocoq
```shell
git clone https://github.com/GeoCoq/GeoCoq
opam repo add coq-released https://coq.inria.fr/opam/release
opam install coq-geocoq
DITTO_TRANSFORMATION=T1 find ./GeoCoq/ -not -name "*_bis.v" -name '*.v' -exec  dune exec fcc -- --plugin=ditto-plugin {}  \;
```

# Coq ditto

## install

To install and run follow the instructions below:
```shell
opam switch create . --deps-only
opam install . --deps-only
eval $(opam env)
dune build
make
```

## running on a simple file

To run the plugin on a single file, run the following command:

```shell
dune exec fcc -- --plugin=ditto-plugin --diags_level=2 file.v
```

## running on a library

To run the plugin on multiple files, like for example a library, use find like this:
```shell
find ./library_folder/ -not -name "*_bis.v" -name '*.v' -exec  dune exec fcc -- --plugin=ditto-plugin {}  \;
```

Example:
to run the plugin on each *.v file of Geocoq
```shell
git clone https://github.com/GeoCoq/GeoCoq
opam repo add coq-released https://coq.inria.fr/opam/release
opam install coq-geocoq
find ./GeoCoq/ -not -name "*_bis.v" -name '*.v' -exec  dune exec fcc -- --plugin=ditto-plugin {}  \;
```

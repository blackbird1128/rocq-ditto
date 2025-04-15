FROM ocaml/opam:alpine-ocaml-5.2

USER opam
RUN mkdir coq-ditto # owning issues otherwise
WORKDIR coq-ditto

USER root
RUN apk add --no-cache gmp-dev linux-headers

USER opam

COPY --chown=opam:opam ./dune-project dune-project
COPY --chown=opam:opam  *.opam ./
RUN opam install . --deps-only

COPY --chown=opam:opam ./lib/ lib/
COPY --chown=opam:opam ./fcc_plugin/ fcc_plugin/
COPY --chown=opam:opam ./test/ test/

RUN mkdir vendor
WORKDIR vendor

RUN cp /home/opam/.opam/5.2/bin/fcc fcc

WORKDIR ..

RUN eval $(opam env) &&  dune build . --profile=release


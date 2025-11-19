#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "Usage: $0 [latest|<rocq-version>]"
  echo "Example: $0 latest"
  echo "         $0 9.0.0"
  exit 1
}

if [[ $# -ne 1 ]]; then
  usage
fi

VERSION="$1"

if [[ "$VERSION" == "latest" ]]; then
  echo ">> Setting up with the latest Rocq version..."
  opam switch -y create . ocaml-base-compiler --deps-only
#  opam install -y rocq-stdlib
  eval "$(opam env)"
  mkdir -p vendor/
  ln -f  _opam/bin/rocq _opam/bin/coqc
  cp ./_opam/bin/fcc ./vendor/fcc
  make build
else
  echo ">> Setting up with Rocq version $VERSION..."
  opam switch create . ocaml-base-compiler.5.4.0 --no-install
  # Pin either rocq-core (>=9.0.0) or coq-core (<9.0.0)
  if [[ "$VERSION" =~ ^9\. ]]; then
    echo "Pinning rocq-core $VERSION..."
    opam pin add -y rocq-core "$VERSION"
    echo "Installing stdlib..."
#    opam install -y rocq-stdlib
  else
    echo "Pinning coq-core $VERSION..."
    opam pin add -y coq-core "$VERSION"
  fi
  opam install -y . --deps-only
  # For pinned Rocq version, dune still expects coqc to exist
  if [[ -f _opam/bin/rocq ]]; then
      ln -f _opam/bin/rocq _opam/bin/coqc
  fi
  mkdir -p vendor/
  cp ./_opam/bin/fcc ./vendor/fcc
  eval "$(opam env)"
  make build
fi

echo "Configuration completed successfully!"

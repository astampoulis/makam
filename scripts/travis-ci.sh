#!/usr/bin/env bash

set -ex
set -o pipefail

export MAKAM_BIN_URL=https://s3.amazonaws.com/makam-travis-artifacts/makam-mac-bin/makam-bin-darwin64-"$(./scripts/source-hash.sh)"
export OCAML_BIN_URL=https://s3.amazonaws.com/makam-travis-artifacts/ocaml-mac-bin/"$OPAM_SWITCH"/opam.tar.gz

# See if a build is needed.
# We only need to build on Travis if a new Makam binary needs to be produced;
# we're only using Travis to generate MacOS X binaries.

if [[ $(git log --format=oneline -n 1 $TRAVIS_COMMIT) == *"[travis-skip]"* ]] || ( wget --spider $MAKAM_BIN_URL 2>/dev/null ); then
  export BUILD_NEEDED="no"
  exit 0
else
  export BUILD_NEEDED="yes"
fi

if ( wget --spider $OCAML_BIN_URL 2>/dev/null ); then
  export OCAML_BIN_EXISTS="yes"
else
  export OCAML_BIN_EXISTS="no"
fi

# Install OPAM and OCaml

brew install gpatch https://raw.githubusercontent.com/Homebrew/homebrew-core/7cfc8ee1d8d2bff2f7545170936a9abdb4662547/Formula/opam.rb || true

if [[ $OCAML_BIN_EXISTS == "yes" ]]; then
  (cd ~; wget -q $OCAML_BIN_URL; tar xzf opam.tar.gz; rm opam.tar.gz)
else
  mkdir -p travis-artifacts/ocaml-mac-bin/"$OPAM_SWITCH"
  opam init --yes --comp="$OPAM_SWITCH"
  (export MAIN_DIR=$(pwd); cd ~; tar czf $MAIN_DIR/travis-artifacts/ocaml-mac-bin/"$OPAM_SWITCH"/opam.tar.gz .opam)
fi

eval $(opam config env)

# Install dependencies

opam update --yes
opam switch create ./ --yes
npm install -g yarn

# Compile Makam

opam config exec make

# Make sure that it can run the prelude, as a sanity check

echo "" | ./makam --cache-dir=stdlib-cache

# Move the binary over to the right location

mkdir -p travis-artifacts/makam-mac-bin
cp nativerepl.native travis-artifacts/makam-mac-bin/makam-bin-darwin64-"$(./scripts/source-hash.sh)"

echo 1 > upload-makam-bin
if [[ $OCAML_BIN_EXISTS == "no" ]]; then echo 1 > upload-ocaml-bin; fi

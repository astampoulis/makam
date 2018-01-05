#!/usr/bin/env bash

set -e

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <version>"
  exit 1
fi

VERSION=$1

sed -i -r -e "s/^Version:     .*$/Version:     $VERSION/" _oasis
sed -i -r -e "s/^version: \"[^\"]+\"/version: \"$VERSION\"/" opam/opam
sed -i -r -e "s/version = \"[^\"]+\"/version = \"$VERSION\"/" toploop/version.ml
sed -i -r -e "s/version = \"[^\"]+\"/version = \"$VERSION\"/" js/index.html
sed -i -r -e "s/\"version\": \"[^\"]+\"/\"version\": \"$VERSION\"/" npm/package.json

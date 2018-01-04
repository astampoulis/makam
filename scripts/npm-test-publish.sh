#!/usr/bin/env bash

set -e
set -o pipefail

npm whoami >/dev/null

cp -f nativerepl.native npm/makam-bin-linux64
cp -f README.md npm/

STDLIB_FILES=$(grep -E --only-matching "stdlib/[^\"]+" opam/files/makam.install | uniq)
rsync --del --archive --del --relative --verbose $STDLIB_FILES npm/

BASEVERSION=$(node -p "require('./npm/package.json').version")
VERSION=$BASEVERSION-test-$(git rev-parse --short HEAD)

(cd npm;
 npm version $VERSION;
 set +e; npm publish --tag test; RES=$?;
 npm version $BASEVERSION;
 exit $RES)

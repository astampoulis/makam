#!/usr/bin/env bash

set -e
set -o pipefail

npm whoami >/dev/null

cp -f nativerepl.native npm/makam-bin-linux64
cp -f README.md npm/

rm -rf npm/stdlib/
cp -R stdlib npm/

BASEVERSION=$(node -p "require('./npm/package.json').version")
VERSION=$BASEVERSION-test-$(git rev-parse --short HEAD)

(cd npm;
 npm version $VERSION;
 set +e; npm publish; RES=$?;
 npm version $BASEVERSION;
 exit $RES)

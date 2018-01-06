#!/usr/bin/env bash

set -e
set -o pipefail

npm whoami >/dev/null

OPAM_MAKAM_BIN=$(opam config var makam:lib)/makam-bin
if [[ -e $OPAM_MAKAM_BIN && \
      $($OPAM_MAKAM_BIN --version | cut -d':' -f 2) == $(./scripts/source-hash.sh) ]]; then
  echo Using makam binary from opam
  cp $OPAM_MAKAM_BIN npm/makam-bin-linux64
else
  make build && cp -f nativerepl.native npm/makam-bin-linux64
fi

cp -f README.md npm/

STDLIB_FILES=$(grep -E --only-matching "stdlib/[^\"]+" opam/files/makam.install | uniq)
rsync --del --archive --del --relative --verbose $STDLIB_FILES npm/

(cd npm; yarn install; yarn build)

# Generate result cache for stdlib so that startup time is fast
(cd npm; rm -rf stdlib-cache; echo "" | yarn makam --cache-dir=stdlib-cache)

BASEVERSION=$(./scripts/makam-version.sh)
TESTVERSION=$(./scripts/makam-version.sh npm-test-version)

(cd npm;
 npm version $TESTVERSION;
 set +e; npm publish --tag test; RES=$?;
 npm version $BASEVERSION;
 exit $RES)

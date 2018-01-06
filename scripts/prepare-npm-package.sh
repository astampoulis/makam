#!/usr/bin/env bash

set -e
set -o pipefail

TOPDIR=$(git rev-parse --show-toplevel)
BASEVERSION=$($TOPDIR/scripts/makam-version.sh)

if [[ $# -lt 1 ]]; then
  UPDATE_VERSION=0
  PACKAGEVERSION=$BASEVERSION
else
  UPDATE_VERSION=1
  PACKAGEVERSION=$1
fi

# OPAM_MAKAM_BIN=$(opam config var makam:lib)/makam-bin
# if [[ -e $OPAM_MAKAM_BIN && \
#       $($OPAM_MAKAM_BIN --version | cut -d':' -f 2) == $($TOPDIR/scripts/source-hash.sh) ]]; then
#   echo Using makam binary from opam
#   cp $OPAM_MAKAM_BIN $TOPDIR/npm/makam-bin-linux64
# else
#   (cd $TOPDIR; make build && cp -f nativerepl.native npm/makam-bin-linux64)
# fi

cp -f $TOPDIR/nativerepl.native $TOPDIR/npm/makam-bin-linux64

cp -f $TOPDIR/README.md $TOPDIR/npm/

STDLIB_FILES=$(cd $TOPDIR; grep -E --only-matching "stdlib/[^\"]+" opam/files/makam.install | uniq)
(cd $TOPDIR; rsync --del --archive --del --relative --verbose $STDLIB_FILES npm/)

(cd $TOPDIR/npm; yarn install; yarn build; rm -rf node_modules; yarn install --prod)

# Generate result cache for stdlib so that startup time is fast
(cd $TOPDIR/npm; rm -rf stdlib-cache; echo "" | yarn makam --cache-dir=stdlib-cache)

(cd $TOPDIR/npm;
 [[ $UPDATE_VERSION -eq 1 ]] && npm version $PACKAGEVERSION;
 set +e; npm pack; RES=$?;
 [[ $UPDATE_VERSION -eq 1 ]] && npm version $BASEVERSION;
 mv makam-$PACKAGEVERSION.tgz $TOPDIR/;
 exit $RES)

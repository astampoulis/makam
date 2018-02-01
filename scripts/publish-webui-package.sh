#!/usr/bin/env bash

set -e
set -o pipefail

TOPDIR=$(git rev-parse --show-toplevel)
BASEVERSION=$($TOPDIR/scripts/makam-version.sh)
SOURCEHASH=$($TOPDIR/scripts/source-hash.sh)

if [[ ${1:-x} == "prod" ]]; then
  TEST_VERSION=0
  UPDATE_VERSION=0
  PACKAGEVERSION=$BASEVERSION
elif [[ ${1:-x} == "x" ]]; then
  TEST_VERSION=1
  UPDATE_VERSION=1
  PACKAGEVERSION=$($TOPDIR/scripts/makam-version.sh npm-test-version)
else
  echo "Usage: $0 [prod]"
  exit 1
fi

(cd $TOPDIR/webui; yarn install; yarn build)

(cd $TOPDIR/webui;
 [[ $UPDATE_VERSION -eq 1 ]] && npm version $PACKAGEVERSION;
 rm -f $TOPDIR/makam-webui-$PACKAGEVERSION.tgz;
 set +e; npm pack; RES=$?; set -e;
 [[ $UPDATE_VERSION -eq 1 ]] && npm version $BASEVERSION;
 mv makam-webui-$PACKAGEVERSION.tgz $TOPDIR/;
 if [[ $RES -ne 0 ]]; then exit $RES; fi)

npm whoami >/dev/null

if [[ $TEST_VERSION -eq 1 ]]; then
  (cd $TOPDIR; echo npm publish --tag test makam-webui-$PACKAGEVERSION.tgz)
else
  (cd $TOPDIR; echo npm publish makam-webui-$PACKAGEVERSION.tgz)
fi

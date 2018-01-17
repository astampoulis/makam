#!/bin/bash

set -e

TOPDIR=$(git rev-parse --show-toplevel)

if [[ ${1:x} == "prod" ]]; then
  PACKAGE_VERSION=$(cd $TOPDIR; ./scripts/makam-version.sh)
  STAGE=prod
elif [[ ${1:-x} == "x" ]]; then
  DO_TEST=1
  PACKAGE_VERSION=$(cd $TOPDIR; ./scripts/makam-version.sh npm-test-version)
  STAGE=dev
else
  cat <<EOF
Usage: $0 [prod]

$(basename $0)       -- Update test npm package, deploy webservice to dev and test
$(basename $0) prod  -- Deploy webservice to prod

EOF
  exit 1
fi

[[ $DO_TEST -eq 1 ]] && (cd $TOPDIR; ./scripts/source-hash.sh update; make prepare-test-npm-package)

(cd $TOPDIR/webservice;

 yarn;
 rm -rf node_modules/makam;
 tar xzf ../makam-$PACKAGE_VERSION.tgz;
 mv package node_modules/makam;

 if [[ $STAGE == dev ]]; then
   ./node_modules/.bin/sls deploy function --stage $STAGE -f makamQuery
 else
   ./node_modules/.bin/sls deploy --stage $STAGE
 fi)

if [[ $DO_TEST -eq 1 ]]; then

  curl -X POST \
    https://0l0h0ccxff.execute-api.us-east-1.amazonaws.com/dev/makam/query \
    -H 'content-type: application/json' \
    -d '{ "stateBlocks": [ "foo: prop.", "foo :- print_string \"hello\".", "foo ?" ], "query": "foo ?" }' | jq

fi

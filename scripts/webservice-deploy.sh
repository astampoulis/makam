#!/bin/bash

set -e

TEST_BASE_URL=https://0l0h0ccxff.execute-api.us-east-1.amazonaws.com/dev
PROD_BASE_URL=https://hwtoumy97e.execute-api.us-east-1.amazonaws.com/prod
LOCAL_BASE_URL=http://127.0.0.1:3000/

function usage {
  cat <<EOF
Usage: $0 [local|prod|<stage>]

$(basename $0)         -- Update test npm package, deploy webservice to dev and test
$(basename $0) prod    -- Deploy webservice to prod
$(basename $0) <stage> -- Deploy webservice to other stage
$(basename $0) local   -- Run webservice locally


EOF
}

TOPDIR=$(git rev-parse --show-toplevel)

if [[ ${1:-x} == "--help" ]]; then
  usage
  exit 0
fi

if [[ ${PACKAGE_VERSION:-x} != "x" ]]; then

  if [[ ! -e $TOPDIR/makam-${PACKAGE_VERSION}.tgz ]]; then
    echo "Downloading makam-${PACKAGE_VERSION}..."
    (cd $TOPDIR; npm pack "makam@${PACKAGE_VERSION}")
  fi
  DO_BUILD=0

elif [[ ${1:-x} == "x" || ${1:-x} == "local" ]]; then

  PACKAGE_VERSION=$(cd $TOPDIR; ./scripts/makam-version.sh npm-test-version)

elif [[ ${1:-x} == "prod" ]]; then

  PACKAGE_VERSION=$(cd $TOPDIR; ./scripts/makam-version.sh)

else

  echo "A Makam package version needs to be specified to deploy to stage $1 through the environment variable PACKAGE_VERSION"
  exit 1

fi

if [[ ${1:x} == "prod" ]]; then
  STAGE=prod
  BASE_URL=$PROD_BASE_URL
elif [[ ${1:-x} == "local" ]]; then
  DO_BUILD=${DO_BUILD:-1}
  DO_TEST=${DO_TEST:-0}
  BASE_URL=$LOCAL_BASE_URL
  STAGE=local
elif [[ ${1:-x} == "x" ]]; then
  DO_BUILD=${DO_BUILD:-1}
  DO_TEST=${DO_TEST:-1}
  BASE_URL=$TEST_BASE_URL
  STAGE=dev
else
  STAGE=$1
fi

[[ $DO_BUILD -eq 1 ]] && (cd $TOPDIR; ./scripts/source-hash.sh update; make prepare-test-npm-package)

(cd $TOPDIR/webservice;

 yarn;
 rm -rf node_modules/makam;
 tar xzf ../makam-$PACKAGE_VERSION.tgz;
 mv package node_modules/makam;

 if [[ $STAGE == dev ]]; then
   ./node_modules/.bin/sls deploy function --stage $STAGE -f makamQuery
 elif [[ $STAGE == local ]]; then
   ./node_modules/.bin/sls offline
 else
   ./node_modules/.bin/sls deploy --stage $STAGE
 fi)

if [[ $DO_TEST -eq 1 ]]; then

  curl -X POST \
    $BASE_URL/makam/query \
    -H 'content-type: application/json' \
    -d '{ "stateBlocks": [ "foo: prop.", "foo :- print_string \"hello\".", "foo ?" ], "query": "foo ?" }' | jq

fi

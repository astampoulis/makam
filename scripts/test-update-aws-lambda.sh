#!/bin/bash

set -e


TOPDIR=$(git rev-parse --show-toplevel)

$TOPDIR/scripts/source-hash.sh update
(cd $TOPDIR; make prepare-test-npm-package)

(cd $TOPDIR/webservice;

 rm -rf node_modules/makam;

 tar xzf ../makam-$(../scripts/makam-version.sh npm-test-version).tgz;
 mv package node_modules/makam;

 ./node_modules/.bin/sls deploy function --stage dev -f makamQuery)

curl -X POST \
  https://0l0h0ccxff.execute-api.us-east-1.amazonaws.com/dev/makam/query \
  -H 'content-type: application/json' \
  -d '{ "stateBlocks": [ "foo: prop.", "foo :- print_string \"hello\".", "foo ?" ], "query": "foo ?" }' | jq

# sls logs -f makamQuery

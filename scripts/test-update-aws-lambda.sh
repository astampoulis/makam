#!/bin/bash

set -e


TOPDIR=$(git rev-parse --show-toplevel)

$TOPDIR/scripts/source-hash.sh update
(cd $TOPDIR; make prepare-test-npm-package)

(cd $TOPDIR/webservice;
 rm -rf package &&
 tar xzf ../makam-$(../scripts/makam-version.sh npm-test-version).tgz &&
 sls deploy function -f makamQuery)

curl -X POST \
  https://3ta0k0voh5.execute-api.us-east-1.amazonaws.com/dev/makam/query \
  -H 'content-type: application/json' \
  -d '{ "input": [ "print_string \"hello\" ?"] }' | jq

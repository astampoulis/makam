#!/bin/bash

if [[ ${1:x} == "refresh" ]]; then

 ../scripts/source-hash.sh update
 (cd ../; make prepare-test-npm-package)

 rm -rf node_modules/makam;
 tar xzf ../makam-$(../scripts/makam-version.sh npm-test-version).tgz;
 mv package node_modules/makam;

fi

rm -f /tmp/makam-{state,output}-*
node -e 'var x = JSON.stringify({ "stateBlocks": [ "foo: prop.", "foo :- print_string \"hello\", log_error X `oops`.", "foo ?" ], "query": "foo ? print_string \"lala\" ?" }); console.log(JSON.stringify({body: x}))' | SLS_DEBUG=* sls invoke local -f makamQuery

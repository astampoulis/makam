#!/bin/bash

rm -f /tmp/makam-{state,output}-*
node -e 'var x = JSON.stringify({ "stateBlocks": [ "foo: prop.", "foo :- print_string \"hello\", log_error X `oops`.", "foo ?" ], "query": "foo ? print_string \"lala\" ?" }); console.log(JSON.stringify({body: x}))' | SLS_DEBUG=* sls invoke local -f makamQuery

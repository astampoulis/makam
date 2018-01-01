#!/bin/bash

TIMING_DEADLINE="65.0"
NOCACHE_REFERENCE="91.0"

set -eux
set -o pipefail

make cache-clean
COMMAND="make makam-tests"

node scripts/time.js 1 "$COMMAND" | tee nocache_time
node scripts/time.js 1 "$COMMAND" | tee cache_time

NOCACHE_TIME=$(tail -n 1 nocache_time)
CACHE_TIME=$(tail -n 1 cache_time)

rm nocache_time cache_time

( eval $(node -e "console.log(($CACHE_TIME / $NOCACHE_TIME) < 0.75 ? true : false)") ) &&
( eval $(node -e "console.log($CACHE_TIME < $TIMING_DEADLINE * ($NOCACHE_TIME / $NOCACHE_REFERENCE) ? true : false)") ) ||
(echo "Timing regression"; exit 1)

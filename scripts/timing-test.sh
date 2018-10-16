#!/bin/bash

TIMING_DEADLINE="85.0"
NOCACHE_REFERENCE="140.0"

set -eux
set -o pipefail

make cache-clean
COMMAND="make makam-tests"

node scripts/time.js 1 "$COMMAND" | tee nocache_time
NOCACHE_TIME=$(tail -n 1 nocache_time)

# allow a 20% window (CircleCI speed is unpredictable)
( eval $(node -e "console.log($NOCACHE_TIME / $NOCACHE_REFERENCE < 1.20 ? true : false)") ) ||
( echo "Timing regression: everything got slower"; exit 1 )

node scripts/time.js 1 "$COMMAND" | tee cache_time
CACHE_TIME=$(tail -n 1 cache_time)

rm nocache_time cache_time

( eval $(node -e "console.log(($CACHE_TIME / $NOCACHE_TIME) < 0.75 ? true : false)") ) &&
( eval $(node -e "console.log($CACHE_TIME < $TIMING_DEADLINE * Math.max(0.95, ($NOCACHE_TIME / $NOCACHE_REFERENCE)) ? true : false)") ) ||
(echo "Timing regression: cached stuff got slower"; exit 1)

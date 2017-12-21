#!/bin/bash

set -eux

make cache-clean
COMMAND="make makam-tests"

NOCACHE_TIME=$(node scripts/time.js 1 "$COMMAND" | tail -n 1)
CACHE_TIME=$(node scripts/time.js 1 "$COMMAND" | tail -n 1)

( eval $(node -e "console.log(($CACHE_TIME / $NOCACHE_TIME) < 0.75 ? true : false)") ) &&
( eval $(node -e "console.log($CACHE_TIME < 60.0 ? true : false)") ) ||
(echo "Timing regression"; exit 1)

#!/bin/bash

set -eux
set -o pipefail

make cache-clean
COMMAND="make makam-tests-timed"

( time -p bash -c "$COMMAND; echo 'total time:'" ) 2>&1 | tee nocache_time

( time -p bash -c "$COMMAND; echo 'total time:'" ) 2>&1 | tee cache_time

if [[ "${CI-}" == "true" ]]; then
  mkdir /tmp/artifacts
  mv {no,}cache_time /tmp/artifacts/
fi

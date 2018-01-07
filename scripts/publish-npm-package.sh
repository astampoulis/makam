#!/usr/bin/env bash

set -e
set -o pipefail

npm whoami >/dev/null

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <tgz package>"
  exit 1
fi

if ( echo $1 | grep -q "\-test\-" - ); then
  npm publish --tag test $1
else
  npm publish $1
fi

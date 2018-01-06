#!/usr/bin/env bash

set -e
set -o pipefail

TOPDIR=$(git rev-parse --show-toplevel)

function sourceHash() {
  SOURCE_FILES=$(cd $TOPDIR; git ls-files | grep -E "((^opam)|(\.(ml|ml4|peg)$))" | grep -E --invert-match "(setup|version)\.ml$")
  find $SOURCE_FILES -print0 | xargs -0 sha1sum | sort | sha1sum | cut -f 1 -d' '
}

if [[ $# -lt 1 ]]; then

  sourceHash

elif [[ "$1" == "check-if-updated" ]]; then

  REAL_HASH=$(sourceHash)
  STORED_HASH=$(grep --only-matching -E 'source_hash = "([^"]*)"' $TOPDIR/toploop/version.ml | cut -d'"' -f2)
  if [[ $REAL_HASH != $STORED_HASH ]]; then
    echo "Source hash needs to be updated."
    exit 1
  fi

elif [[ "$1" == "update" ]]; then

  NEW_HASH=$(sourceHash)
  sed -i -r -e "s/source_hash = \"[^\"]*\"/source_hash = \"$NEW_HASH\"/" $TOPDIR/toploop/version.ml

else

  echo "Usage: $0 [check-if-updated|update]"
  exit 1

fi

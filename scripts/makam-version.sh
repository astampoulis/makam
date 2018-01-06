#!/usr/bin/env bash

set -eu
set -o pipefail

TOPDIR=$(git rev-parse --show-toplevel)

function usage() {
  cat <<EOF
Usage: $0 [update <version> | check-if-updated | npm-test-version]

$(basename $0)                     prints current Makam version
$(basename $0) npm-test-version    prints version for test npm package
$(basename $0) update <version>    updates to given version
$(basename $0) check-if-updated    checks whether a version update is needed

EOF
}

function get_version() {
  grep --only-matching -E "version = \"[^\"]+\"" | cut -d'"' -f 2
}

function code_changes_from_parent() {
  git diff-tree -r --name-status $1..HEAD termlang toploop stdlib opam npm/src npm/package.json npm/yarn.lock | grep --invert-match "toploop/version.ml"
}

BASEVERSION=$(cat $TOPDIR/toploop/version.ml | get_version)

if [[ $# -lt 1 ]]; then
  COMMAND=version
else
  COMMAND=$1
fi

case $COMMAND in

--help|help)
  usage
  exit 0
  ;;

version)

  echo $BASEVERSION
  ;;

npm-test-version)

  echo $BASEVERSION-test-$(git rev-parse --short HEAD)
  ;;

update)

  if [[ $# -lt 2 ]]; then
    usage
    exit 1
  fi

  NEWVERSION=$2

  sed -i -r -e "s/version = \"[^\"]+\"/version = \"$NEWVERSION\"/" $TOPDIR/toploop/version.ml
  sed -i -r -e "s/^Version:     .*$/Version:     $NEWVERSION/" $TOPDIR/_oasis
  sed -i -r -e "s/^version: \"[^\"]+\"/version: \"$NEWVERSION\"/" $TOPDIR/opam/opam
  sed -i -r -e "s/\"version\": \"[^\"]+\"/\"version\": \"$NEWVERSION\"/" $TOPDIR/npm/package.json
  sed -i -r -e "s/version = \"[^\"]+\"/version = \"$NEWVERSION\"/" $TOPDIR/js/index.html

  # Do the source hash update afterwards to make sure that the above gets incorporated
  $TOPDIR/scripts/source-hash.sh update

  ;;

check-if-updated)

  # If the source changes, we definitely need a version update -- and the source hash needs to be updated too.
  $TOPDIR/scripts/source-hash.sh check-if-updated

  # Otherwise, check to see if we have any changes that would necessitate a version update

  # First, get the commit where we last branched off of master.
  if [[ $(git rev-parse --abbrev-ref HEAD) == master ]]; then
    PARENT=master^
  else
    PARENT=master
  fi

  # CircleCI behaves weird (sets master to be the current branch?) so we're using
  # origin/master below.
  PARENTCOMMIT=$(git rev-list --boundary HEAD...origin/$PARENT | grep "^-" | cut -c2- | head -n 1)
  PARENTVERSION=$(git show $PARENTCOMMIT:toploop/version.ml | get_version)

  if [[ ! -z $(code_changes_from_parent $PARENTCOMMIT) && $PARENTVERSION == $BASEVERSION ]]; then
    cat <<EOF
Summary of changes:

$(code_changes_from_parent $PARENTCOMMIT)

The current version is: $PARENTVERSION
A version update is needed; please use \`$0 update <version>\`.

EOF
    exit 1
  fi

  ;;

esac

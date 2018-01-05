#!/usr/bin/env bash

set -e
set -o pipefail

BASEVERSION=$(node -p "require('./npm/package.json').version")
VERSION=$BASEVERSION-test-$(git rev-parse --short HEAD)

echo $VERSION

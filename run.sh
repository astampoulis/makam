#!/bin/bash

echo just.md | entr -cr bash -c "./makam just.md && pandoc -s --mathjax just.md -o just.html"

#!/usr/bin/env bash

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

lake exe lean-tactic-book --output _out --with-html-multi --without-html-single

if [[ -d LeanTacticBook/img ]]; then
  mkdir -p _out/html-multi/LeanTacticBook
  cp -R LeanTacticBook/img _out/html-multi/LeanTacticBook/
fi

test -f _out/html-multi/index.html
printf 'Built site at %s/_out/html-multi\n' "$repo_root"
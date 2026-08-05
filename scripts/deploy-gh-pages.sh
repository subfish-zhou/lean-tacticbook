#!/usr/bin/env bash

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

deploy_dir=${1:-}
if [[ -z "$deploy_dir" ]]; then
  deploy_dir=$(git worktree list --porcelain | awk '
    $1 == "worktree" { path = $2 }
    $1 == "branch" && $2 == "refs/heads/gh-pages" { print path; exit }
  ')
fi

if [[ -z "$deploy_dir" ]]; then
  printf 'No gh-pages worktree found. Create one with:\n' >&2
  printf '  git worktree add ../lean-tacticbook-pages gh-pages\n' >&2
  exit 1
fi

deploy_dir=$(realpath "$deploy_dir")
deploy_branch=$(git -C "$deploy_dir" branch --show-current)
if [[ "$deploy_branch" != "gh-pages" ]]; then
  printf 'Refusing to deploy to %s (branch: %s).\n' "$deploy_dir" "$deploy_branch" >&2
  exit 1
fi

if [[ -n "$(git -C "$deploy_dir" status --porcelain)" ]]; then
  printf 'Refusing to overwrite dirty gh-pages worktree: %s\n' "$deploy_dir" >&2
  exit 1
fi

command -v rsync >/dev/null || {
  printf 'rsync is required to deploy the generated site.\n' >&2
  exit 1
}

lake build
lake exe lean-auto-book --output _out --with-html-multi --without-html-single
python3 scripts/wrap-code-boxes.py _out/html-multi

rsync -a --delete \
  --exclude=.git \
  --exclude=.nojekyll \
  --exclude=CNAME \
  _out/html-multi/ "$deploy_dir/"
touch "$deploy_dir/.nojekyll"

printf 'Prepared gh-pages worktree at %s\n' "$deploy_dir"
git -C "$deploy_dir" status --short
printf 'Review, commit, and push the changes from that worktree.\n'
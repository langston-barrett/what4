#!/usr/bin/env bash
set -euo pipefail

_event_name="${1:?expected event name}"
base_sha="${2:?expected base sha}"
head_sha="${3:?expected head sha}"

files=()

if [[ "$base_sha" =~ ^0+$ ]]; then
  while IFS= read -r file; do
    files+=("$file")
  done < <(git diff-tree --no-commit-id --name-only -r "$head_sha" -- 'what4-domains/doc/*.cry' | sort -u)
else
  while IFS= read -r file; do
    files+=("$file")
  done < <(git diff --name-only "$base_sha" "$head_sha" -- 'what4-domains/doc/*.cry' | sort -u)
fi

echo "Changed Cryptol specs:"
if ((${#files[@]} == 0)); then
  echo "(none)"
  echo "count=0" >> "$GITHUB_OUTPUT"
  exit 0
fi

printf '  %s\n' "${files[@]}"
echo "count=${#files[@]}" >> "$GITHUB_OUTPUT"
{
  echo "files<<EOF"
  printf '%s\n' "${files[@]}"
  echo "EOF"
} >> "$GITHUB_OUTPUT"

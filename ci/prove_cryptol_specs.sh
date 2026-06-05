#!/usr/bin/env bash
set -euo pipefail

cryptol --version

files=()
while IFS= read -r file; do
  files+=("$file")
done

tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

declare -a pids=()
declare -a logs=()

for i in "${!files[@]}"; do
  f="${files[$i]}"
  log="$tmpdir/$i.log"
  logs+=("$log")
  (
    echo "=== $f ==="
    cryptol --command=":prove" "$f"
  ) >"$log" 2>&1 &
  pids+=("$!")
done

fail=0
for pid in "${pids[@]}"; do
  if ! wait "$pid"; then
    fail=1
  fi
done

for log in "${logs[@]}"; do
  cat "$log"
done

exit "$fail"

#!/usr/bin/env bash
# Sequentially prove each chunk of cryptol property aliases with a 10s per-proof
# cap (proverTimeout). NEVER parallel. Emits a per-property summary.
set -u
CRY="/home/langston/crysolve/bin/cryptol"
SR="/nix/store/c1rgfy5kcyabkaza8hvfxffb8z982qd6-steam-run-1.0.0.85/bin/steam-run"
SUM=/tmp/proof_summary.txt
: > "$SUM"
for c in /tmp/chunk_*; do
  idx=$(basename "$c")
  icry=./run_${idx}.icry
  { echo ':l doc/smoothclp.cry'; echo ':set proverTimeout=10';
    while read -r n; do echo ":prove $n"; done < "$c"; echo ':quit'; } > "$icry"
  out=/tmp/out_${idx}.txt
  timeout 320s "$SR" bash -c "PATH=/home/langston/crysolve/bin:\$PATH LD_LIBRARY_PATH=/usr/lib64:/usr/lib $CRY -b $icry" > "$out" 2>&1
  # outcomes in order
  grep -E "Q\.E\.D\.|Counterexample|Unknown" "$out" \
    | sed -E 's/.*Q\.E\.D\..*/PASS/; s/.*Counterexample.*/FAIL-CEX/; s/.*Unknown.*/TIMEOUT/' > /tmp/o_${idx}.txt
  paste -d' ' "$c" /tmp/o_${idx}.txt >> "$SUM"
done
echo "=== SUMMARY ==="
echo "total lines: $(wc -l < "$SUM")"
echo "PASS:    $(grep -c ' PASS$' "$SUM")"
echo "TIMEOUT: $(grep -c ' TIMEOUT$' "$SUM")"
echo "FAIL:    $(grep -c ' FAIL-CEX$' "$SUM")"
echo "=== non-PASS ==="
grep -vE ' PASS$' "$SUM"

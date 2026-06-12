#!/usr/bin/env python3
"""
Compare two precision CSVs (strides.csv vs sasi.csv produced by
``strides-precision`` and ``sasi-precision``).

Each CSV has columns ``op,abs,conc,precision``:

* ``abs`` is the sum of abstract-output cardinalities over all input pairs
  (or unary inputs).
* ``conc`` is the same sum but for the concrete oracle.
* ``precision = conc / abs`` as a percentage (smaller ``abs`` is better).

Usage:
    compare_csvs.py STRIDES.csv SASI.csv [--csv] [--check-conc-match]
"""
from __future__ import annotations

import argparse
import csv
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


@dataclass(frozen=True)
class Row:
    op: str
    abs_: int
    conc: int

    @property
    def precision_pct(self) -> float:
        return 100.0 * self.conc / self.abs_ if self.abs_ else 0.0


def load(path: Path) -> dict[str, Row]:
    out: dict[str, Row] = {}
    with path.open() as f:
        reader = csv.DictReader(f)
        for raw in reader:
            op = raw["op"]
            out[op] = Row(op=op, abs_=int(raw["abs"]), conc=int(raw["conc"]))
    return out


def compare(strides: dict[str, Row], sasi: dict[str, Row]) -> list[dict[str, str]]:
    """Build one row per op, ordered by strides' op order, then sasi-only ops."""
    rows: list[dict[str, str]] = []
    seen: set[str] = set()
    for op in list(strides) + [o for o in sasi if o not in strides]:
        if op in seen:
            continue
        seen.add(op)
        s = strides.get(op)
        x = sasi.get(op)
        if s and x:
            winner = "tie" if s.abs_ == x.abs_ else ("strides" if s.abs_ < x.abs_ else "sasi")
            row = {
                "op": op,
                "strides_abs": str(s.abs_),
                "sasi_abs": str(x.abs_),
                "strides_pct": f"{s.precision_pct:.1f}%",
                "sasi_pct": f"{x.precision_pct:.1f}%",
                "delta_abs": str(s.abs_ - x.abs_),
                "winner": winner,
            }
        elif s:
            row = {
                "op": op, "strides_abs": str(s.abs_), "sasi_abs": "-",
                "strides_pct": f"{s.precision_pct:.1f}%", "sasi_pct": "-",
                "delta_abs": "-", "winner": "strides_only",
            }
        else:
            assert x is not None
            row = {
                "op": op, "strides_abs": "-", "sasi_abs": str(x.abs_),
                "strides_pct": "-", "sasi_pct": f"{x.precision_pct:.1f}%",
                "delta_abs": "-", "winner": "sasi_only",
            }
        rows.append(row)
    return rows


def write_csv(rows: list[dict[str, str]], out: object) -> None:
    fields = ["op", "strides_abs", "sasi_abs", "strides_pct", "sasi_pct",
              "delta_abs", "winner"]
    writer = csv.DictWriter(out, fieldnames=fields)  # type: ignore[arg-type]
    writer.writeheader()
    writer.writerows(rows)


def write_table(rows: Iterable[dict[str, str]], out: object) -> None:
    rs = list(rows)
    cols = ["op", "strides_abs", "sasi_abs", "strides_pct", "sasi_pct",
            "delta_abs", "winner"]
    widths = {c: max(len(c), max((len(r[c]) for r in rs), default=0)) for c in cols}
    sep = "  "
    print(sep.join(c.ljust(widths[c]) for c in cols), file=out)  # type: ignore[arg-type]
    print(sep.join("-" * widths[c] for c in cols), file=out)  # type: ignore[arg-type]
    for r in rs:
        print(sep.join(r[c].ljust(widths[c]) for c in cols), file=out)  # type: ignore[arg-type]


# For these ops the conc column counts something other than the concrete
# oracle's output cardinality, so a mismatch isn't an oracle bug:
#   leq: counts pairs where the syntactic check returns True (= recall);
#        the two domains' checks have different recall by construction.
_NON_ORACLE_CONC_OPS = {"leq", "leqPrecise", "leqExact"}


def check_conc_match(strides: dict[str, Row], sasi: dict[str, Row]) -> int:
    """Return 0 if all shared oracle ops have matching conc, else nonzero."""
    bad = 0
    for op in sorted(set(strides) & set(sasi)):
        if op in _NON_ORACLE_CONC_OPS:
            continue
        s = strides[op]
        x = sasi[op]
        if s.conc != x.conc:
            print(
                f"conc mismatch on {op}: strides={s.conc} sasi={x.conc}",
                file=sys.stderr,
            )
            bad += 1
    if bad:
        print(f"{bad} op(s) disagree on conc — oracle bug", file=sys.stderr)
    return 1 if bad else 0


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("strides_csv", type=Path)
    p.add_argument("sasi_csv", type=Path)
    p.add_argument("--csv", action="store_true",
                   help="emit machine-readable CSV instead of a pretty table")
    p.add_argument("--check-conc-match", action="store_true",
                   help="exit nonzero if any shared op has differing conc")
    args = p.parse_args(argv)

    strides = load(args.strides_csv)
    sasi = load(args.sasi_csv)

    if args.check_conc_match:
        return check_conc_match(strides, sasi)

    rows = compare(strides, sasi)
    if args.csv:
        write_csv(rows, sys.stdout)
    else:
        write_table(rows, sys.stdout)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

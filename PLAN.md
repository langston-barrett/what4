# Implement Smooth CLPs (SmoothClp ⋈ Bitwise)

## Context

The `What4.Domains.BV.Strides` domain represents bitvector sets as progressions
`(start, stride, n)`. Its hot-path lattice/arithmetic operations (`add`, `sub`,
`pseudoJoin`, `mul`) compute an integer **gcd** of operand strides to fix the
result stride. gcd is `G(w)`-class — the most expensive primitive in the cost
model — and dominates at every tier, making the domain markedly slower than
known-bits/tnum analyses (a handful of word-bitwise ops).

**Smooth CLPs** fix this by constraining the stride to a fixed *smooth* basis:
`stride = 2^k · m` where `m` is a **squarefree** product of odd primes drawn from
a small fixed basis `B` (e.g. `{3,5,7,11,13}`). Then:

- the **2-part** `2^k` is already free (`lowestSetBit`, as in Strides);
- the **odd part** is a `|B|`-bit **presence bitmask**, so `gcd`/`lcm` of two
  strides degrade to `2^min/max(k) · (mask_a .&./.|. mask_b)` — AND/OR/`blsi`,
  no Euclid, no division;
- factoring an arbitrary integer into this form (only at *ingestion* and inside
  `mul`) is one `gcd`-against-`R = ∏B` plus a table lookup.

This is the tnum strategy generalized with a few odd "channels": the congruence
lattice becomes bit-operations. Outcome: a strides-family domain competitive with
known-bits on the common operations, paired with the bitwise domain in a reduced
product so it also carries arbitrary forced-bit facts the stride representation
structurally cannot.

Scope: a **standalone** `SmoothClp` core domain (full operation set, own
Cryptol model, own test file) plus the `SmoothClpBitwise` reduced product —
mirroring the existing `Strides` / `StridesBitwise` split exactly. The standalone
core is independently meaningful (a smooth-modulus congruence ⋈ wrapped-interval
domain) and is what the product delegates to.

## Decisions (settled with user)

- **Standalone core + product**, both exposed (mirror `Strides`/`StridesBitwise`).
- **Explicit representation** `(start, stridePow2, oddFactorsMask, steps)` — the
  squarefree rep where the congruence lattice *is* bit-ops — **plus a cached
  integer `stride`** (see Representation below; the design analysis showed
  reconstruct-on-demand pessimizes the ~20 sites that need the integer and helps
  only the ~5 lattice sites).
- **No orientation-robustness by default.** It is a ~4× constant-factor cost for a
  marginal precision gain, which fights the KnownBits-speed thesis. Default and
  `*Fast` add/sub/mul run a single-orientation kernel. Orientation-robustness is
  demoted to the `*Precise` tier only (opt-in), mirroring the existing
  Fast/default/Precise split.
- **Full parallel Cryptol mirror**: a complete `doc/smoothclp.cry` wired into
  `TestCoverage`'s bidirectional Cryptol↔Haskell correspondence, matching how
  `Strides` is treated.
- Same module/section/property **organization** as `Strides`; the
  `TestCoverage`-enforced export-order and invocation discipline is the spec for
  "same organization."

## Representation

```haskell
data Domain (w :: Nat) = Domain
  { start          :: !Natural   -- first element
  , stride         :: !Natural   -- CACHED integer stride = 2^stridePow2 · oddProduct(oddFactorsMask)
  , stridePow2     :: !Word      -- 2-exponent: strideGcd = 2^stridePow2  (== lowestSetBit stride)
  , oddFactorsMask :: !Word      -- presence bitmask over basis B (squarefree odd part)
  , steps          :: !Natural   -- step count
  , mask           :: !Natural   -- 2^w - 1
  }
```

- `stride` is redundant but cached: every arc/membership/Diophantine site reads it
  as an integer exactly as Strides does (zero porting risk, zero overhead).
- `stridePow2`/`oddFactorsMask` are read by the lattice ops only;
  `strideGcd = 2^stridePow2` becomes a field read.
- **Invariant** (extends `proper`): `stride == 2^stridePow2 · oddProduct(oddFactorsMask)`,
  `oddFactorsMask` within basis range, `stride` smooth.
- Basis tables (module constants): `oddProduct :: Word -> Natural` (2^|B| entries),
  and `R = ∏B` with `smoothPartOf :: Natural -> (Word, Natural)` computing the
  squarefree-basis part of an odd integer via `gcd(·, R)` (NOT mere `urem` — must
  strip to squarefree; see Critical detail #4 below).

## Critical design resolutions (from design analysis)

1. **`mk` is the single smoothing point.** Given requested `(s, st, nn)`: split
   `st = 2^k · m_odd`, round `m_odd` *down* to its largest squarefree-basis
   divisor `m_s` (`smoothPartOf`), set `st_s = 2^k · m_s` and rescale
   `steps_s = steps · (st `div` st_s)`, then run the existing `mk` body (which
   `clampToOrbit`s and canonicalizes full cosets/singletons). Sound: smaller
   stride ⇒ denser coset ⇒ superset. **`stridePow2` is preserved** (only odd
   factors drop), so `strideGcd`, `orbitLen`, `forcedBits` low-pinning, `clampToOrbit`
   are all unchanged — exactly the invariants downstream needs. This rescale
   mirrors the existing `n' = na·(sa/d)+nb·(sb/d)` pattern in
   `addSubStrideAndSteps`.

2. **Orientation / `reverseD` — `*Precise`-only, not default.**
   Orientation-robustness (try operand and its `reverseD`, keep the smaller
   result) is a ~4× constant-factor cost for marginal precision; it does not
   belong on the hot path. Default and `*Fast` add/sub/mul run a **single
   orientation** (no `reverseD`, no `orientRobust` wrapper) — the cheapest
   meaningful kernel. The `*Precise` variants opt back into orientation-robustness.
   Where orientation *is* used (`*Precise`), `2^w − t` is generally NOT smooth, so
   run it on the **integer stride** (the cached field) exactly as Strides does —
   the reversed orientation is a transient integer-stride object, never a stored
   smooth `Domain`; smooth only at the final `mk`. So: `add`/`addFast` =
   single-orientation integer kernel + smooth `mk`; `addPrecise` = orient-robust
   integer kernel + smooth `mk`. Same for `sub`, `mul`.

3. **`mul` is the largest divergence and the precision cost.**
   `cornerProductStride`/`clpStepBound` gcd over `t1·l2, t2·l1, t1·t2` where
   `l` are arbitrary corner values — `t·l` is NOT smooth, so this stays a genuine
   integer gcd (the AND-of-masks thesis does not apply). The explicit rep buys
   nothing in `mul`'s stride computation; the result `d` is then smoothed in `mk`
   (a `mul`-specific precision loss vs. Strides). Acceptable and documented.

4. **Ingestion factoring** (`fromAscEltList`, and `mk`): compute the
   squarefree-basis part via `gcd(m_odd, R)` then strip squares — `urem` alone
   only tests divisibility. Verify in a property (`smoothPartDividesAndSquarefree`).

5. **`canonicalize`/`Canonical`** operate on the integer `stride` exactly as
   Strides (the `min(t, 2^w−t)` orientation). The `Canonical` newtype is an opaque
   O(1) equality/hash key and need **not** satisfy the smoothness invariant — this
   sidesteps `2^w − t` non-smoothness. Reuse the Strides logic verbatim.

6. **`reduce`/`reducePrecise` are favorable.** The strides-side forced-bit lift
   only ever *raises `stridePow2`* (multiplies stride by `2^j`), which is a field
   bump in the explicit rep; `oddFactorsMask` is preserved. Arc clips `lcm` against
   a stride-1 arc (preserves the lifted smooth stride); the general `lcm` of two
   smooth strides is smooth (`2^max(k) · (mask_a .|. mask_b)`). No reduce path
   yields a non-smooth stride.

## Files to create

Naming: all modules, the `Domain` type, the Cryptol model, qualifiers, and test
files use **`SmoothClp`** (the domain is a *smooth circular linear progression*).

| File | Mirrors | Notes |
|------|---------|-------|
| `src/What4/Domains/BV/SmoothClp.hs` | `Strides.hs` | Core domain + all exported `correct_*` properties + all helpers (basis tables `oddProduct`/`R`/`smoothPartOf`, smooth-gcd/lcm, eGCD/Diophantine internals — kept in this one module, no separate Internal module). Same `-- *` section structure and export order. |
| `src/What4/Domains/BV/SmoothClpBitwise.hs` | `StridesBitwise.hs` | Reduced product with `Bitwise`; lifts each op + `reduce`/`reducePrecise`; threads `tightUBounds` into `B.*Bounded`. |
| `doc/smoothclp.cry` | `doc/strides.cry` | Full parallel Cryptol mirror; smooth stride modeled as `(start, stridePow2, oddFactorsMask, steps)` with `oddProduct`/`smoothPartOf`; every op + `correct_*`/dominance property. |
| `test/SmoothClp.hs` | `test/Strides.hs` | `genTest` registration of every exported property; `genWidth*` generators. |
| `test/SmoothClpBitwise.hs` | `test/StridesBitwise.hs` | Same for the product. |
| `test/SmoothClp/Precision.hs` analogue (optional) | `test/Strides/Precision.hs` | If precision-regression tracking is wanted; can defer. |

## Files to modify

- **`what4-domains.cabal`**:
  - `exposed-modules`: add `SmoothClp`, `SmoothClpBitwise` (after the Strides
    block, lines ~175–177).
  - `other-modules` of `bvdomain_tests` AND `bvdomain_tests_hh`: add
    `SmoothClp`, `SmoothClpBitwise` (lines ~199–207, ~218–226).
- **`test/BVDomTests.hs`**: `import qualified SmoothClp` / `SmoothClpBitwise`;
  add `SmoothClp.tests`, `SmoothClpBitwise.tests` to the "Bitvector Domain"
  `testGroup` (~line 56, alongside `Strides.tests`).
- **`test/TestCoverage.hs`**:
  - Add `smoothClpMod = HsModule "src/.../SmoothClp.hs" "SC" "test/SmoothClp.hs"`
    and `smoothClpBitwiseMod = HsModule ".../SmoothClpBitwise.hs" "SCB" "test/SmoothClpBitwise.hs"` (~line 54–61).
  - `allHsModules`: add both. `cryptolBackedModules`: add `smoothClpMod` only
    (the product is excluded, like `stridesBitwiseMod`). `cryptolFiles`: add
    `doc/smoothclp.cry`.
  - Seed `cryptolOnly`/`haskellOnly` allowlists by analogy to the Strides entries
    (e.g. `toListMember` haskell-only; `correct_ule`/`correct_sle` cryptol-only).

## Build order (suggested)

1. **`SmoothClp.hs` helpers**: basis (`B`, `R`, `oddProduct`, `smoothPartOf`,
   smooth `gcd'`/`lcm'` on `(stridePow2, oddFactorsMask)`), plus the integer-level
   eGCD/Diophantine (ported from `Strides.Internal` into this module — no separate
   Internal module). Properties (exported from `SmoothClp`):
   `smoothPartDividesAndSquarefree`, `smoothGcdDividesTrueGcd`,
   `smoothGcdExactOnSmooth`.
2. **`SmoothClp.hs` skeleton**: record + `mk` (with smoothing #1) + `proper` +
   `strideGcd`/`orbitLen`/`canonicalize` (#5) + `member`/`toList`/`size` +
   `toArith`/`fromArith`/`toBitwise`/`forcedBits`/`fromBitwise`. Port from Strides;
   `strideGcd` reads `stridePow2`.
3. **Arithmetic**: `negate`, `scale`; `add`/`sub` + `addPrecise`/`subPrecise`
   (default = single-orientation integer kernel + smooth `mk`; `*Precise` =
   orient-robust, per #2); `mulFast`/`mul`/`mulPrecise` (#3; default/`Fast`
   single-orientation, `*Precise` orient-robust); division ops, SMT-LIB variants,
   LLVM-flag variants. Port kernels; redirect only the gcd sites to integer-level
   + `mk` smoothing. Note: where Strides has no orientation split today (it makes
   `add`/`sub`/`mul` orient-robust by default), SmoothClp **adds** a
   single-orientation default and reserves orient-robustness for `*Precise` —
   document this as an intentional cost/precision divergence from Strides.
4. **Bitwise** (`not`/`and`/`or`/`xor` + Fast/Precise), **ext/select/concat**,
   **shifts/rotations**.
5. **Lattice**: `pseudoMeet`/`Precise`, `exactMeet`, `lowerBound(s)`,
   `pseudoJoin`/`Precise`, `boundingBoxJoin`, `exactJoin`. The join stride uses
   smooth gcd; meet `lcm` uses smooth lcm (#6).
6. **Assumes** (unsigned/signed/Ne, + Precise).
7. **reduce/reducePrecise/reduceFixpoint** (#6) + `refineByBits*`.
8. **Generators** `genDomain`/`genElement`/`genPair` (generate a smooth stride
   directly: random `stridePow2` + random `oddFactorsMask`).
9. **`SmoothClpBitwise.hs`**: structural copy of `StridesBitwise.hs` with
   `S.` → `SC.` and the reduced-product properties.
10. **Cryptol** `doc/smoothclp.cry`: mirror, op-for-op and property-for-property.
11. **Wire** cabal + `BVDomTests` + `TestCoverage`; iterate until coverage passes.

## Verification

- `cabal test bvdomain_tests` and `cabal test bvdomain_tests_hh` — the QuickCheck
  and Hedgehog property suites must pass, including all new `SmoothClp*`
  properties (soundness `correct_*`, `*Shrinks`, `*Idempotent`, dominance laws).
- `cabal test bvdomain_coverage` — enforces (a) every exported property is invoked
  in the test file as `SC.`/`SCB.<name>`, (b) Cryptol↔Haskell name correspondence
  for `SmoothClp` (modulo allowlists), (c) export-order matches definition order.
  This is the machine-checked definition of "same organization."
- `cryptol doc/smoothclp.cry -c :prove` — prove the Cryptol soundness
  properties with Z3 (manual, matching `doc/README.md` for `bvdomain.cry`).
- **Key novel-claim properties** to assert (beyond ported soundness):
  - `smoothGcdDividesTrueGcd`, `smoothGcdExactOnSmooth` (the approximation is a
    sound common divisor, exact on smooth inputs).
  - `strideAlwaysSmooth` / `properImpliesSmooth` (the invariant holds after every op).
  - `mkSmoothingSound` (rounding the stride down over-approximates: `γ(old) ⊆ γ(mk-smoothed)`).
- Optional: a precision-regression entry comparing `SmoothClp` result
  cardinality vs. `Strides` on a corpus, to quantify the `mul`/ingestion precision
  cost (#3) — soundness tests won't catch tightness loss.

{-|
Module      : What4.Domains.BV.Strides
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Strides are an abstract domain for bitvectors. An element of the strides domain
is a tuple @(start, stride, n)@ representing the sequence of @n + 1@ bitvectors
visited by walking @n@ steps of size @stride@ from @start@ (mod @2^w@):

@
gamma((start, stride, n)) := { start + i * stride mod 2^w | 0 <= i <= n }
@

(Here, @gamma@ is the /concretization function/ in abstract interpretation.)

We call such a tuple a /progression/ in the sense of arithmetic progressions.

== Intuition

There are two "lossy" but helpful ways to conceptualize strided intervals.

=== Geometry

It can be helpful to conceptualize these progressions as strided intervals that
proceed clockwise around a \"number circle\". This circle starts at 0 at the
south pole, proceeds around to the signed maximum at the north pole (and then
immediately to the signed minimum), and ends at the unsigned maximum just before
0.

@
smax = 011..1 --vv-- 100..0 = smin
                --
              /    \\
              \\    /
                --
umin = 000..0 --^^-- 111..1 = umax
@

Unlike the classic interval domain over unbounded mathematical integers,
progressions can wrap around 0 from "high" values to "low" values (when
interpreted as unsigned bitvectors, i.e., with the lexicographical ordering on
their bits).

==== Self-wrapping

However, /and crucially/, this "geometric" intuition is limited. Unlike the
wrapped intervals domain (discussed further below), progressions can wrap around
/their own starting point/ without visiting the same value twice, even multiple
times. A progression with @gcd(stride, 2^w) = 1@ progression can visit every
element of @[0, 2^w - 1]@ before repeating. We call progressions that wrap in
this way /self-wrapping/.

=== Algebra

A progression @(start, stride, n)@ is a (not-necessarily-closed subset of a)
/coset/ @start + stride(ℤ/(2^w)ℤ)@ of the additive group ℤ/(2^w)ℤ.

== Visualization and examples

The diagrams below show the represented set as one cell per bitvector value
across @[0, 2^w)@; @*@ marks a member, @.@ a non-member. The outer brackets are
the modulus boundary - values fall off the right end and reappear on the left.

At @w = 4@:

@
[****************]   @⊤@ (the full set)
[..*****.........]   start=2,  stride=1, n=4: {2,3,4,5,6}
[..*.*.*.*.......]   start=2,  stride=2, n=3: {2,4,6,8}
[*...*...*...*...]   start=0,  stride=4, n=3: {0,4,8,12}
[**............**]   start=14, stride=1, n=3: {14,15,0,1}  (wraps around 0)
[*...........*.*.]   start=12, stride=2, n=2: {12,14,0}    (wraps around 0)
[*....*.*......*.]   start=0,  stride=7, n=3: {0,7,14,5}   (self-wrapping)
@

You can generate diagrams like the above with the following Python function:

@
def diagram(w, start, stride, n):
    members = {(start + i * stride) % (2 ** w) for i in range(n + 1)}
    cells = ''.join('*' if v in members else '.' for v in range(2 ** w))
    return f'[{cells}]'
@

which you can load into a REPL with

@
python3 -ic "$(awk '\/^def diagram\/,\/^    return/' src\/What4\/Domains\/BV\/Strides.hs)"
@

A Haskell equivalent is the exported 'diagram' function; see its doctests on
'mk' for examples.

== Complexity

This domain uses unbounded integers internally, and supports analysis of
variables of any bit-width @w@. Every exported operation is documented with its
complexity in big-O notation in terms of @w@. In particular, this means that
operations like bitwise-and on 'Natural' are considered @O(w)@.

== Comparison to other domains

The strides domain is similar to, but ultimately distinct from, a variety
of domains in the literature. The following are presented in ascending
chronological order of definition, but in roughly descending order of similarity
to the strides domain.

=== /Strided intervals/ (2006)

The strided interval (/SI/) domain of /Intermediate-Representation Recovery
from Low-Level Code/ is the reduced product of a finite-interval @[-2^(w-1),
2^(w-1)]@ domain with a congruence domain. However, the SASI paper (see below)
states that "strided-intervals require the signedness of the variable and do not
take care of the value overflows and underflows." The strides domain takes great
pains to soundly handle over- and under-flows.

=== /Circular linear progressions/ (2007)

The strides domain is perhaps most similar to /circular linear progressions/
(CLPs), from /Executable Analysis using Abstract Interpretation with Circular
Linear Progressions/. A CLP is a tuple @(start, end, stride)@ representing the
set

@
gamma((start, end, stride)) :=
  { start + i * stride, start + 2 * i * stride, ..., end }
@

The immediate difference between CLPs and the strides domain is the
representation. We can easily recover @end@ from @(start, stride, n)@ in @O(w)@
via the identity @end = start + n * stride mod 2^w@, and check for self-wrap in
@O(w)@ via @n * stride >= 2^w@.

The procedure for deriving @n@ from @end@ is more complex. Let @g = gcd(2^w,
stride)@. Note that:

* @g@ is a power of 2,
* @stride / g@ is odd, and
* @stride / g@ and @2^w / g@ are coprime (by the definition of @gcd@).

Then @stride / g@ has a multiplicative inverse @s^(-1)@ mod @2^w / g@ that
can be computed via Hensel lifting (Newton iteration).  Subtracting @start@,
dividing by @g@, and multiplying by @s^(-1)@ on both sides yields @n@ as
desired:

@
((end - start) / g) * s^(-1) = n
@

Not only was this direction more complex, but also requires @O(w log w)@
time. This is an important point of motivation for moving from CLP's @(start,
end, stride)@ to our @(start, stride, n)@. In fact, several operations on
CLPs compute with @n@ internally, only to recover @end@ post-hoc (e.g.,
intersection).

An implementation of CLPs is available at
<https://github.com/statinf-otawa/otawa-clp>.

=== /Wrapped intervals/ (2012)

In /Signedness-Agnostic Program Analysis: Precise Integer Bounds for Low-Level
Code/, the authors state that "Setting the stride in [CLPs] to 1 results in
precisely the concept of wrapped intervals that we use in this paper." Thus,
their /wrapped intervals/ (WIs) correspond closely to our stride-1 progressions.

Their wrapped intervals are pairs @(lo, hi)@ representing the set

@
gamma((lo, hi)) := { lo, lo + 1, ..., hi }
@

@lo@ does not need to be "less than" @hi@ in the sense of signed nor unsigned
bitvectors.

A self-wrapping stride-1 interval simply /saturates/ the space @[0, 2^w - 1]@.
Thus, the transfer functions (abstract operations) on WIs do not consider this
case. This is important, as they form the basis for the following domain.

=== /Signedness-agnostic strided intervals/ (2019)

/Signedness-agnostic strided intervals/ (SASIs) (from the paper /BinTrimmer:
Towards Static Binary Debloating Through Abstract Interpretation/) are
based very closely on wrapped intervals, but they add stride information.
Fascinatingly, the /BinTrimmer/ paper does not cite the CLP paper, despite the
quote about CLPs in the wrapped intervals paper.

Like CLPs, SASIs are tuples @(lb, ub, s)@ representing the set

@
gamma((lb, ub, s)) := { lb, lb + s, lb + 2 * s ..., ub }
@

However, the membership check given in the paper is unsound with respect
to their @gamma@. It /is/ sound if we further assume that the SASIs don't
self-wrap. It's hard to say if the other operations on SASIs are sound with
respect to this non-self-wrapping interpretation, as the paper only specifies
@or@.

This unsoundness makes sense when we consider that SASIs are closely based on
WIs: self-wrapping does not matter for WIs (it saturates). The SASI operations
were not adequately adjusted for the new domain. The strides domain is what
results from adequately adjusting them.

Happily, this adjustment also improves precision. The implementation of addition
on SASIs at <https://github.com/ucsb-seclab/sasi> appears to saturate to ⊤
when addition of the endpoints could overflow. However, this is not necessary
for strided intervals. Let @s@ be the SASI @(0, 2^n-2, 2)@. For @w=4@, we
can represent this visually as @[*.*.*.*.*.*.*.*.]@. Then pointwise addition
@gamma(s) + gamma(s) = { a + b | a in gamma(s), b in gamma(s) }@ yields exactly
@gamma(s) = {0, 2, ..., 2^(w-1)}@. That is to say, the most precise result would
be @s + s = s@. This is what our 'add' yields on the equivalent progressions,
whereas SASI would yield ⊤.

=== Additional related work

For more discussion of related work, see /Interval Analysis and Machine
Arithmetic: Why Signedness Ignorance Is Bliss/.

== Testing strategy

=== Soundness

To be correct (i.e., sound), our abstract operations (e.g., 'add')  must
over-approximate the corresponding concrete operations (addition mod @2^w@).
The specific claim is the following: Given two bitvectors @x@ and @y@ that
are members of progressions @a@ and @b@ respectively, then for each concrete
operation @op@ (e.g., addition mod @2^w@) and the corresponding abstract
operation @absOp@, @x `op` y@ is a 'member' of @a `absOp` b@. By the correctness
specification of 'member', this is equivalent to the statement (equivalently, @x
`op` y@ is literally a member of the concretization @gamma(a `absOp` b)@ where
@gamma = 'toList'@).

The Cryptol specification at @doc\/strides.cry@ contains @correct_*@ predicates
for each operation; the Haskell @correct_*@ predicates here mirror that
specification. CI runs property-based tests for the Haskell predicates and
proves the Cryptol predicates at particular bit-widths.

=== Precision

==== Precision via comparison to wrapped intervals

As described above, wrapped intervals are like stride-1 progressions. We would
hope that adding the stride only improves the precision of our operations. In
particular, we might hope that the following shape of property holds:

@
member (a `op` b) x ==> A.member (toArith a `A.op` toArith b) x
@

This does not hold generally, and for an interesting reason: 'toArith' is too
precise. Naively, we might expect 'toArith' to yield ⊤ for any self-wrapping
progression. In actuality,  it yields the somewhat tighter interval @[start
% g, ..., start % g + (2^w - g)]@. Operations on this interval can result in
non-supersets of the corresponding operation on progressions.

We might instead hope that 

@
member (a `op` b) x ==> A.member (hull a `A.op` hull b) x
@

where @hull@ is just the interval @[start a, start a + 1, ..., end a]@, which
collapses to top for self-wrapping intervals. This /also/ does not hold in
general, because TODO.

TODO: Talk about subsets restricted to non-self-wrapping.

At this point, we might be a bit disappointed and simply settle for

@
size (a `op` b) x <= A.size (hull a `A.op` hull b)
@

Empirically, this property does hold for 'mul' on the exhaustive @w=4@
enumeration: across all 1.18M (a, b) pairs, @size (mul a b) <= A.size
(A.mul (hull a) (hull b))@, and 'mul' is strictly tighter than arith on
about 24% of pairs (where the strides domain preserves coset structure that
arith collapses).

We test the strongest of the above properties that apply to each operation.
Currently, the principled approach to a precise domain would take a reduced
product of the strides domain with the @Arith@ domain. This may be made
superfluous by more precise implementations of the transfer functions in the
future.

==== /Precision via enumeration/

Our "precision regression" tests work as follows. For each concrete operation
@op@ and corresponding abstract operation @absOp@, enumerate all progressions
at @w=4@. For each pair of progressions, compute the sum of the cardinalities of
the sets resulting from pointwise application of @op@ to each of their members.
Also compute the sum of cardinalities of the progressions resulting from
@absOp@. The resulting percentage @100 * concSum / absSum@ is a measure of the
precision of the abstract operation, with 100% meaning perfectly precise. This
is expensive to compute, but tractable at @w=4@.

This is an imperfect measure in that it is not necessarily possible for every
operation to achieve a score of 100%. That would require also computing the
progression that is the best possible approximation of the pointwise result. We
may do this in the future.

=== Exactness

The Haskell property tests and the Cryptol specification both include a small
set of /exactness/ properties drawn from /ASE: A Value Set Decision Procedure
for Symbolic Execution/.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.Strides
  ( Domain
  , start
  , stride
  , n
  , mask
  , end
  , proper
  , diagram
  , display
  -- * Construction
  , mk
  , top
  , fromAscEltList
  -- , singleton
  -- , fromRange
  -- , fromFoldable
  -- * Canonicalization
  , Canonical
  , getCanonical
  , canonicalize
  -- * Conversion
  , toArith
  , hull
  , fromArith
  , toBitwise
  , forcedBits
  , fromForcedBits
  , fromForcedBitsSigned
  , fromBitwise
  -- * Queries
  , member
  , toList
  , size
  -- , asSingleton
  , eq
  , leq
  , leqPrecise
  , leqExactPartial
  , leqExact
  , isSelfWrapping
  -- , ubounds
  -- , sbounds
  -- , ult
  -- , slt
  -- , overlap
  -- * Arithmetic
  , negate
  , add
  , sub
  , reverseD
  , scale
  , mul
  , udiv
  , urem
  , sdiv
  , srem
  -- ** Arithmetic (SMT-LIB div-by-zero semantics)
  , udivSmtlib
  , uremSmtlib
  , sdivSmtlib
  , sremSmtlib
  -- * Bitwise operations
  , not
  , andFast
  , and
  , andPrecise
  , orFast
  , or
  , orPrecise
  , xorFast
  , xor
  -- * Concatenation, extension, selection, and truncation
  , zext
  , sext
  , concat
  , select
  -- * Shifts and rotations
  , shl
  , shlRaw
  , lshr
  , lshrRaw
  , ashr
  , ashrRaw
  , rol
  , rolRaw
  , ror
  , rorRaw
  -- * Lattice operations
  -- $lattice
  -- ** Meets
  , pseudoMeet
  , pseudoMeetPrecise
  , exactMeet
  , lowerBound
  , lowerBounds
  -- ** Joins
  , pseudoJoin
  , pseudoJoinPrecise
  , boundingBoxJoin
  , exactJoin
  -- * Branch-condition assumptions
  , assumeUlt
  , assumeUle
  , assumeUgt
  , assumeUge
  , assumeSlt
  , assumeSle
  , assumeSgt
  , assumeSge
  -- * Reduced product with bitwise
  -- $reduced
  , refineByBits
  , refineByBitsPrecise
  , refineBitsByStrides
  , reduceStep
  , reduce
  , reduceFixpoint
  -- * Generators
  , genDomain
  , genElement
  , genPair
  -- * Properties
  -- ** Internal helpers
  , modNegCorrect
  , modSubCorrect
  , firstCosetMemberCorrect
  , wrapOffsetCorrect
  , strideGcdDividesStride
  , strideGcdIsPow2
  , orbitLenViaToList
  , divByPow2Correct
  , invModPow2Correct
  , floorSumCorrect
  , valueIndexCorrect
  , valueIndexMaybeCorrect
  , valueAtCorrect
  , circLeqAtZero
  , circLeqAnchorMin
  , circLeqAnchorMax
  , isSelfWrappingViaToList
  -- ** Construction
  -- , correct_singleton
  , fromAscEltListMember
  , fromAscEltListToListExactNonWrapping
  -- ** Canonicalization
  , canonLossless
  , canonProper
  , canonUnique
  , canonIdempotent
  , eqCorrect
  , canonForwardOriented
  , canonMatchesSearch
  , canonHashRespectsEq
  -- ** Conversion
  , toArithCorrect
  , startEndArcCorrect
  , cosetArcCorrect
  , fromArithCorrect
  , roundtripArith
  , toBitwiseCorrect
  , strideBitwiseCorrect
  , forcedBitsDisjoint
  , forcedBitsMember
  , fromForcedBitsCorrect
  , fromForcedBitsSignedCorrect
  , fromBitwiseCorrect
  -- ** Queries
  -- , correct_asSingleton
  , startMember
  , endMember
  , toListMember
  , memberToList
  , toListNoDuplicates
  , leqCorrect
  , leqReflexive
  , leqTransitive
  , leqRefinesLeqExact
  , leqPreciseCorrect
  , leqPreciseReflexive
  , leqPreciseRefinesLeqExact
  , leqExactCorrect
  , leqExactComplete
  , leqExactReflexive
  , leqExactTransitive
  , leqExactPartialAgrees
  , leqExactWindowAgrees
  , sizeViaToList
  , cosetsDisjointCorrect
  , eqExactCorrect
  , eqExactReflexive
  , eqExactSymmetric
  , eqExactTransitive
  -- , correct_ubounds
  -- , correct_sbounds
  -- , correct_ult
  -- , correct_slt
  -- , correct_overlap
  -- ** Arithmetic
  , correct_neg
  , correct_add
  , correct_sub
  , reverseDSameSet
  , psplitProper
  , psplitCovers
  , psplitPartitions
  , psplitOp2Sound
  , correct_scale
  , correct_mul
  , addSubSizeCorrect
  , addRobustClosedFormAgrees
  , addRobustDominatesRaw
  , subRobustDominatesRaw
  , mulRobustDominatesRaw
  , correct_mulCorners
  , correct_mulNoStraddleU
  , correct_mulNoStraddleS
  , correct_scaleSingleton
  , zboundsArcSameModular
  , zboundsArcMinMidpoint
  , cornerArcEncloses
  , cornerProductStrideDivides
  , clpStepBoundSound
  , arcStepBoundSound
  , correct_udiv
  , correct_urem
  , correct_sdiv
  , correct_srem
  -- *** Exactness
  , addExact
  , subExact
  , mulConstExact
  , udivConstExact
  , uremConstExact
  , ultExactTrueSeparated
  , ultExactFalseSeparated
  -- *** Arithmetic (SMT-LIB div-by-zero semantics)
  , correct_udivSmtlib
  , correct_uremSmtlib
  , correct_sdivSmtlib
  , correct_sremSmtlib
  -- ** Bitwise operations
  , correct_not
  , correct_and
  , correct_or
  , correct_xor
  , correct_andPrecise
  , correct_orPrecise
  , correct_andSingleton
  , warrenAndLoCorrect
  , warrenAndHiCorrect
  , operandRangeCorrect
  , andPreciseDominatesAndFast
  -- ** Concatenation, extension, selection, and truncation
  , correct_zero_ext
  , correct_sign_ext
  , correct_concat
  , correct_select
  -- ** Shifts and rotations
  , correct_shl
  , correct_lshr
  , correct_ashr
  , correct_rol
  , correct_ror
  -- ** Lattice operations
  -- *** Splitting helpers
  , nsplitUnion
  , nsplitDisjoint
  , ssplitUnion
  , ssplitDisjoint
  -- *** Meets
  , correct_pseudoMeet
  , correct_pseudoMeetPrecise
  , pseudoMeetLowerBound
  , pseudoMeetPreciseLowerBound
  , pseudoMeetCommutative
  , pseudoMeetPreciseCommutative
  , pseudoMeetIdempotent
  , pseudoMeetPreciseIdempotent
  , pseudoMeetTopIdentity
  , pseudoMeetPreciseTopIdentity
  , correct_exactMeet
  , exactMeetCommutative
  , exactMeetIdempotent
  , exactMeetLowerBound
  , exactMeetTopIdentity
  , exactMeetAssociative
  , correct_lowerBound
  , lowerBoundLeqExactBoth
  , lowerBoundCommutative
  , lowerBoundIdempotent
  , lowerBoundTopIdentity
  , lowerBoundIsLargestLowerBound
  , correct_lowerBounds
  , lowerBoundsAllSubsets
  , lowerBoundDominatedByPseudoMeet
  -- *** Joins
  , correct_pseudoJoin
  , correct_pseudoJoinPrecise
  , pseudoJoinUpperBound
  , pseudoJoinPreciseUpperBound
  , pseudoJoinCommutative
  , pseudoJoinPreciseCommutative
  , pseudoJoinIdempotent
  , pseudoJoinPreciseIdempotent
  , pseudoJoinPreciseRefinesJoin
  , pseudoJoinTopAnnihilator
  , pseudoJoinPreciseTopAnnihilator
  , correct_boundingBoxJoin
  , boundingBoxJoinCommutative
  , boundingBoxJoinIdempotent
  , boundingBoxJoinTopAnnihilator
  , boundingBoxJoinUpperBound
  , boundingBoxJoinAssociative
  , boundingBoxJoinMonotone
  , pseudoJoinDominatesBoundingBoxJoin
  , correct_exactJoin
  , exactJoinCommutative
  , exactJoinIdempotent
  , exactJoinUpperBound
  , exactJoinTopAnnihilator
  , exactJoinAssociative
  -- *** Compactification
  , correct_compactify
  -- ** Branch-condition assumptions
  , correct_assumeUlt
  , correct_assumeUle
  , correct_assumeUgt
  , correct_assumeUge
  , correct_assumeSlt
  , correct_assumeSle
  , correct_assumeSgt
  , correct_assumeSge
  , assumeUltShrinks
  , assumeUleShrinks
  , assumeUgtShrinks
  , assumeUgeShrinks
  , assumeSltShrinks
  , assumeSleShrinks
  , assumeSgtShrinks
  , assumeSgeShrinks
  , assumeUltIdempotent
  , assumeUleIdempotent
  , assumeUgtIdempotent
  , assumeUgeIdempotent
  , assumeSltIdempotent
  , assumeSleIdempotent
  , assumeSgtIdempotent
  , assumeSgeIdempotent
  -- ** Reduced product with bitwise
  , knownZerosOnesNatDisjoint
  , knownZerosOnesNatMember
  , liftForcedBitsShrinks
  , liftForcedBitsMember
  , arcClipBitwiseShrinks
  , arcClipBitwiseMember
  , correct_refineByBits
  , refineByBitsShrinks
  , correct_refineByBitsPrecise
  , refineByBitsPreciseShrinks
  , refineByBitsPreciseDominatesRoundTripNonSelfWrap
  , correct_refineBitsByStrides
  , refineBitsByStridesShrinks
  , refineBitsByStridesDominatesMeetToBitwise
  , correct_reduceStep
  , correct_reduce
  , reduceStepShrinks
  , reduceShrinks
  , reduceIdempotent
  , reduceConflictMeansEmpty
  , trimSelfWrapNotSelfWrapping
  , trimSelfWrapSubset
  , trimSelfWrapIdentity
  , trimSelfWrapIdempotent
    -- * Re-exports
    --
    -- | Re-exported so doctests (and downstream users) obtain @knownNat@\/@NatRepr@
    -- from the same @parameterized-utils@ build that 'mk' and friends were
    -- compiled against, avoiding spurious type mismatches when more than one
    -- build is visible in a GHCi session.
  , NatRepr
  , knownNat
  ) where

import           Control.Exception (assert)
import           Data.Bits ((.&.), popCount, shiftL, shiftR)
import           Data.Hashable (Hashable(..), hash)
import           Data.Maybe (fromMaybe)
import           GHC.TypeNats (Nat, type (+), type (<=))
import           Numeric.Natural (Natural)
import           Prelude hiding (negate, not, and, or, concat)
import qualified Prelude

import qualified Data.Bits as Bits
import qualified Data.List as List
import qualified Data.Set as Set

import           Data.Parameterized.NatRepr (NatRepr, LeqProof(..), knownNat, maxUnsigned)
import qualified Data.Parameterized.NatRepr as NR
import qualified What4.Domains.Arithmetic as Arith
import           What4.Domains.Arithmetic (countTrailingZerosOr0, isPow2Natural)
import qualified What4.Domains.BV.Arith as A
import qualified What4.Domains.BV.Bitwise as B
import qualified What4.Domains.BV.Strides.Internal as SI
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInteger)

-- $setup
-- >>> :set -XBinaryLiterals -XDataKinds -XTypeApplications
-- >>> import Prelude hiding (negate, not, and, or, concat)
-- >>> import Numeric.Natural (Natural)
-- >>> let w4 = knownNat @4
-- >>> let mk4 = mk (knownNat @4) :: Natural -> Natural -> Natural -> Domain 4

-- | A 'Domain' represents the set
--
-- @
-- { (start + stride * i) mod (mask + 1) | 0 <= i <= n }
-- @
--
-- where @mask = 2^w - 1@ for some @w@. The orbit thus has @n + 1@ elements.
--
-- The conceptual /end/ of the orbit, @(start + n * stride) mod 2^w@, is
-- exposed via the 'end' accessor.
data Domain (w :: Nat)
  = Domain
    { start :: !Natural
    , stride :: !Natural
    , n :: !Natural
    , mask :: !Natural
    }
  deriving (Eq, Ord, Show)

-- | /O(w)/. The conceptual @end@ of the orbit: @(start + n * stride) mod 2^w@.
end :: Domain w -> Natural
end c@Domain{start, stride, n, mask} =
  assert (proper c) $ (start + n * stride) .&. mask
{-# INLINE end #-}

-- | The data-structure invariants of 'Domain'.
proper :: Domain w -> Bool
proper Domain {start, stride, n, mask} =
  let g = lowestSetBit stride
      orbit = orbitLenOf mask g
  in Prelude.and
     [ start .&. mask == start
     , stride .&. mask == stride
     , stride > 0
     , n < orbit
     -- Singletons (@n = 0@) are canonicalized to stride 1.
     , n /= 0 || stride == 1
     -- Full cosets (@n + 1 = orbit@): smallest start in coset, stride = @g@.
     , n + 1 < orbit || (start < g && stride == g)
     ]

-- | /O(2^w \/ g)/. ASCII diagram of a progression in the style of the
-- module-level visualization examples: @[@ followed by one @*@ per member value
-- and one @.@ per non-member value, followed by @]@. Width is @mask + 1@ cells.
--
-- Useful in GHCi and in doctests to inspect progressions at a glance.
--
-- == Examples
--
-- Contiguous run:
--
-- >>> diagram (mk4 2 1 4)
-- "[..*****.........]"
--
-- Stride-2 (even numbers only):
--
-- >>> diagram (mk4 0 2 7)
-- "[*.*.*.*.*.*.*.*.]"
--
-- Wrap around 0:
--
-- >>> diagram (mk4 14 1 3)
-- "[**............**]"
diagram :: Domain w -> String
diagram d = '[' : [ if member d v then '*' else '.' | v <- [0..mask d] ] ++ "]"

-- | 'diagram' combined with 'toList': @diagram d ++ "  = " ++ show (toList d)@.
-- Convenient for showing both the visual layout and the explicit element list.
display :: Domain w -> String
display d = diagram d ++ "  = " ++ show (toList d)

-- ------------------------------------------------------------------
-- * Internal helpers

integerToNatural :: Integer -> Natural
integerToNatural = fromIntegral
{-# INLINE integerToNatural #-}

-- | /O(w)/. Reduce a 'Natural' modulo @2^w@, where @w@ is the width of the progression.
modMask :: Domain w -> Natural -> Natural
modMask c v = assert (proper c) $ v .&. mask c
{-# INLINE modMask #-}

-- | /O(w)/. Modular additive inverse modulo @mask + 1@.
modNeg :: Natural -> Natural -> Natural
modNeg mask x =
  assert ((mask + 1) .&. mask == 0) $
  assert (x .&. mask == x) $
  (mask + 1 - x) .&. mask
{-# INLINE modNeg #-}

-- | /O(w)/. Modular subtraction @x - y@ mod @mask + 1@.
modSub :: Natural -> Natural -> Natural -> Natural
modSub mask x y =
  assert ((mask + 1) .&. mask == 0) $
  assert (x .&. mask == x) $
  assert (y .&. mask == y) $
  (x + modNeg mask y) .&. mask
{-# INLINE modSub #-}

-- | /O(w)/. The wrap-around offset of @v@ from @start@: @(v - start) mod 2^w@.
wrapOffset :: Domain w -> Natural -> Natural
wrapOffset c@Domain{start, mask} v =
  assert (proper c) $ modSub mask v start
{-# INLINE wrapOffset #-}

-- | /O(w)/. The lowest set bit of @x@; equivalently @gcd(x, 2^w)@ for any
-- @w@ at least the bit-length of @x@.
lowestSetBit :: Natural -> Natural
lowestSetBit x = 1 `shiftL` countTrailingZerosOr0 (toInteger x)
{-# INLINE lowestSetBit #-}

-- | /O(w)/. @gcd(stride, 2^w)@. Since @2^w@ is a power of two, this equals the
-- lowest set bit of @stride@.
strideGcd :: Domain w -> Natural
strideGcd Domain{stride} = lowestSetBit stride
{-# INLINE strideGcd #-}

-- | /O(w)/. Sufficient (but not necessary) condition that @a@ and @b@ share
-- no values: @start a − start b@ is not a multiple of @min(strideGcd a,
-- strideGcd b)@, so the cosets @start a + ⟨stride a⟩@ and @start b + ⟨stride
-- b⟩@ in @Z\/2^w@ don't intersect at all (regardless of the orbit windows).
-- The converse fails when the cosets agree but the orbit windows are
-- disjoint, which this check doesn't see.
cosetsDisjoint :: Domain w -> Domain w -> Bool
cosetsDisjoint a b =
  modSub (mask a) (start a) (start b) .&. (min (strideGcd a) (strideGcd b) - 1)
    /= 0
{-# INLINE cosetsDisjoint #-}

-- | /O(w)/. @2^w \/ g@, where @mask = 2^w - 1@ and @g@ is a power-of-two
-- divisor of @2^w@ (e.g. @gcd(stride, 2^w)@). Used to compute the orbit
-- length of a progression from raw @mask@ and @g@ before a 'Domain' value exists.
orbitLenOf :: Natural -> Natural -> Natural
orbitLenOf mask g =
  assert (isPow2Natural (mask + 1)) $
  (mask + 1) `divByPow2` g
{-# INLINE orbitLenOf #-}

-- | /O(w)/. The orbit length: the number of distinct bitvectors visited by
-- the progression, which is @2^w \/ gcd(stride, 2^w)@. See
-- 'orbitLenViaToList'.
orbitLen :: Domain w -> Natural
orbitLen c@Domain{mask} = orbitLenOf mask (strideGcd c)
{-# INLINE orbitLen #-}

-- | /O(w)/. Cap @n@ at the orbit length minus 1: the maximum step count
-- representable for stride @stride@ at width @log2 (mask + 1)@.
clampToOrbit :: Natural -> Natural -> Natural -> Natural
clampToOrbit mask stride i =
  min i (orbitLenOf mask (lowestSetBit stride) - 1)
{-# INLINE clampToOrbit #-}

-- | /O(w)/. The smallest value @v@ in the wrapped arc starting at @lo@
-- (i.e. @v = (lo + off) mod 2^w@ for some @off ≥ 0@) with @v ≡ x (mod g)@,
-- where @g@ is a power-of-two divisor of @2^w = mask + 1@.
firstCosetMember ::
  Natural {- ^ @mask = 2^w - 1@ -} ->
  Natural {- ^ @lo@ -} ->
  Natural {- ^ @g@ -} ->
  Natural {- ^ @x@ -} ->
  Natural
-- The offset @off@ is @(x - lo) mod g@, taken on the @g@-cycle: since @g@
-- divides @2^w@, masking by @g - 1@ after a mod-@2^w@ subtraction yields
-- the mod-@g@ residue.
firstCosetMember mask lo g x =
  assert (isPow2Natural g && (mask + 1) `mod` g == 0) $
  (lo + (modSub mask x lo .&. (g - 1))) .&. mask
{-# INLINE firstCosetMember #-}

-- | /O(w)/. @x \/ p@ where @p@ is a power of two, computed as a right shift.
-- Asserts that @p@ is a (nonzero) power of two.
divByPow2 :: Natural -> Natural -> Natural
divByPow2 x p =
  assert (isPow2Natural p) $ x `shiftR` popCount (p - 1)
{-# INLINE divByPow2 #-}

-- | /O(w log w)/. Modular inverse of @a@ modulo @m@ where @m@ is a power of two
-- and @a@ is odd.
invModPow2 :: Natural -> Natural -> Natural
-- Computed via Hensel lifting (Newton iteration): @x' = x * (2 - a*x) mod m@.
-- Each step doubles the number of correct low bits, so the loop runs in @O(log
-- w)@ iterations of @O(w)@ work.
invModPow2 a m = assert (a .&. 1 == 1) $ go 1
  where
    mMinus1 = m - 1
    go x =
      let ax = (a * x) .&. mMinus1 in
      if ax == 1
        then x
        else go ((x * (2 + m - ax)) .&. mMinus1)

-- | /O(w^2)/. Euclidean-like floor sum,
-- @floorSum n m a b = sum_{i=0}^{n-1} ((a*i + b) \`Prelude.div\` m)@.
-- Requires @m > 0@; all values are non-negative.
floorSum :: Natural -> Natural -> Natural -> Natural -> Natural
floorSum n0 m0 a0 b0 = go 0 n0 m0 a0 b0
  where
    go !ans !n !m !a !b
      | n == 0 || m == 0 = ans
      | a >= m =
          go (ans + (n * (n - 1) `Prelude.div` 2) * (a `Prelude.div` m))
             n m (a `mod` m) b
      | b >= m =
          go (ans + n * (b `Prelude.div` m)) n m a (b `mod` m)
      | otherwise =
          let yMax = a * n + b
          in if yMax < m
               then ans
               else go ans (yMax `Prelude.div` m) a m (yMax `mod` m)

-- | /O(w log w)/. The progression index of @v@: the unique @i@ in @[0, 2^w \/
-- g)@ such that @start + i*stride ≡ v (mod 2^w)@, where @g = gcd(stride, 2^w)@.
-- Requires @g@ to divide @(v - start) mod 2^w@.
--
-- This costs O(w log w) for the modular inverse via 'invModPow2'; the step
-- count of the progression itself, @n c@, is available directly.
valueIndex :: Domain w -> Natural -> Natural
valueIndex c@Domain{stride, mask} v =
  assert (proper c) $
  assert (off .&. (g - 1) == 0) $
  ((off `divByPow2` g) * sInv) .&. (m' - 1)
  where
    -- @g@ is a power of two (see 'strideGcd'), so all divisions by it (and by
    -- @2^w@) are right shifts.
    off  = wrapOffset c v
    g    = strideGcd c
    m'   = (mask + 1) `divByPow2` g
    sInv = invModPow2 (stride `divByPow2` g) m'

-- | /O(w log w)/. Like 'valueIndex', but returns 'Nothing' when @v@ is not on
-- the coset of @c@ (so 'valueIndex'\'s precondition would be violated).
valueIndexMaybe :: Domain w -> Natural -> Maybe Natural
valueIndexMaybe c v
  | wrapOffset c v `mod` strideGcd c == 0 = Just (valueIndex c v)
  | otherwise                             = Nothing
{-# INLINE valueIndexMaybe #-}

-- | /O(w)/. The value at progression index @i@: @(start + i * stride) mod 2^w@.
-- Left inverse of 'valueIndex' on indices in @[0, 2^w \/ g)@.
valueAt :: Domain w -> Natural -> Natural
valueAt c@Domain{start, stride} i = assert (proper c) $
  modMask c (start + i * stride)
{-# INLINE valueAt #-}

-- | /O(w)/. SASI and WI's @≤_x@: @a ≤_x b@ iff @(a - x) mod 2^w <= (b - x) mod
-- 2^w@. Equivalently, traversing the circle of bitvectors starting at @x@, @a@
-- is reached no later than @b@.
circLeq :: Natural -> Natural -> Natural -> Natural -> Bool
circLeq m x a b = (a + nx) .&. m <= (b + nx) .&. m
  where nx = modNeg m x

-- ------------------------------------------------------------------
-- * Construction

-- | Construct a progression from @(start, stride, n)@: the orbit
-- @{ start, start + stride, ..., start + n·stride }@ (all mod @2^w@).
-- Asserts that
--
-- * @start@ and @stride@ fit in @w@ bits
-- * @stride > 0@
-- * @n@ is within the orbit length @2^w \/ gcd(stride, 2^w)@
-- * the resulting element is 'proper'
--
-- Saturates and canonicalizes:
--
--   * @n = 0@ (singleton): stride is forced to 1.
--   * @n + 1 = 2^w \/ g@ (full coset): @start@ is reduced to its residue
--     modulo @g@, stride is reduced to @g@.
--
-- == Examples
--
-- >>> diagram (mk4 2 2 3)
-- "[..*.*.*.*.......]"
-- >>> diagram (mk4 0 7 3)
-- "[*....*.*......*.]"
mk ::
  NatRepr w ->
  -- | @start@
  Natural ->
  -- | @stride@
  Natural ->
  -- | @n@: step count, @0 ≤ n < 2^w \/ gcd(stride, 2^w)@
  Natural ->
  Domain w
mk w s st nn =
  assert (s .&. m == s) $
  assert (st .&. m == st) $
  assert (st > 0) $
  assert (nn < orbit) $
  assert (proper c) c
  where
    m = integerToNatural (maxUnsigned w)
    g = lowestSetBit st
    orbit = orbitLenOf m g
    (s', st', n')
      -- Singleton: stride is irrelevant; pin to 1.
      | nn == 0          = (s, 1, 0)
      -- Full coset: any element of @start mod g + g·Z@ is a valid start.
      -- Pick @start = start mod g@, @stride = g@.
      | nn + 1 == orbit  = (s .&. (g - 1), g, orbit - 1)
      | otherwise        = (s, st, nn)
    c = Domain { start = s', stride = st', n = n', mask = m }
{-# INLINE mk #-}

-- | /O(w)/. The top element of the lattice: the progression containing every
-- @w@-bit value, @(0, 1, 2^w - 1)@.
top :: NatRepr w -> Domain w
top w = mk w 0 1 (integerToNatural (maxUnsigned w))
{-# INLINE top #-}

-- | /O(n · w)/. Construct the tightest progression covering an ascending list of
-- distinct unsigned bitvectors. Elements are assumed to lie in @[0, 2^w)@ and
-- to be strictly increasing (no duplicates). Returns 'Nothing' on the empty
-- list.
fromAscEltList :: (1 <= w) => NatRepr w -> [Natural] -> Maybe (Domain w)
-- References:
--
-- * SASI Definition 2, Abstraction function
fromAscEltList w =
  \case
    [] -> Nothing
    [x] -> Just (mk w x 1 0)
    (x : xs) ->
      let !diffs = zipWith (-) xs (x:xs)
          !d = Prelude.foldr1 Prelude.gcd (map toInteger diffs)
          !nn = fromInteger ((toInteger (last xs) - toInteger x) `Prelude.div` d)
      in Just (mk w x (fromInteger d) nn)

-- ------------------------------------------------------------------
-- * Canonicalization

-- | A progression in canonical form: the unique representative its set gets
-- from 'canonicalize'. The constructor is hidden, so the only way to obtain a
-- @Canonical@ is via 'canonicalize'; that is what makes its instances sound:
--
--   * @'Eq' ('Canonical' w)@ /is/ set equality (see 'eqCorrect'),
--   * @'Ord'@ and @'Hashable'@ are likewise functions of the denoted set,
--
-- so @Canonical@ values are safe to use directly as @Map@\/@Set@ keys, as
-- hash-cons or memo keys, and for dedup. Recover the underlying 'Domain' with
-- 'getCanonical'.
newtype Canonical w = Canonical (Domain w)
  deriving (Eq, Ord, Show)

-- | The underlying canonical 'Domain'. It is 'proper', and equal denoted sets
-- give structurally-equal results.
getCanonical :: Canonical w -> Domain w
getCanonical (Canonical c) = c
{-# INLINE getCanonical #-}

-- | Hashes the denoted set: two 'Canonical' values are equal iff their sets
-- are, so this agrees with 'Eq' as a hashing key requires.
instance Hashable (Canonical w) where
  hashWithSalt salt (Canonical Domain{start, stride, n, mask}) =
    salt `hashWithSalt` start `hashWithSalt` stride
         `hashWithSalt` n `hashWithSalt` mask

-- | /O(w)/. Lossless canonical form: the unique 'proper' representative of a
-- progression's /set/, wrapped in 'Canonical'. Two progressions denote the same
-- set iff their 'canonicalize' results are equal (the @'Eq' 'Canonical'@
-- instance), so consumers who want @O(1)@ equality — hash-consing, dedup, memo
-- keys — can 'canonicalize' on demand and then use the derived @Eq@\/@Ord@\/
-- @Hashable@.
--
-- Among the 'proper' representations of a set this picks the one with the
-- smallest stride, tie-broken by smallest start. It is @O(w)@ rather than a
-- number-theoretic search because the only representational freedom left to
-- collapse on a non-saturated progression is /orientation/: a progression and
-- its reverse denote the same set with strides @t@ and @2^w − t@, so the
-- minimal stride is just @min(t, 2^w − t)@. (@g = 'strideGcd'@ is fixed by the
-- set, and on a non-saturated progression so is the step count @n@.) The
-- /saturated/ regimes carry extra freedom that 'mk'\/'proper' already pin, so
-- 'canonicalize' leaves them alone:
--
--   * /full coset/ (@n + 1 = orbitLen@): the orbit is the whole subgroup, so
--     any stride generating @⟨g⟩@ and any @n ≥ orbitLen − 1@ denote the same
--     set; 'mk' pins @stride = g@, @start < g@, @n = orbitLen − 1@.
--   * /singleton/ (@n = 0@): a one-point set has no stride; 'mk' pins it to 1.
--   * /coset minus one point/ (@n + 2 = orbitLen@): every unit stride
--     represents the set, so the minimum collapses to @g@ with the start
--     shifted one step back.
--
-- == Why this is opt-in rather than part of 'proper'
--
-- The split is /computational/, not about precision (operations are
-- orientation-/representation-robust, so deferring any normalization costs no
-- precision). The load-bearing 'proper' invariant is the cardinality clause
-- @n < orbitLen@: operations read @'size' = n + 1@ as the true element count
-- (e.g. 'eqExact'\'s size short-circuit, the union\/intersection sizes in
-- 'compactify'), which holds only when the step count isn\'t inflated past the
-- orbit. That clause /must/ be maintained, and 'mk' does. The remaining
-- 'proper' pins — full-coset @stride = g@\/@start < g@, singleton @stride = 1@ —
-- are representational like orientation, but 'mk' establishes them for free on
-- every construction, so there is no reason /not/ to. Orientation is the one
-- normalization that is /not/ free to maintain: making it a 'proper' invariant
-- would add a @min(t, 2^w − t)@ flip plus a result re-normalization to every
-- operation, and (since 'strideGcd', 'orbitLen', 'size', and membership are all
-- already orientation-invariant) no operation reads anything it would enable.
-- Its sole consumer is equality, so it is deferred here and paid only when an
-- @O(1)@-equality key is actually wanted.
--
-- == Examples
--
-- A large stride reverses to its minimal orientation. At @w = 4@, walking
-- stride 11 from 1 visits @{1, 12, 7, 2}@; the same set is the stride-@16 − 11
-- = 5@ progression from 2, and 'canonicalize' picks the smaller stride:
--
-- >>> let a = mk4 1 11 3
-- >>> display a
-- "[.**....*....*...]  = [1,12,7,2]"
-- >>> display (getCanonical (canonicalize a))
-- "[.**....*....*...]  = [2,7,12,1]"
-- >>> canonicalize a == canonicalize (mk4 2 5 3)
-- True
canonicalize :: Domain w -> Canonical w
canonicalize c@Domain{start = s, stride = t, n = nn, mask = m} = Canonical $
  case () of
    _ | nn + 1 == orbitLen c -> c                  -- full coset: already canonical
      | nn == 0              -> c                   -- singleton: stride already 1
      | nn + 2 == orbitLen c ->                     -- coset minus a single point
          mkChecked ((s + modNeg m t + g) .&. m) g nn
      | t <= modNeg m t      -> c                   -- already the smaller orientation
      | otherwise            -> mkChecked (end c) (modNeg m t) nn  -- reverse
  where
    g = strideGcd c
    -- Build a 'Domain' with the stored mask, asserting the result is 'proper'.
    -- The orientation flip preserves 'strideGcd' (and hence 'orbitLen'), and the
    -- coset-minus-one rewrite uses @stride = g@ with @n@ unchanged, so neither
    -- branch needs the saturation handling that 'mk' applies.
    mkChecked s' t' n' =
      let d = Domain { start = s', stride = t', n = n', mask = m }
      in assert (proper d) d

-- ------------------------------------------------------------------
-- * Conversion

-- | /O(w)/. Convert a progression to an arithmetic domain (wrapped interval).
--
-- For non-self-wrapping progressions, the result is the interval @[start, end]@
-- (over-approximating by collapsing to stride = 1). For self-wrapping progressions,
-- the orbit visits exactly the values congruent to @start@ modulo
-- @g = gcd(stride, 2^w)@, so we use the tightest such interval:
-- @[start \`mod\` g, mask + 1 - g + (start \`mod\` g)]@.
toArith :: Domain w -> A.Domain w
-- For self-wrapping progressions, this does not yield the tightest interval
-- that contains all of their points. By the three-gap theorem (Sós 1957,
-- Świerczkowski 1958, Van Ravenstein 1988), that interval would be the
-- complement of the largest gap between elements. This is computable via
-- Ostrowski-decomposition and was implemented previously, but removed as it was
-- very complex. You can find it in the git history if you need it.
toArith c = if isSelfWrapping c then cosetArc c else startEndArc c

-- | The arith hull of a progression: the arc @[start, start + n·stride]@. In
-- contrast to 'toArith', saturates to top when @n·stride >= 2^w@ (i.e., on
-- self-wrapping orbits).
hull :: Domain w -> A.Domain w
hull c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  A.interval (toInteger m) (toInteger s) (toInteger (nn * t))

-- | /O(w)/. The arc @[start, ..., end]@ on the number circle, ignoring stride.
-- The convex hull (in the wrapped-interval sense) of a non-self-wrapping orbit;
-- under-approximates a self-wrapping orbit, so caller must ensure the input
-- is not self-wrapping.
startEndArc :: Domain w -> A.Domain w
startEndArc c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  assert (Prelude.not (isSelfWrapping c)) $
  -- Non-self-wrapping: @n·stride < 2^w@, so the arc length is exactly @n·t@.
  A.interval (toInteger m) (toInteger s) (toInteger (nn * t))

-- | /O(w)/. The arc @[start \`mod\` g, ..., start \`mod\` g + (2^w - g)]@,
-- where @g = gcd(stride, 2^w)@. The union of all bitvectors congruent to
-- @start@ modulo @g@; sound on any progression, but only a tight cover on
-- self-wrapping orbits, so caller must ensure the input is self-wrapping.
cosetArc :: Domain w -> A.Domain w
cosetArc c@Domain{start = s, mask = m} =
  assert (proper c) $
  assert (isSelfWrapping c) $
  let g = strideGcd c
      imask = toInteger m
      lo = toInteger (s .&. (g - 1))
  in A.interval imask lo (imask + 1 - toInteger g)

-- | /O(w)/. Convert an arithmetic domain (wrapped interval) to a progression.
fromArith :: NatRepr w -> A.Domain w -> Maybe (Domain w)
fromArith w = \case
  A.BVDAny _mask -> Just (mk w 0 1 (integerToNatural imask))
    where imask = maxUnsigned w
  d | A.isBottom d -> Nothing
    | otherwise -> case A.arithDomainData d of
        Nothing -> Nothing
        Just (lo, sz) -> Just (mk w (integerToNatural lo) 1 (integerToNatural sz))

-- TODO: The bitwise->arith helper below duplicates
-- 'bitwiseToArithDomain' in "What4.Domains.BV". Once that is moved into a
-- common module that 'Strides' can import (e.g. by adding a dep from
-- 'BV.Bitwise' to 'BV.Arith'), inline-call it instead.

-- | /O(w)/. Convert a progression to a bitwise domain.
--
-- A thin wrapper around 'forcedBits': the resulting bitwise domain has
-- forced-1 bits exactly @ones@ and forced-0 bits exactly @zeros@. Both
-- the low (stride pinning) and high (span pinning) sources contribute.
toBitwise :: Domain w -> B.Domain w
toBitwise = strideBitwise

-- | /O(w)/. Bitwise domain capturing every bit forced by the progression.
-- Equivalent to 'toBitwise'; named for compatibility with downstream
-- callers that distinguish stride-derived bitwise info from arc-derived
-- info. Span pinning (see 'forcedBits') subsumes the high-bit information
-- the arc-based path would have contributed.
strideBitwise :: Domain w -> B.Domain w
strideBitwise c =
  let imask = toInteger (mask c)
      (zeros, ones) = forcedBits c
  in B.interval imask (toInteger ones) (imask `Bits.xor` toInteger zeros)

-- | /O(w)/. Bits forced to known values across the whole orbit, as a
-- @(zeros, ones)@ pair: a bit set in @zeros@ is @0@ in every member; a
-- bit set in @ones@ is @1@ in every member; a bit in neither may take
-- both values. The two values are bit-disjoint
-- (see 'forcedBitsDisjoint'), and every member of the progression
-- agrees with them ('forcedBitsMember').
--
-- Two independent sound sources are unioned:
--
--   * /Stride pinning./ Writing @stride = 2^v · m@ with @m@ odd, every
--     orbit element shares its low @v@ bits with @start@. (Each step
--     adds a multiple of @2^v@, leaving the low @v@ bits unchanged.)
--   * /Span pinning./ Let @R = n · stride@ be the integer span of the
--     orbit. Every bit position @k@ with @2^k > R@ and
--     @bit_k(start) == bit_k(start + R)@ is fixed at that common value.
--     (Crossing a @2^k@ boundary flips bit @k@ via a carry; the span
--     bound @2^k > R@ caps the boundary crossings at one, and
--     endpoint-bit agreement rules even that one out.)
--
-- The two contributions are bit-disjoint: stride pinning sets bits
-- @[0, v)@; span pinning only sets bits @≥ v + 1@ (because
-- @R ≥ stride ≥ 2^v@ means @intLog2 R ≥ v@, so the span mask starts at
-- bit @v + 1@).
forcedBits :: Domain w -> (Natural, Natural)
forcedBits c@Domain{start = s, mask = m} =
  let notN x       = m `Bits.xor` x             -- @~x@ at the operand's width
      g            = strideGcd c
      lowMask      = g - 1                       -- bits [0, v)
      lowOnes      = s Bits..&. lowMask
      lowZeros     = lowMask Bits..&. notN s
      span_        = n c * stride c
      -- Bits @k@ with @2^k > span_@. When @span_ >= 2^w@, no bit at the
      -- operand's width is above the span, so the mask is @0@.
      belowSpan    = integerToNatural (Arith.bitsBelow (toInteger span_))
                       Bits..&. m
      spanMask     = notN belowSpan
      sEnd         = (s + span_) Bits..&. m
      agree        = notN (s `Bits.xor` sEnd)
      highForced   = agree Bits..&. spanMask
      highOnes     = highForced Bits..&. s
      highZeros    = highForced Bits..&. notN s
  in (lowZeros Bits..|. highZeros, lowOnes Bits..|. highOnes)

-- | /O(w)/. The progression covering every @w@-bit value that agrees with
-- the forced-bit pair @(zeros, ones)@ — a @0@ at every bit set in @zeros@,
-- a @1@ at every bit set in @ones@ — and lies in the unsigned interval
-- @[lo, hi]@. See 'fromForcedBitsCorrect'.
--
-- Preconditions: @zeros@ and @ones@ are bit-disjoint and fit in @w@ bits,
-- @lo <= hi <= 2^w - 1@, and at least one value satisfies all the
-- constraints (the result is still a proper 'Domain', but unspecified,
-- otherwise).
--
-- Note that this constructs a /cover/ of the constraint set from scratch;
-- it is not a refinement operator. The subset-preserving analogue, which
-- refines an existing progression in place by forced bits, is
-- 'liftForcedBits'.
fromForcedBits ::
  (1 <= w) =>
  NatRepr w ->
  -- | @(zeros, ones)@
  (Natural, Natural) ->
  -- | @(lo, hi)@
  (Natural, Natural) ->
  Domain w
-- This is the shared kernel behind the bitwise operations ('andFast',
-- 'andPrecise', 'andSingleton', 'xorFast'), the bitwise conversion
-- ('fromBitwise'), the constant-shift fallback in 'lshrRaw', and the
-- bit-aware refinements of the width-changing conversions ('zext', 'sext',
-- 'concat', 'select'). 'fromForcedBitsSigned' is the variant for intervals
-- on the signed number line ('ashrRaw'). The reasoning, in coset terms
-- (writing
-- @m = 2^w - 1@ for the width mask, so @m XOR zeros@ is the value with a
-- @1@ exactly at the positions /not/ forced to @0@):
--
--   * /Stride./ All bits below the lowest free (unforced) bit @v@ are
--     determined, so every admissible value is congruent to @ones@ mod
--     @2^v@: the constraint set lies in a single coset of the subgroup
--     @2^v·Z/2^wZ@, giving stride @d = 2^v@.
--   * /Lower bound./ Every admissible value sets all bits of @ones@, and
--     bitwise dominance implies unsigned dominance: @x .&. ones == ones@
--     forces @x >= ones@. Since @ones@ is itself on the coset, it is a
--     valid anchor — scattered forced ones /above/ the lowest free bit
--     raise the start without leaving the coset.
--   * /Upper bound./ Dually, every admissible value clears all bits of
--     @zeros@, so @x <= m XOR zeros@.
--   * /Interval./ The extra constraint @[lo, hi]@ (Warren bounds, operand
--     ranges, arith conversion bounds, ...) intersects all of the above:
--     the start is @max lo ones@ aligned up to the coset, and the step
--     count is floored at @min hi (m XOR zeros)@.
--
-- When every bit is forced, the result is the singleton @{ones}@ (the
-- interval cannot exclude it when the nonemptiness precondition holds).
fromForcedBits w (zeros, ones) (lo, hi) =
  assert (zeros Bits..&. ones == 0) $
  assert (zeros <= integerToNatural (maxUnsigned w)) $
  assert (ones <= integerToNatural (maxUnsigned w)) $
  assert (lo <= hi) $
  assert (hi <= integerToNatural (maxUnsigned w)) $
  let !m = integerToNatural (maxUnsigned w)
      !free = m `Bits.xor` (zeros Bits..|. ones)
  in if free == 0
       then mk w ones 1 0
       else
         let !d = lowestSetBit free
             !lo0 = max lo ones
             !lo1 = lo0 + (modSub m (ones Bits..&. (d - 1)) lo0 Bits..&. (d - 1))
             !hi' = min hi (m `Bits.xor` zeros)
             !nSteps = if hi' < lo1 then 0 else (hi' - lo1) `divByPow2` d
         in mk w (lo1 Bits..&. m) d nSteps

-- | /O(w)/. Signed-interval variant of 'fromForcedBits': the progression
-- covering every @w@-bit value that agrees with the forced-bit pair
-- @(zeros, ones)@ and whose /signed/ value lies in @[lo, hi]@. See
-- 'fromForcedBitsSignedCorrect'.
--
-- Preconditions: as for 'fromForcedBits', with
-- @-2^(w-1) <= lo <= hi <= 2^(w-1) - 1@.
fromForcedBitsSigned ::
  (1 <= w) =>
  NatRepr w ->
  -- | @(zeros, ones)@
  (Natural, Natural) ->
  -- | @(lo, hi)@, as signed values
  (Integer, Integer) ->
  Domain w
-- The coset/dominance reasoning of 'fromForcedBits' transfers to the
-- signed number line wholesale:
--
--   * The stride @d@ divides @2^w@, so a value's residue mod @d@ is the
--     same whether read from its unsigned or signed representative, and
--     coset alignment can run in plain integer arithmetic.
--   * The bit-derived bounds become the signed values of the extremal
--     admissible /patterns/: when the sign bit is forced, the patterns
--     @ones@ and @m XOR zeros@ themselves (read as signed); when it is
--     free, the most-negative pattern @ones .|. 2^(w-1)@ and the
--     most-positive pattern @(m XOR zeros) .&. ~(2^(w-1))@.
fromForcedBitsSigned w (zeros, ones) (lo, hi) =
  assert (zeros Bits..&. ones == 0) $
  assert (zeros <= integerToNatural (maxUnsigned w)) $
  assert (ones <= integerToNatural (maxUnsigned w)) $
  assert (lo <= hi) $
  assert (NR.minSigned w <= lo && hi <= NR.maxSigned w) $
  let !m = integerToNatural (maxUnsigned w)
      !free = m `Bits.xor` (zeros Bits..|. ones)
      !half = (m + 1) `Bits.shiftR` 1  -- 2^(w-1), the sign bit
      !signFree = free Bits..&. half /= 0
      !loPat = if signFree then ones Bits..|. half else ones
      !hiPat = if signFree
                 then (m `Bits.xor` zeros) Bits..&. (m `Bits.xor` half)
                 else m `Bits.xor` zeros
  in if free == 0
       then mk w ones 1 0
       else
         let !d = lowestSetBit free
             !dI = toInteger d
             !r = toInteger (ones Bits..&. (d - 1))
             !lo0 = max lo (toSigned w (toInteger loPat))
             !hi' = min hi (toSigned w (toInteger hiPat))
             !lo1 = lo0 + ((r - lo0) `Prelude.mod` dI)
             !nSteps = if hi' < lo1 then 0 else (hi' - lo1) `Prelude.div` dI
         in mk w (asN w lo1) d (integerToNatural nSteps)

-- | /O(w)/. Convert a bitwise domain to a progression: 'fromForcedBits' at
-- the bitwise domain's forced bits and numeric bounds.
fromBitwise :: NatRepr w -> B.Domain w -> Maybe (Domain w)
fromBitwise w b =
  case NR.isZeroOrGT1 w of
    Left _ -> Nothing  -- unreachable: 'B.Domain' widths are positive
    Right LeqProof ->
      let !(lo, hi) = B.bitbounds b
      in Just (fromForcedBits w (knownZerosOnesNat b)
                 (integerToNatural lo, integerToNatural hi))

-- ------------------------------------------------------------------
-- * Queries

-- | /O(w log w)/. Test if the given value is a member of the progression.
--
-- == Examples
--
-- >>> let evens = mk4 0 2 7
-- >>> display evens
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
-- >>> member evens 4
-- True
-- >>> member evens 3
-- False
member :: Domain w -> Natural -> Bool
-- References:
--
-- * SASI Definition 3, Membership function
--
-- SASI\'s @member@ function is actually broken. Their concretization function
-- matches our 'toList', which means that their intervals can semantically
-- support wrapping around multiple times, but their membership function only
-- supports non-self-wrapping intervals. This is likely due to its heritage
-- from Wrapped Intervals, where self-wrapping stride-1 intervals would result
-- in saturation.
member c v = assert (proper c) $
  case valueIndexMaybe c v of
    Just i  -> i <= n c
    Nothing -> False

-- | /O(2^w \/ g)/, where @g = gcd(stride, 2^w)@. Concretization function.
--
-- Enumerates the (distinct) elements of a progression, in the order they are
-- produced by the progression: @start, start + stride, ..., end@ (all mod
-- @2^w@).
toList :: Domain w -> [Natural]
-- References:
--
-- * CLP Section 3, @conc@
-- * SASI Definition 1, Concretization function
toList c@Domain{start, stride, n} = assert (proper c) $ go 0 start
  where
    go !i !v
      | i == n    = [v]
      | otherwise = v : go (i + 1) (modMask c (v + stride))

-- | /O(w)/. The number of distinct values in the progression: @n + 1@.
--
-- == Examples
--
-- >>> let a = mk4 2 1 4
-- >>> display a
-- "[..*****.........]  = [2,3,4,5,6]"
-- >>> size a
-- 5
-- >>> size (top w4)
-- 16
size :: Domain w -> Natural
size c@Domain{n} = assert (proper c) $ n + 1
{-# INLINE size #-}

-- | /O(w)/. Exact set-equality: 'True' iff @a@ and @b@ denote the same set.
-- This is literally @'canonicalize' a == 'canonicalize' b@ — 'canonicalize' is
-- a lossless normal form, so structural equality of canonical forms /is/ set
-- equality (see 'eqCorrect'). At @O(w)@ it dominates the @O(w^2)@ 'eqExact'
-- oracle it is checked against.
--
-- == Examples
--
-- >>> eq (mk4 1 11 3) (mk4 2 5 3)   -- same set {1,2,7,12}, different strides
-- True
-- >>> eq (mk4 0 2 7) (mk4 0 4 3)    -- evens vs {0,4,8,12}
-- False
eq :: Domain w -> Domain w -> Bool
eq a b = canonicalize a == canonicalize b

-- | /O(w)/. Sound, reflexive, and transitive but coarse approximation of
-- 'leqExact'. Use 'leqPrecise' for a finer (but non-transitive) check, or
-- 'leqExact' for an exact (but quadratic) one.
--
-- == Examples
--
-- Every even is in @⊤@, but @⊤@ is not contained in the evens:
--
-- >>> let evens = mk4 0 2 7
-- >>> display evens
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
-- >>> leq evens (top w4)
-- True
-- >>> leq (top w4) evens
-- False
leq :: Domain w -> Domain w -> Bool
-- Writing @stride = 2^v · m@ for odd @m@, the subgroup @⟨stride⟩@ in
-- @Z\/2^w@ is @⟨2^v⟩@. We accept @a ⊆ b@ if /any/ of:
--
--   (1) /Equal/: @a == b@. Transitive on the nose.
--   (2) /Full b/, in three parts:
--         (2a) @b@ spans its full orbit (@n b + 1 == orbitLen b@);
--         (2b) /Coset/: @start a − start b ∈ ⟨stride b⟩@; and
--         (2c) /Subgroup/: @⟨stride a⟩ ⊆ ⟨stride b⟩@, i.e. @strideGcd b@
--              divides @stride a@.
--       If both @b@ and @c@ are full, the coset and subgroup containments
--       chain: @⟨stride a⟩ ⊆ ⟨stride b⟩ ⊆ ⟨stride c⟩@, etc.
--
-- A singleton-on-orbit fast path would also be sound and would catch
-- additional cases, but membership testing is /O(w log w)/ ('member'); we
-- keep that path in 'leqPrecise' instead so 'leq' stays /O(w)/.
leq a b = assert (proper a) $ assert (proper b) $
  equal               -- (1)
  || (bIsFull         -- (2a)
        && cosetMatches      -- (2b)
        && subgroupContained -- (2c)
     )
  where
    equal             = a == b
    bIsFull           = n b + 1 == orbitLen b
    cosetMatches      = wrapOffset b (start a) `mod` strideGcd b == 0
    subgroupContained = stride a `mod` strideGcd b == 0

-- | /O(w log w)/. Sound and finer approximation of 'leqExact' than 'leq'.
-- Reflexive but not transitive in general.
leqPrecise :: Domain w -> Domain w -> Bool
-- The check embeds @a@\'s orbit into @b@\'s index space:
--
--   (1) /On orbit/: @start a@ lies on @b@\'s orbit (at some @b@-index
--       @iAStart@), and @iAStart <= n b@.
--   (2) /Singleton/: if @a@ is a singleton, (1) is enough.
--   (3) Otherwise:
--         (3a) /Stride aligned/: @stride b@ divides @stride a@; that
--              multiple @aStepInB@ is how far each step of @a@ advances
--              in @b@-index space; and
--         (3b) /Fits in b/: after @n a@ such steps, the @b@-index reached
--              still does not exceed @n b@.
leqPrecise a b = assert (proper a) $ assert (proper b) $
  case valueIndexMaybe b (start a) of
    Nothing      -> False  -- (1) start a not on b's orbit
    Just iAStart ->
      onOrbit iAStart                       -- (1)
      && (aIsSingleton                      -- (2)
          || (strideAligned                 -- (3a)
              && aFitsInsideB iAStart       -- (3b)
             ))
  where
    aIsSingleton  = n a == 0
    onOrbit i     = i <= n b
    strideAligned = stride a `mod` stride b == 0
    aStepInB      = stride a `Prelude.div` stride b
    aFitsInsideB i = i + n a * aStepInB <= n b

-- | /O(w log w)/. Like 'leqExact', but never runs the quadratic window count:
-- returns @Just@ the exact answer on the sub-domain it can decide cheaply, and
-- 'Nothing' on the one residual case that genuinely needs 'leqExact'\''s
-- 'floorSum'. Exact wherever it is defined.
leqExactPartial :: Domain w -> Domain w -> Maybe Bool
-- Writing @stride = 2^v · m@ for odd @m@, the subgroup of @Z\/2^w@ generated
-- by @stride@ is @⟨2^v⟩@ — the odd factor @m@ is invertible mod @2^w\/2^v@
-- and so doesn\'t change which subgroup is generated. The check is then:
--
--   (1) /Coset/: @start a@ lies on @b@\'s coset, i.e. @start a − start b ∈
--       ⟨2^{v_b}⟩@. Read off as @b@-index @iAStart@.
--   (2) /Subgroup/: @⟨stride a⟩ ⊆ ⟨stride b⟩@, i.e. @v_a ≥ v_b@. Equivalent
--       to @2^{v_b} = strideGcd b@ dividing @stride a@.
--   (3) /Window/: the indices @{ iAStart + i · aStep mod orbitLen b
--       | 0 ≤ i ≤ n a }@ all lie in @[0, n b]@, where
--       @aStep = stride a · stride b^{-1} mod orbitLen b@ in @b@\'s index space.
--
-- All cheap branches of (3) — @a@ a singleton, @b@ full, /pigeonhole/
-- (@|a| > |b|@: under (2) @a@\'s b-indices are distinct, so @a@ has too many
-- elements to fit), /monoFits-accept/ (a's window walks an unwrapped run that
-- stays in @[0, n b]@; sound regardless of window size), and /small window/
-- (where @a@\'s indices can only fit @[0, n b]@ in at most one orientation, so
-- a 'monoFits' rejection is exact) — are @O(w)@ each. (The @Maybe@-valued
-- counterpart and its exactness — wherever it commits, it equals the oracle
-- 'leqExact' — are proven in Cryptol at @w = 4@, with @w = 8@ corroborated by
-- randomized testing; see @doc/strides.cry@,
-- @leqExactPartial@\/@leqExactPartialAgrees@.) Only the /residual/ case — large
-- window over non-full @b@, with @a@ small enough to fit (@|a| ≤ |b|@) but
-- 'monoFits' rejecting — is left to the caller as 'Nothing': there @a@ may fit
-- by wrapping, which needs a count.
leqExactPartial a b = assert (proper a) $ assert (proper b) $
  case valueIndexMaybe b (start a) of
    Nothing -> Just False                            -- (1) fails: start a off coset
    Just iAStart
      | aIsSingleton          -> Just (iAStart <= n b)  -- (1) ok; (2)/(3) vacuous
      | Prelude.not subgroupContained -> Just False     -- (2) fails
      | bIsFull               -> Just True              -- (3) vacuous: full orbit
      | n a > n b             -> Just False             -- (3) pigeonhole
      | monoFits iAStart      -> Just True              -- (3) monoFits-accept
      | smallWindow           -> Just False             -- (3) exact reject
      | otherwise             -> Nothing                -- (3) needs floorSum
  where
    gB :: Natural
    gB = strideGcd b
    mB :: Natural
    mB = orbitLen b
    aIsSingleton, subgroupContained, bIsFull, smallWindow :: Bool
    aIsSingleton      = n a == 0
    subgroupContained = stride a `mod` gB == 0   -- (2)
    bIsFull           = n b + 1 == mB
    smallWindow       = (n b + 1) * 2 <= mB
    -- @a@'s stride translated to @b@-index space, modulo b's orbit length.
    invSB, aStep :: Natural
    invSB = invModPow2 (stride b `divByPow2` gB) mB
    aStep = ((stride a `divByPow2` gB) * invSB) .&. (mB - 1)
    -- (3), monoFits: @a@'s indices fit @[0, n b]@ if they fit without
    -- wrapping in some orientation. Forward: @iAStart + n a · aStep@
    -- never exceeds @n b@. Backward: from the last index, stepping by
    -- @mB - aStep@, the reach never exceeds @n b@. /Sound True/ regardless of
    -- window size (an unwrapped run stays in @[0, n b]@); /exact/ — i.e. False
    -- is also sound — only under 'smallWindow', where the window cannot fit
    -- by wrapping.
    monoFits :: Natural -> Bool
    monoFits iAStart =
      let nA       = n a
          forward  = iAStart + nA * aStep
          iEnd     = forward `mod` mB
          backward = iEnd + nA * (mB - aStep)
      in iAStart <= n b && (forward <= n b || backward <= n b)

-- | /O(w^2)/. The 'floorSum'-based window count that decides the one case
-- 'leqExactPartial' leaves open (a large window over a non-full @b@). Of the
-- @n a + 1@ visited @b@-indices @{ iAStart + i · aStep mod orbitLen b }@,
-- count how many fall in @[0, n b]@; @a@\'s window fits iff that count is
-- @n a + 1@.
--
-- Correct on /any/ proper @a@, @b@ with @start a@ on @b@\'s coset and
-- @⟨stride a⟩ ⊆ ⟨stride b⟩@ (it does not rely on the large-window guard); the
-- guard only governs /whether/ this @O(w^2)@ path is needed over the @O(w)@
-- one. 'leqExact' uses it solely on 'leqExactPartial'\''s 'Nothing'.
leqExactWindow :: Domain w -> Domain w -> Bool
leqExactWindow a b =
  let gB      = strideGcd b
      mB      = orbitLen b
      invSB   = invModPow2 (stride b `divByPow2` gB) mB
      aStep   = ((stride a `divByPow2` gB) * invSB) .&. (mB - 1)
      iAStart = valueIndex b (start a)
      nA1     = n a + 1
      wWidth  = n b + 1
      hits    = nA1 + floorSum nA1 mB aStep iAStart
                    - floorSum nA1 mB aStep (iAStart + mB - wWidth)
  in hits == nA1

-- | /O(w log w)/, except /O(w^2)/ on the residual case: @b@\'s window is
-- larger than half its orbit, @b@ is not full, @a@ has at most as many points
-- as @b@\'s window, and @a@\'s indices in @b@\'s index space neither fit
-- forward nor backward without wrapping. Partial order on progressions:
-- @leqExact a b@ iff every element of @a@ is in @b@.
leqExact :: Domain w -> Domain w -> Bool
-- 'leqExactPartial' decides everything but the residual large-window wrapping
-- case in @O(w)@; that remaining case is the only one where @a@ can fit @b@\'s
-- window by wrapping, so it falls back to the @O(w^2)@ 'leqExactWindow' count.
leqExact a b = fromMaybe (leqExactWindow a b) (leqExactPartial a b)

-- | /O(w)/. Does this progression self-wrap? A progression is self-wrapping if the
-- cumulative distance traversed by its orbit (@n * stride@, where @n@ is the
-- number of steps from @start@ to @end@) exceeds @2^w@. Geometrically: walking
-- around the number circle from @start@, the orbit passes its starting point
-- at least once before reaching @end@.
--
-- Note that all points in a valid progression are distinct by construction, so
-- self-wrapping does /not/ mean that the progression values multiple times. It
-- only describes how far the orbit traveled.
isSelfWrapping :: Domain w -> Bool
isSelfWrapping Domain{stride, n, mask} = n * stride > mask
{-# INLINE isSelfWrapping #-}

-- | /O(w^2)/. Exact set-equality on progressions: 'True' iff @a@ and @b@
-- denote the same set of bitvectors. Short-circuits on size mismatch (a
-- necessary condition); otherwise checks 'leqExact' in one direction —
-- equal cardinalities plus containment force set equality.
--
-- Internal: the public equality test is 'eq' (@O(w)@ via 'canonicalize'). This
-- @leqExact@-based decision is retained as an independent oracle that 'eq' is
-- checked against (see 'eqCorrect'); 'eqExactCorrect' in turn ties it to the
-- 'toList' ground truth, so the two algorithms cross-check each other.
eqExact :: Domain w -> Domain w -> Bool
eqExact a b = size a == size b && leqExact a b

-- ------------------------------------------------------------------
-- Lifted operations (internal scaffolding; not exported)
--
-- These helpers convert a progression to an arithmetic or bitwise domain, apply the
-- corresponding operation there, and convert back. Since the result of an
-- @A.*@ or @B.*@ op on a proper input is always proper (never bottom),
-- @fromArith@\/@fromBitwise@ here always succeed, and we project from the
-- 'Maybe' with 'fromJustUnsafe'. This loses precision (the round-trip
-- collapses non-trivial strides), but is sound.

fromJustUnsafe :: String -> Maybe a -> a
fromJustUnsafe loc = \case
  Just x  -> x
  Nothing -> error ("What4.Domains.BV.Strides: " ++ loc ++ ": Nothing")
{-# INLINE fromJustUnsafe #-}

liftArith1 ::
  (1 <= w) =>
  NatRepr w ->
  (A.Domain w -> A.Domain w) ->
  Domain w -> Domain w
liftArith1 w f c =
  fromJustUnsafe "liftArith1" (fromArith w (f (toArith c)))
{-# INLINE liftArith1 #-}

liftArith2 ::
  (1 <= w) =>
  NatRepr w ->
  (A.Domain w -> A.Domain w -> A.Domain w) ->
  Domain w -> Domain w -> Domain w
liftArith2 w f a b =
  fromJustUnsafe "liftArith2" (fromArith w (f (toArith a) (toArith b)))
{-# INLINE liftArith2 #-}

liftBitwise1 ::
  (1 <= w) =>
  NatRepr w ->
  (B.Domain w -> B.Domain w) ->
  Domain w -> Domain w
liftBitwise1 w f c =
  fromJustUnsafe "liftBitwise1" (fromBitwise w (f (toBitwise c)))
{-# INLINE liftBitwise1 #-}

liftBitwise2 ::
  (1 <= w) =>
  NatRepr w ->
  (B.Domain w -> B.Domain w -> B.Domain w) ->
  Domain w -> Domain w -> Domain w
liftBitwise2 w f a b =
  fromJustUnsafe "liftBitwise2" (fromBitwise w (f (toBitwise a) (toBitwise b)))
{-# INLINE liftBitwise2 #-}

-- ------------------------------------------------------------------
-- * Arithmetic

-- | /O(w)/. Negation: stride is preserved; the orbit reverses, so the new
-- @start@ is the old @end@ negated. The step count @n@ is unchanged.
--
-- == Examples
--
-- >>> let a = mk4 2 1 4
-- >>> display a
-- "[..*****.........]  = [2,3,4,5,6]"
-- >>> display (negate w4 a)
-- "[..........*****.]  = [10,11,12,13,14]"
negate :: (1 <= w) => NatRepr w -> Domain w -> Domain w
negate w c@Domain{stride, n = nn, mask} =
  assert (proper c) $
  mk w (modNeg mask (end c)) stride nn

-- | /O(w)/. Addition.
--
-- == Examples
--
-- >>> let a = mk4 2 3 2; b = mk4 2 1 2
-- >>> display a
-- "[..*..*..*.......]  = [2,5,8]"
-- >>> display b
-- "[..***...........]  = [2,3,4]"
-- >>> display (add w4 a b)
-- "[....*********...]  = [4,5,6,7,8,9,10,11,12]"
-- >>> diagram (add w4 (top w4) (top w4))
-- "[****************]"
--
-- Adding the evens to themselves stays the evens (stride is preserved as
-- @gcd(2, 2) = 2@):
--
-- >>> let evens = mk4 0 2 7
-- >>> display (add w4 evens evens)
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
--
-- 'add' is /orientation-robust/ ('orientRobustAddSub'): the cross-operand
-- integer gcd that fixes the result stride is sensitive to whether each operand
-- is represented forwards or via its 'reverseD'. We pick the tightest
-- orientation (via the closed-form 'addSubSize'), which never loses to and
-- sometimes beats the raw single-orientation 'addRaw' (see
-- 'addRobustDominatesRaw').
add :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
add w = orientRobustAddSub w (addRaw w)

-- | /O(w)/. The single-orientation addition kernel (see 'add' for the
-- orientation-robust wrapper that should be preferred).
addRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 4.2 Arithmetic Operations
-- * WI 3.2 Analysing expressions
--
-- In the CLP (start, end, stride) formulation, they give:
--
--   (l1, u1, δ1) + (l2, u2, δ2) := (l1 + l2, u1 + u2, gcd(δ1, δ2))
--
-- (This only works with some assumptions on endpoint ordering and overflow.)
--
-- Shift each orbit by the other's @start@, then walk @span\'@ steps from
-- @start a + start b@ in stride @d = gcd(stride a, stride b)@ (with singleton
-- operands skipped), where @span' = n a · (stride a / d) + n b · (stride b / d)@
-- — both ratios are exact since @d@ divides both strides. The conceptual
-- orbit may overshoot the available step count (e.g. when summing two full
-- cosets @span'@ doubles); 'clampToOrbit' caps it, and 'mk' canonicalizes
-- the saturated case to the full coset of @start'@.
addRaw w a b =
  assert (proper a) $
  assert (proper b) $
  mk w start' d (clampToOrbit (mask a) d n')
  where
    (d, n') = addSubStrideAndSteps (n a) (stride a) (n b) (stride b)
    start' = modMask a (start a + start b)

-- | /O(w)/. Subtraction.
--
-- == Examples
--
-- >>> let a = mk4 4 1 4; b = mk4 1 1 2
-- >>> display a
-- "[....*****.......]  = [4,5,6,7,8]"
-- >>> display b
-- "[.***............]  = [1,2,3]"
-- >>> display (sub w4 a b)
-- "[.*******........]  = [1,2,3,4,5,6,7]"
--
-- Like 'add', 'sub' is orientation-robust ('orientRobustAddSub'): it scores
-- both representatives of each operand with the closed-form 'addSubSize' and
-- materializes the tightest.
sub :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sub w = orientRobustAddSub w (subRaw w)

-- | /O(w)/. The single-orientation subtraction kernel (see 'sub' for the
-- orientation-robust wrapper that should be preferred).
subRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
subRaw w a b =
  assert (proper a) $
  assert (proper b) $
  mk w start' d (clampToOrbit (mask a) d n')
  where
    (d, n') = addSubStrideAndSteps (n a) (stride a) (n b) (stride b)
    start' = modSub (mask a) (start a) (end b)

-- | Shared scalar kernel for 'addRaw'\/'subRaw' and the closed-form
-- 'addSubSize': compute the result stride @d@ and step count @n'@ from just the
-- operand step counts and strides.
addSubStrideAndSteps ::
  Natural {- ^ @n_a@ -} -> Natural {- ^ @stride a@ -} ->
  Natural {- ^ @n_b@ -} -> Natural {- ^ @stride b@ -} ->
  (Natural, Natural)
addSubStrideAndSteps na sa nb sb = (d, n')
  where
    d = case (na, nb) of
          (0, 0) -> 1
          (0, _) -> sb
          (_, 0) -> sa
          _      -> Prelude.gcd sa sb
    n' = na * (sa `div` d) + nb * (sb `div` d)

-- | /O(w)/. The /reverse orientation/ of a progression: the same set walked
-- backwards. The new @start@ is the old 'end', the stride becomes its modular
-- additive inverse @2^w - stride@, and the step count @n@ is unchanged.
--
-- Unlike 'negate', this denotes /exactly the same set/ as the input (verified
-- by 'reverseDSameSet'): @{start + i·stride}@ and @{end + i·(2^w − stride)}@
-- enumerate the same values in opposite order. Singletons and full cosets are
-- their own reverse after 'mk' canonicalization.
--
-- The point is precision, not the set: @stride@ and @2^w − stride@ share the
-- same 'strideGcd' (lowest set bit) but are different /integers/, so they feed
-- different cross-operand integer gcds into 'add'\/'sub'\/'mul'. Trying both
-- orientations and keeping the tighter result is what 'orientRobust' exploits.
reverseD :: NatRepr w -> Domain w -> Domain w
reverseD w c@Domain{stride, n = nn, mask} =
  assert (proper c) $
  mk w (end c) (modNeg mask stride) nn

-- | Run a sound binary operation at all (up to four) orientation combinations
-- of its operands and keep the smallest result.
--
-- Each of @a@, @b@ has two interchangeable representatives as a set — itself
-- and its 'reverseD' — that nonetheless feed different integer strides into the
-- cross-operand gcd inside 'add'\/'sub'\/'mul'. Since every orientation denotes
-- the same set, every candidate is a sound abstraction of the same true
-- result; taking the cardinality-minimum is therefore sound and /dominates/ the
-- single-orientation result (which is among the candidates). See
-- 'addRobustDominatesRaw'. Cost is /O(w)/ — a 4x constant factor, no
-- asymptotic change.
--
-- Orientations that coincide after 'mk' canonicalization (singletons, full
-- cosets) are deduplicated, so degenerate operands incur no extra work.
--
-- Used directly by 'mul', whose result size is /not/ a closed-form function of
-- the operand strides (it threads through corner products and a non-monotone
-- 'pseudoJoin'), so the result really must be materialized at each orientation.
-- 'add'\/'sub' instead use 'orientRobustAddSub', which scores orientations with
-- the closed-form 'addSubSize' and materializes only the winner.
orientRobust ::
  NatRepr w ->
  (Domain w -> Domain w -> Domain w) ->
  Domain w -> Domain w -> Domain w
orientRobust w op a b =
  List.foldl1' minBySize
    [ op ai bj | ai <- orientations a, bj <- orientations b ]
  where
    orientations c = let r = reverseD w c in if r == c then [c] else [c, r]
    minBySize x y = if size x <= size y then x else y

-- | /O(w)/. Split a progression by index parity into two sub-progressions
-- with stride @2·stride@: the even-index orbit @(start, 2t, n \`div\` 2)@ and
-- the odd-index orbit @(start + t, 2t, (n - 1) \`div\` 2)@. Their union is
-- exactly @c@, partitioned cleanly: writing @stride = 2^v · m@ for odd @m@,
-- bit @v@ of element @i@ is @bit_v(start) XOR (i mod 2)@, so the even and odd
-- halves are distinguished by bit @v@. Each half therefore pins one more low
-- bit than @c@ does.
--
-- Returns @[c]@ in the cases where the split is uninformative:
--
--   * /Singleton/ (@n = 0@): there is no second piece.
--   * /Full coset/ (@n + 1 = orbitLen@): both halves saturate back to the
--     same full coset of @c@, so the split adds no precision.
--   * /Stride at the top bit/ (@2·stride ≡ 0 mod 2^w@): the @2t@ stride is
--     ill-defined; this only arises when @t = 2^(w-1)@, which forces a
--     singleton or full coset and is already handled above.
psplit :: (1 <= w) => NatRepr w -> Domain w -> [Domain w]
psplit w c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  let !t' = (2 * t) .&. m
  in if nn == 0 || nn + 1 == orbitLen c || t' == 0
       then [c]
       else
         let !nEven = nn `Prelude.div` 2
             !nOdd  = (nn - 1) `Prelude.div` 2
             !sOdd  = (s + t) .&. m
         in [mk w s t' nEven, mk w sOdd t' nOdd]

-- | Run a sound binary operation at all (up to four) 'psplit' combinations of
-- its operands, pseudo-join the sub-results, and return whichever of the raw
-- and pseudo-joined results is smaller by cardinality.
--
-- Soundness: every concrete @x \`op\` y@ for @x ∈ a, y ∈ b@ has @x@ in some
-- 'psplit' piece of @a@ and @y@ in some piece of @b@, so it is in the
-- corresponding sub-result, hence in the pseudo-join. The min-by-size keeps
-- the raw call's result whenever it is at least as tight, so this never
-- worsens @op@ by cardinality.
--
-- Costs at most @5 · cost(op) + 3 · cost(pseudoJoin) + O(w)@ (the raw call,
-- 4 sub-ops, 3 folded pseudo-joins, and 2 'psplit' calls), still /O(w)/ for
-- /O(w)/ ops. Worth using for ops where the cross-operand interaction is
-- sensitive to bit-@v@ pinning (e.g. 'andPrecise', where each piece has one
-- more fixed low bit than the input).
psplitOp2 ::
  (1 <= w) =>
  NatRepr w ->
  (Domain w -> Domain w -> Domain w) ->
  Domain w -> Domain w -> Domain w
psplitOp2 w op a b =
  let !raw = op a b
      !subs = [ op ai bj | ai <- psplit w a, bj <- psplit w b ]
      !pj = case subs of
              []     -> raw           -- unreachable: psplit returns ≥ 1 piece
              (c:cs) -> Prelude.foldr (pseudoJoin w) c cs
  in if size raw <= size pj then raw else pj

-- | Like 'psplitOp2', but only splits the second operand — useful for
-- operations like shifts/rotates where the second argument has a structurally
-- different role and splitting only it captures most of the precision win at
-- half the work.
--
-- Costs at most @3 · cost(op) + cost(pseudoJoin) + O(w)@ (the raw call,
-- 2 sub-ops, 1 pseudo-join, and 1 'psplit' call).
psplitOp2R ::
  (1 <= w) =>
  NatRepr w ->
  (Domain w -> Domain w -> Domain w) ->
  Domain w -> Domain w -> Domain w
psplitOp2R w op a b =
  let !raw = op a b
      !subs = [ op a bj | bj <- psplit w b ]
      !pj = case subs of
              []     -> raw           -- unreachable: psplit returns ≥ 1 piece
              (c:cs) -> Prelude.foldr (pseudoJoin w) c cs
  in if size raw <= size pj then raw else pj

-- | The exact result size of @addRaw@\/@subRaw@ on operands with the given step
-- counts and strides, /without/ materializing the result.
--
-- Writing @s = 2^v · μ@ (μ odd), 'addRaw' walks @n' + 1@ values in stride
-- @d = gcd(s_a, s_b)@ (singletons skipped by 'addSubStrideAndSteps'), saturating at
-- the orbit length @2^w / lowestSetBit d@:
--
-- @
-- size = min(n' + 1, 2^w \/ lowestSetBit d),   n' = n_a·(s_a\/d) + n_b·(s_b\/d)
-- @
--
-- The @start'@ of the result (the only thing distinguishing 'addRaw' from
-- 'subRaw') never enters this count, so 'addSubSize' scores /both/ operations
-- and /all/ orientations. The orbit length is itself orientation-invariant
-- (@lowestSetBit@ ignores the odd part that reversal flips); only @n'@ — through
-- the cross-operand @gcd@ of the odd parts — actually moves. See
-- 'addSubSizeCorrect'.
addSubSize ::
  Natural {- ^ @mask = 2^w - 1@ -} ->
  Natural {- ^ @n_a@ -} -> Natural {- ^ @stride a@ -} ->
  Natural {- ^ @n_b@ -} -> Natural {- ^ @stride b@ -} ->
  Natural
addSubSize m na sa nb sb =
  min (n' + 1) (orbitLenOf m (lowestSetBit d))
  where
    (d, n') = addSubStrideAndSteps na sa nb sb

-- | The (≤2) distinct orientation strides of an operand, for scoring with
-- 'addSubSize'. Reversal flips the stride to its modular additive inverse, but
-- leaves the size formula unchanged for degenerate operands:
--
--   * /Singleton/ (@n = 0@): its stride is the dummy @1@, which 'addSubSize'
--     skips anyway, so the orientation is irrelevant.
--   * /Full coset/ (@n + 1 = orbitLen@): 'reverseD' canonicalizes back to the
--     same progression, so there is genuinely only one orientation.
--
-- Otherwise the two orientations @{stride, 2^w − stride}@ are distinct (they
-- coincide only at @stride = 2^{w-1}@, which forces a singleton or full coset),
-- and 'reverseD' leaves the reversed stride uncanonicalized at @2^w − stride@.
strideOrientations :: Domain w -> [Natural]
strideOrientations c
  | n c == 0              = [stride c]
  | n c + 1 == orbitLen c = [stride c]
  | otherwise             = [stride c, modNeg (mask c) (stride c)]

-- | Orientation-robust 'add'\/'sub' (see 'orientRobust' for the rationale).
--
-- Where the generic 'orientRobust' materializes the result at every orientation
-- and takes the cardinality-minimum, this scores each of the (≤4) orientation
-- pairs with the closed-form 'addSubSize' — a couple of scalar gcd\/mults — and
-- materializes the winning orientation /once/. The two agree exactly
-- ('addRobustClosedFormAgrees'), since 'addSubSize' /is/ @size . op@.
--
-- == Examples
--
-- Orientation matters: at @w = 4@, the two-element progressions @{0,6}@ and
-- @{0,10}@ have different cross-operand gcds at the four orientation
-- combinations, because 'reverseD' replaces a stride @s@ with @2^w − s@:
--
-- >>> let a = mk4 0 6 1; b = mk4 0 10 1
-- >>> (stride a, stride (reverseD w4 a))
-- (6,10)
-- >>> (stride b, stride (reverseD w4 b))
-- (10,6)
--
-- The forward gcd is @gcd(6, 10) = 2@ — an 8-step stride-2 walk — but the
-- diagonal pairings give @gcd(6, 6) = 6@ and @gcd(10, 10) = 10@, both yielding
-- a 3-element result. 'orientRobustAddSub' picks the tightest:
--
-- >>> display (add w4 a b)
-- "[*.....*...*.....]  = [10,0,6]"
-- >>> stride (add w4 a b)
-- 6
--
-- And because every orientation denotes the same set, the answer is invariant
-- under reversing either or both operands:
--
-- >>> eq (add w4 a b) (add w4 (reverseD w4 a) b)
-- True
-- >>> eq (add w4 a b) (add w4 a (reverseD w4 b))
-- True
-- >>> eq (add w4 a b) (add w4 (reverseD w4 a) (reverseD w4 b))
-- True
orientRobustAddSub ::
  NatRepr w ->
  -- | 'addRaw' or 'subRaw'
  (Domain w -> Domain w -> Domain w) ->
  Domain w -> Domain w -> Domain w
orientRobustAddSub w op a b =
  op (pick a saBest) (pick b sbBest)
  where
    m = mask a
    (saBest, sbBest) =
      fst $ List.foldl1' minBySize
        [ ((sa, sb), addSubSize m (n a) sa (n b) sb)
        | sa <- strideOrientations a, sb <- strideOrientations b ]
    minBySize x y = if snd x <= snd y then x else y
    -- Materialize only the chosen orientation; 'reverseD' only when it wins.
    pick c s = if s == stride c then c else reverseD w c

scale :: (1 <= w) => NatRepr w -> Integer -> Domain w -> Domain w
scale w k = liftArith1 w (A.scale k)

-- ------------------------------------------------------------------
-- Anchors and corner products
--
-- This section explains the math used in 'mul' and its helpers
-- ('mulCorners', 'mulFromCorners', 'mulCutUS'). The /goal/ of 'mul' is to
-- compute a sound progression — meaning one whose set of values contains
-- every concrete product of an element of @a@ with an element of @b@.
-- The result is itself a coset progression: a finite window into a coset
-- of the subgroup generated by some stride in @ℤ\/2^w@.
--
-- == What we're computing
--
-- Given operands @a = (l1, t1, n_a)@ and @b = (l2, t2, n_b)@ (each a start,
-- stride, and step count), the concrete product set is
--
-- @
--   { (l1 + i·t1) · (l2 + j·t2) mod 2^w | 0 ≤ i ≤ n_a, 0 ≤ j ≤ n_b }
-- @
--
-- We want a progression @(start', d, n')@ whose values cover that set. We
-- find one by computing two things:
--
-- 1. A stride @d@ such that every concrete product equals @start'@ plus
--    a multiple of @d@ mod @2^w@. This is the /coset/ the result lives on.
-- 2. A step count @n'@ that bounds how many @d@-steps separate any
--    concrete product from @start'@.
--
-- Both come from a single algebraic identity:
--
-- @
--   (l1 + i·t1) · (l2 + j·t2)
--     = l1·l2 + i·(t1·l2) + j·(t2·l1) + i·j·(t1·t2)
--       ^^^^^   ^^^^^^^^^   ^^^^^^^^^   ^^^^^^^^^^^
--       anchor   "i-step"    "j-step"   cross-term
-- @
--
-- Reading this as a function of @i@ and @j@:
--
--   * The /anchor/ @l1·l2@ is the product when @i = j = 0@ — the
--     "origin" of the product orbit.
--   * The /i-step/ coefficient @t1·l2@ is how much the product changes
--     when @i@ advances by 1 (with @j@ held constant). Each step of @a@
--     pushes the product by @t1·l2@.
--   * The /j-step/ coefficient @t2·l1@ is symmetric: each step of @b@
--     pushes the product by @t2·l1@.
--   * The /cross-term/ coefficient @t1·t2@ is how much the product
--     changes when /both/ @i@ and @j@ advance by 1 — a second-order
--     bilinear effect that the i-step and j-step alone don't capture.
--
-- Every product is the anchor plus an integer combination of these three
-- coefficients (with multipliers @i@, @j@, @i·j@). The gcd of the three
-- coefficients divides every such combination, so as an integer every
-- product equals the anchor plus a multiple of
-- @gcd(t1·l2, t2·l1, t1·t2)@. Taking that gcd modulo @2^w@ gives @d@.
--
-- == What "corner products" are
--
-- The function @\(x, y) -> x·y@ is bilinear (monotone in each argument
-- separately). So when @x@ ranges over an integer interval @[al, ah]@ and
-- @y@ ranges over @[bl, bh]@, the maximum and minimum of @x·y@ occur at
-- one of the four corners of the rectangle: @al·bl@, @al·bh@, @ah·bl@,
-- @ah·bh@. We call these the /corner products/. Every concrete product
-- lies in @[min(corners), max(corners)]@ as an integer.
--
-- This gives us our first step-count bound. Dividing the range
-- @max(corners) − min(corners)@ by the stride @d@ yields an upper bound
-- on how many @d@-steps separate any product from the @min@ corner —
-- the /arc step bound/ ('arcStepBound').
--
-- The second step-count bound — the /CLP sum/ ('clpStepBound') — comes
-- straight from the algebraic expansion. Walking @i@ from @0@ to @n_a@
-- shifts the product by at most @n_a · |t1·l2|@ in integer magnitude;
-- same for @j@; the cross-term adds @n_a · n_b · |t1·t2|@. Their sum,
-- divided by @d@, bounds the @d@-steps from the anchor. This bound is
-- sound but pessimistic: it adds the worst-case magnitude of each term
-- independently, ignoring that some terms shift in opposing directions
-- and partially cancel.
--
-- 'mulFromCorners' computes both bounds and takes the smaller — sound
-- and at least as tight as either alone.
--
-- == Why anchor choice matters
--
-- The /anchor/ is a chosen pair of integer representatives @(al, bl)@,
-- not unique: shifting either by a multiple of @2^w@ leaves the modular
-- product set unchanged. So both @start b@ and @start b - 2^w@ are valid
-- integer representatives of operand @b@.
--
-- /But/ they give different integer corner products. If @b = {14, 15}@
-- at @w = 4@, the unsigned representative is the integer arc @[14, 15]@,
-- with endpoints of magnitude up to 15. The negative-shifted
-- representative @[-2, -1]@ has endpoints of magnitude up to 2. Since
-- corner products multiply integer endpoints, the second representative
-- gives a much smaller corner-product range and therefore a tighter
-- @arcStepBound@.
--
-- 'zboundsArc' picks whichever shift puts the operand's midpoint closer
-- to zero. (When the operand sits entirely in the lower bitvector half,
-- no shift helps, and 'zboundsArc' returns the unsigned arc unchanged.)
--
-- The shift also subtly changes the /stride/. 'cornerProductStride' uses
-- @gcd(t1·|bl|, t2·|al|, t1·t2)@ — absolute values, since gcd is defined
-- on non-negative integers. Shifting changes @|bl|@, which can change the
-- integer gcd, which can change the modular stride after @mod 2^w@.
-- Different anchors can therefore yield genuinely different coset
-- progressions, not just different representatives of the same one.
--
-- 'mulCorners' enumerates the distinct anchor combinations (unsigned or
-- zbounds for each operand — up to four pairs) and returns the cardinality
-- minimum. 'midUpper' identifies which operands have a non-trivial choice:
-- when an operand's midpoint is in the lower half, unsigned and zbounds
-- coincide, so it has only one candidate.
--
-- == Why we need a second recipe (the "cut")
--
-- 'mulCorners' represents each operand as a single integer arc. When an
-- operand wraps mod @2^w@ — its orbit crosses zero, e.g. @{14, 15, 0, 1}@
-- with integer arc @[14, 17]@ — that arc still describes the same modular
-- set, but corner products with the other operand can blow up: the wrap
-- forces an endpoint near @2^w@ in magnitude, so the corner-product
-- range stretches and @arcStepBound@ becomes loose.
--
-- The /cut/ recipe ('mulCutUS', based on WI §3.2) handles this by
-- splitting each wrapping operand at the unsigned pole into non-wrapping
-- pieces, computing per-piece products with 'mulFromCorners' (which then
-- has small corner-product ranges on each piece), and pseudo-joining the
-- per-piece results. It also intersects an unsigned-anchor and a
-- signed-anchor sub-product per piece, contributing additional precision
-- the single-anchor approach can't reach.
--
-- == Putting it together
--
-- 'mul' dispatches on whether either operand wraps mod @2^w@:
--
--   * /Neither wraps/: 'mulCorners' alone is optimal. 'ssplit' on a
--     non-wrapping operand returns it unchanged, so the cut path reduces
--     to a strict subset of the anchor candidates 'mulCorners' considers.
--     Empirically (w=4) corners is always at least as tight as cut on
--     non-wrap pairs.
--   * /At least one wraps/: 'mulCorners' and 'mulCutUS' are
--     incomparable. We compute both and take the cardinality minimum.

-- | /O(w)/. Multiplication.
--
-- Uses the cheap 'pseudoMeet' and 'pseudoJoin' for the cut + ×_us path. The
-- @leqExact@-aware 'pseudoMeetPrecise'/'pseudoJoinPrecise' make individual
-- sub-products tighter, but 'pseudoJoin' isn't monotone, so feeding tighter
-- inputs through it can produce a /less/ tight aggregate. Empirically at
-- @w = 4@ the @O(w^2)@ variant is incomparable with this @O(w)@ one
-- (sometimes wins, often ties, sometimes loses), and we don't pay the
-- @w@-factor cost for an unreliable improvement.
--
-- Like 'add'\/'sub', 'mul' is orientation-robust ('orientRobust'): the corner
-- products and the cut\'s integer strides both depend on operand orientation,
-- so trying both representatives of each operand and keeping the tightest
-- result is a sound, cheap precision win (see 'mulRobustDominatesRaw').
mul :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mul w = orientRobust w (mulRaw w)

-- | /O(w)/. The single-orientation multiplication kernel (see 'mul' for the
-- orientation-robust wrapper that should be preferred).
mulRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * WI 3.2 Analysing expressions
-- * CLP 4.2 Arithmetic Operations
-- Dispatch: when neither operand wraps mod 2^w, 'mulCorners' alone is optimal
-- (the cut + ×_us recipe collapses to the same answer because 'ssplit' on a
-- non-wrapping operand returns the operand unchanged). When at least one
-- operand wraps, the cut splits it into non-wrapping pieces whose products
-- can be tighter than 'mulCorners'\'s direct anchor enumeration; we then
-- take the cardinality min. Empirically at w=4: corners ≤ cut on 100% of
-- non-wrap pairs (so the dispatch loses no precision), and the cut is
-- strictly tighter on 1.0% of wrap pairs (justifying its cost there).
mulRaw w a b
  | wrapsU a || wrapsU b =
      let !rcorners = mulCorners w a b
          !rcut = mulCutUS pseudoMeet pseudoJoin w a b
      in if size rcorners <= size rcut then rcorners else rcut
  | otherwise = mulCorners w a b

-- Whether the operand's orbit wraps mod @2^w@: @start + n·stride > mask@.
wrapsU :: Domain w -> Bool
wrapsU c = start c + n c * stride c > mask c
{-# INLINE wrapsU #-}

-- Run 'mulFromCorners' at the distinct combinations of unsigned-vs-zbounds
-- integer reps for the two operands and return the smallest result. The
-- choice is driven by 'midUpper': when an operand's midpoint is in the
-- lower bitvector half, 'zboundsArc' returns the same arc as 'unsignedArc',
-- so the U-vs-Z distinction collapses for that operand. The number of
-- distinct candidates is therefore @2^k@ where @k@ is the count of
-- midUpper-true operands.
--
-- Singletons go through 'scaleSingleton' (exact and stride-preserving)
-- since 'mulFromCorners' would still be sound but is wasteful when one
-- operand has no orbit.
mulCorners :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mulCorners w a b
  | n a == 0 = scaleSingleton w (start a) b
  | n b == 0 = scaleSingleton w (start b) a
  | otherwise =
      let !(uAl, uAh) = unsignedArc a
          !(uBl, uBh) = unsignedArc b
          !rUU = mulFromCorners w a b uAl uAh uBl uBh
      in case (midUpper a, midUpper b) of
           (False, False) -> rUU
           (True,  False) ->
             let !(zAl, zAh) = zboundsArc a
                 !rZU = mulFromCorners w a b zAl zAh uBl uBh
             in minBy size rUU rZU
           (False, True ) ->
             let !(zBl, zBh) = zboundsArc b
                 !rUZ = mulFromCorners w a b uAl uAh zBl zBh
             in minBy size rUU rUZ
           (True,  True ) ->
             let !(zAl, zAh) = zboundsArc a
                 !(zBl, zBh) = zboundsArc b
                 !rUZ = mulFromCorners w a b uAl uAh zBl zBh
                 !rZU = mulFromCorners w a b zAl zAh uBl uBh
                 !rZZ = mulFromCorners w a b zAl zAh zBl zBh
             in minBy size (minBy size rUU rUZ) (minBy size rZU rZZ)
  where
    minBy f x y = if f x <= f y then x else y

-- Whether the operand's unsigned arc has its midpoint in the upper bitvector
-- half. When this is False, 'zboundsArc' coincides with 'unsignedArc' (no
-- shift), so the U-vs-Z anchor distinction is a no-op for that operand.
midUpper :: Domain w -> Bool
midUpper c = 2 * start c + n c * stride c > mask c
{-# INLINE midUpper #-}

-- The WI 3.2 cut + ×_us recipe, parameterized over the meet/join helpers
-- used to combine sub-products. 'ssplit' each operand at the unsigned pole,
-- run both an unsigned and a signed product on each pair of pieces,
-- intersect (the intersection is the source of added precision), then
-- pseudo-join the sub-results.
mulCutUS ::
  (1 <= w) =>
  (NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)) ->
  (NatRepr w -> Domain w -> Domain w -> Domain w) ->
  NatRepr w -> Domain w -> Domain w -> Domain w
mulCutUS meetOp joinOp w a b =
  assert (proper a) $
  assert (proper b) $
  case () of
    -- Singleton fast path: @{k} × (s, t, n) = (k·s, k·t, n) mod 2^w@ is exact
    -- (preserving stride), while a cut + ×_us pseudo-join would round it out
    -- through Arith. Roughly all (a, b) pairs where one is a singleton get
    -- strictly worse without this case.
    _ | n a == 0 -> scaleSingleton w (start a) b
      | n b == 0 -> scaleSingleton w (start b) a
      | otherwise ->
          case [ c | u <- cut w a, v <- cut w b, c <- mulNoStraddleUS meetOp w u v ] of
            []     -> mk w 0 1 0  -- unreachable on proper inputs
            (c:cs) -> Prelude.foldr (joinOp w) c cs

-- | /O(w)/. The pole-crossing cut WI 3.2 uses for multiplication. We don't
-- need WI 3.2's full @ssplit ∘ nsplit@ here, just 'ssplit': the @×_s@
-- sub-product handles signed-pole crossings via 'zbounds' style anchoring
-- (treating an arc that crosses the signed pole as a contiguous arc in the
-- negative-signed half), which avoids a cut and the precision lost when
-- pseudo-joining the two signed-pole pieces.
cut :: (1 <= w) => NatRepr w -> Domain w -> [Domain w]
cut w c = ssplit w c

-- The signed-meet-unsigned product on a pair of cut pieces:
-- @u ×_us v = (u ×_u v) ∩ (u ×_s v)@. Returns one domain or none.
mulNoStraddleUS ::
  (1 <= w) =>
  (NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)) ->
  NatRepr w -> Domain w -> Domain w -> [Domain w]
mulNoStraddleUS meetOp w u v =
  case (mulNoStraddleU w u v, mulNoStraddleS w u v) of
    (pu, ps) -> case meetOp w pu ps of
      Nothing -> []
      Just c  -> [c]

-- | /O(w)/. Unsigned product of two cut pieces: treat the pieces as integer
-- intervals on @[0, 2^w)@, multiply with the same coset/step-count formula as
-- 'mul', and saturate to top when the integer extent exceeds @2^w@.
mulNoStraddleU ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mulNoStraddleU w a b =
  let (al, ah) = unsignedArc a
      (bl, bh) = unsignedArc b
  in mulFromCorners w a b al ah bl bh

-- Product of two non-wrap-mod-@2^w@ pieces, using 'zboundsArc' to pick the
-- integer-arc representative whose corners are smallest in magnitude. When
-- a piece's start is in the upper bitvector half, this shifts it into the
-- negative-signed half as a /contiguous/ integer arc — the standard signed
-- interpretation would split such a piece at @smax/smin@ — and the smaller
-- corner magnitudes give 'mulFromCorners' a tighter step-count bound than
-- anchoring at the unsigned start.
mulNoStraddleS ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mulNoStraddleS w a b =
  let (al, ah) = zboundsArc a
      (bl, bh) = zboundsArc b
  in mulFromCorners w a b al ah bl bh

-- The unsigned integer-arc representative of the operand:
-- @[start, start + n·stride]@ (no shift). Always non-negative, but for
-- operands in the upper bitvector half the magnitudes can be near @2^w@.
unsignedArc :: Domain w -> (Integer, Integer)
unsignedArc c =
  assert (proper c) $
  let !lo = toInteger (start c)
      !sz = toInteger (n c) * toInteger (stride c)
  in (lo, lo + sz)

-- Pick a pair of integers whose arc @[lo, lo + n·stride]@ represents the
-- same bitvector progression mod @2^w@ as the operand, but with magnitude
-- closer to zero. The two natural choices are 'unsignedArc' and the
-- @-2^w@-shifted representative @[start - 2^w, start + n·stride - 2^w]@;
-- 'zboundsArc' picks whichever has its midpoint closer to zero.
--
-- 'mulFromCorners' uses @(hi - lo) / dInt@ as one of its step-count
-- bounds, where @hi@, @lo@ are the integer corner products @al·bl@,
-- @al·bh@, etc. That bound is tighter when @|al|@, @|ah|@, @|bl|@, @|bh|@
-- are smaller, because corner products grow with the magnitude of the
-- operand. The midpoint criterion minimises the worst corner magnitude.
--
-- For self-wrapping operands the integer extent is at least @2^w@ either
-- way, so the magnitude-minimising trick doesn't tighten the arc bound
-- meaningfully.
zboundsArc :: Domain w -> (Integer, Integer)
zboundsArc c =
  assert (proper c) $
  let !lo = toInteger (start c)
      !sz = toInteger (n c) * toInteger (stride c)
      !hi = lo + sz  -- integer extent, possibly >= 2^w
      !m  = toInteger (mask c)
  in if 2 * lo + sz > m
       then (lo - (m + 1), hi - (m + 1))
       else (lo, hi)

-- | Compute the coset progression for the integer-arc product @[al, ah] ×
-- [bl, bh]@, given operand strides from @a@ and @b@. Anchors at the integer
-- arc's lo corner.
mulFromCorners ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w ->
  Integer -> Integer -> Integer -> Integer -> Domain w
mulFromCorners w a b al ah bl bh =
  let !(lo, hi) = cornerArc al ah bl bh
      !dIntI = cornerProductStride a b al bl
      !dMod = if dIntI == 0 then 0 else modMask a (fromInteger dIntI)
      !startNat = asN w lo
  in if dMod == 0
       then mk w startNat 1 0
       else
         let !nRaw = Prelude.min (clpStepBound a b al bl dIntI)
                                 (arcStepBound lo hi dIntI)
         in mk w startNat dMod (clampToOrbit (mask a) dMod (fromInteger nRaw))

-- The integer arc enclosing the four corner products
-- @{al·bl, al·bh, ah·bl, ah·bh}@. Every concrete product
-- @(al + i·t1)(bl + j·t2)@ for @0 ≤ i ≤ n_a, 0 ≤ j ≤ n_b@ lies in @[lo, hi]@
-- as an integer (because the bilinear function is monotone in each argument
-- separately, so its extrema lie at corners).
cornerArc :: Integer -> Integer -> Integer -> Integer -> (Integer, Integer)
cornerArc al ah bl bh =
  let !c1 = al * bl
      !c2 = al * bh
      !c3 = ah * bl
      !c4 = ah * bh
  in ( Prelude.min (Prelude.min c1 c2) (Prelude.min c3 c4)
     , Prelude.max (Prelude.max c1 c2) (Prelude.max c3 c4)
     )

-- The integer-valued coset stride for the corner product, anchored at
-- @(al, bl)@. Expanding @(al + i·t1)(bl + j·t2)@ over @0 ≤ i ≤ n_a@,
-- @0 ≤ j ≤ n_b@:
--
--   product − al·bl = i·(t1·bl) + j·(t2·al) + i·j·(t1·t2)
--
-- so every product's offset from the anchor is divisible by
-- @gcd(t1·bl, t2·al, t1·t2)@ as an integer. Singletons (where one operand
-- has @n = 0@) contribute @0@ for the cross-terms involving their stride,
-- since stepping that operand has no effect.
--
-- We use @|al|@, @|bl|@ rather than the raw values; this may inflate the
-- gcd when shifted (negative) anchors are used, which is fine for soundness
-- and necessary for 'arcStepBound' to be sound (it bounds /integer/
-- displacement, not modular).
cornerProductStride ::
  Domain w -> Domain w -> Integer -> Integer -> Integer
cornerProductStride a b al bl =
  let !t1 = toInteger (stride a)
      !t2 = toInteger (stride b)
      !d12 = if n a == 0 then 0 else t1 * Prelude.abs bl
      !d21 = if n b == 0 then 0 else t2 * Prelude.abs al
      !d22 = if n a == 0 || n b == 0 then 0 else t1 * t2
  in Prelude.gcd d12 (Prelude.gcd d21 d22)

-- The CLP-style step-count bound: the sum of per-coefficient maxima.
-- Walking i over @[0, n_a]@ contributes at most @n_a · t1 · |bl|@ integer
-- displacement; same for j, plus the cross-term contributes
-- @n_a · n_b · t1 · t2@. Dividing the total by the coset stride gives an
-- upper bound on the number of stride-d steps any concrete product is from
-- the anchor.
--
-- This bound is anchor-independent in modular arithmetic but uses the
-- integer absolute values of the anchor here, matching
-- 'cornerProductStride'.
clpStepBound ::
  Domain w -> Domain w -> Integer -> Integer -> Integer -> Integer
clpStepBound a b al bl d =
  let !t1 = toInteger (stride a)
      !t2 = toInteger (stride b)
      !na = toInteger (n a)
      !nb = toInteger (n b)
      !d12 = if n a == 0 then 0 else t1 * Prelude.abs bl
      !d21 = if n b == 0 then 0 else t2 * Prelude.abs al
      !d22 = if n a == 0 || n b == 0 then 0 else t1 * t2
  in if d == 0
       then 0
       else na * (d12 `Prelude.div` d) + nb * (d21 `Prelude.div` d)
            + na * nb * (d22 `Prelude.div` d)

-- The integer-arc step-count bound: the integer extent @hi − lo@ divided by
-- the coset stride @d@. Sound because every concrete product lies in
-- @[lo, hi]@ as an integer (see 'cornerArc'), so any such product is at most
-- @(hi − lo)/d@ stride-d steps from @lo@.
arcStepBound :: Integer -> Integer -> Integer -> Integer
arcStepBound lo hi d = if d == 0 then 0 else (hi - lo) `Prelude.div` d

-- @{k} × (s, t, n) = (k·s, k·t, n) mod 2^w@: stride-preserving exact product.
-- The orbit length of the result can be smaller than @c@'s when @k·t mod 2^w@
-- has more low zero bits than @t@ (i.e. @k@ contributes its own factor of 2),
-- so we clamp the step count via 'clampToOrbit'.
scaleSingleton :: (1 <= w) => NatRepr w -> Natural -> Domain w -> Domain w
scaleSingleton w k c =
  assert (proper c) $
  let !s' = modMask c (k * start c)
      !t' = modMask c (k * stride c)
  in if t' == 0
       then mk w s' 1 0  -- @k·t ≡ 0 (mod 2^w)@: every step lands on @k·s@.
       else mk w s' t' (clampToOrbit (mask c) t' (n c))

-- | /O(w)/. Unsigned division.
udiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.2 / Table 3.1 (DIVISION), all-positive row: @(l1,u1,δ1) \/
--   (l2,u2,δ2) ⊆ (l1\/u2, u1\/l2, 1)@.
-- * CLP 3.3.2 (DIVISION by a constant): @(l1,u1,δ1) \/ k = (l1\/k, u1\/k,
--   |δ1\/k|)@ — stride-preserving.
--
-- Implementation: split the dividend with 'ssplit' into non-wrap-mod-@2^w@
-- arcs, convert each piece to its exact arith interval via 'arcArith', divide
-- with 'A.udiv', then union the quotients with 'hullArith'. This stays within
-- the @A.udiv (hull a) (hull b)@ envelope while avoiding a domain 'pseudoJoin'.
-- If the divisor is a single constant @k@ dividing @stride a@, 'udivConst'
-- returns the exact affine quotient instead of collapsing the stride to 1.
udiv w a b =
  assert (proper a) $
  assert (proper b) $
  case udivConst w a b of
    Just r  -> r  -- stride-preserving constant divisor
    Nothing -> hullArith w [ A.udiv (arcArith w ai) bArith | ai <- ssplit w a ]
  where bArith = toArith b

-- Stride-preserving fast path for division by a constant: when @b@ is a single
-- nonzero constant @k@ dividing @stride a@ and @a@ is a single non-wrap arc,
-- the quotient is exactly @(start a \/ k) + i·(stride a \/ k)@.
udivConst :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
udivConst w a b
  | n b == 0 && k /= 0
  , [ai] <- ssplit w a   -- a is a single non-wrap arc
  , n ai > 0 && stride ai `mod` k == 0
  = Just (mk w (start ai `Prelude.div` k) (stride ai `Prelude.div` k) (n ai))
  | otherwise = Nothing
  where k = start b

urem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
urem w = liftArith2 w A.urem

-- | /O(w)/. Signed division.
sdiv :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.2 / Table 3.1 (DIVISION), sign-based case analysis on the
--   endpoints of both operands.
-- * CLP 3.3.2 (DIVISION by a constant): @(l1,u1,δ1) \/ k = (min(l1\/k,u1\/k),
--   max(l1\/k,u1\/k), |δ1\/k|)@ — stride-preserving.
--
-- Implementation: split the dividend at both poles ('signPieces' = 'ssplit'
-- then 'nsplit') into sign-coherent, non-wrap-mod-@2^w@ arcs, convert each
-- piece to its exact arith interval via 'arcArith', divide with 'A.sdiv', then
-- union the quotients with 'hullArith'. This keeps the result within the
-- @A.sdiv (hull a) (hull b)@ envelope without a pole-crossing 'pseudoJoin'
-- that could widen to 'top'. If the divisor is a single constant @k ≠ 0@ with
-- @|k|@ dividing @stride a@, 'sdivConst' returns the exact affine quotient.
sdiv w a b =
  assert (proper a) $
  assert (proper b) $
  case sdivConst w a b of
    Just r  -> r  -- stride-preserving constant divisor
    Nothing -> hullArith w [ A.sdiv w (arcArith w ai) bArith | ai <- signPieces w a ]
  where bArith = toArith b

-- Stride-preserving fast path for signed division by a constant: when @b@ is a
-- single nonzero constant @k@ with @|k|@ dividing @stride a@ and @a@ is a
-- single sign-coherent non-wrap arc, truncated division is affine, so the
-- quotient is exactly @[start a \/ k] + i·(stride a \/ |k|)@. The sign of @k@
-- may reverse the walk, so the result start is the smaller endpoint.
sdivConst :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
sdivConst w a b
  | n b == 0 && k /= 0
  , [ai] <- signPieces w a   -- a is a single sign-coherent non-wrap arc
  , n ai > 0 && stride ai `mod` absK == 0
  = let (aloU, ahiU) = arcUBounds ai
        v0 = toSigned w (toInteger aloU) `quot` k
        vn = toSigned w (toInteger ahiU) `quot` k
    in Just (mk w (asN w (min v0 vn)) (stride ai `Prelude.div` absK) (n ai))
  | otherwise = Nothing
  where
    k    = toSigned w (toInteger (start b))
    absK = integerToNatural (abs k)

-- Split a progression at both poles into sign-coherent, non-wrap-mod-@2^w@
-- pieces: 'ssplit' (south\/unsigned) then 'nsplit' (north\/sign).
signPieces :: (1 <= w) => NatRepr w -> Domain w -> [Domain w]
signPieces w c = concatMap (nsplit w) (ssplit w c)

srem :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
srem w = liftArith2 w (A.srem w)

-- ------------------------------------------------------------------
-- ** Division helpers

-- Is this progression the singleton @{0}@?
isSingletonZero :: Domain w -> Bool
isSingletonZero c = n c == 0 && start c == 0

-- The unsigned arc bounds @(lo, hi)@ of a non-wrap-mod-@2^w@ progression, read
-- directly from @start@ and @end@ (no 'toArith').
-- Precondition: @start + n·stride <= mask@ (e.g. 'ssplit'\/'nsplit' output).
arcUBounds :: Domain w -> (Natural, Natural)
arcUBounds c = (start c, start c + n c * stride c)

-- Build the exact arith interval of a non-wrap-mod-@2^w@ arc, read straight
-- off its @start@\/@end@ via 'A.range'. Unlike 'toArith', this never goes
-- through the lossy 'cosetArc': for a single non-wrapping arc, @[start, end]@
-- is exact. Used to feed dividend pieces into 'A.udiv'\/'A.sdiv'.
arcArith :: (1 <= w) => NatRepr w -> Domain w -> A.Domain w
arcArith w c =
  let (lo, hi) = arcUBounds c
  in A.range w (toInteger lo) (toInteger hi)

-- The strides progression whose orbit contains every element of every arith
-- interval in the list (their bounding hull, converted back via 'fromArith').
-- Empty list yields 'top'. Used to combine the per-dividend-piece quotients
-- from 'A.udiv'\/'A.sdiv' without a domain 'pseudoJoin', which could widen to
-- 'top' across separated pieces.
hullArith :: (1 <= w) => NatRepr w -> [A.Domain w] -> Domain w
hullArith w = \case
  []     -> top w
  (d:ds) -> fromJustUnsafe "hullArith" (fromArith w (List.foldl' A.join d ds))

-- ------------------------------------------------------------------
-- ** Arithmetic (SMT-LIB div-by-zero semantics)

-- | /O(w)/. Unsigned division with SMT-LIB div-by-zero semantics.
udivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- If the divisor may be zero, join the ordinary quotient with the SMT-LIB
-- all-ones result for the zero case.
udivSmtlib w a b
  | isSingletonZero b = mk w (mask a) 1 0            -- divisor exactly {0}: all-ones
  | member b 0        = pseudoJoin w (udiv w a b) (mk w (mask a) 1 0)
  | otherwise         = udiv w a b

uremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
uremSmtlib w = liftArith2 w A.uremSmtlib

-- | /O(w)/. Signed division with SMT-LIB div-by-zero semantics.
sdivSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- If the divisor may be zero, join the ordinary quotient with the sign-based
-- SMT-LIB zero-divisor result.
sdivSmtlib w a b
  | isSingletonZero b = sdivByZeroStrides w a
  | member b 0        = pseudoJoin w (sdiv w a b) (sdivByZeroStrides w a)
  | otherwise         = sdiv w a b

-- The result of @bvsdiv s 0@ as a function of the dividend's sign: all-ones
-- when @s >= 0@, @1@ when @s < 0@. Mirrors 'A.sdivByZero'.
sdivByZeroStrides :: (1 <= w) => NatRepr w -> Domain w -> Domain w
sdivByZeroStrides w a =
  let (al, ah) = A.sbounds w (toArith a)
  in case (al < 0, ah >= 0) of
       (False, _    ) -> mk w (mask a) 1 0            -- s >= 0: all-ones
       (True,  False) -> mk w 1 1 0                   -- s < 0: one
       (True,  True ) -> pseudoJoin w (mk w 1 1 0) (mk w (mask a) 1 0)

sremSmtlib :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
sremSmtlib w = liftArith2 w (A.sremSmtlib w)

-- | The progression whose elements are exactly those of @arith@ that lie in the
-- @g@-coset of @start'@, where @g = lowestSetBit d@. Strictly tighter than
-- the corresponding @liftArith*@ call when @g > 1@, since the stride stays
-- @g@ rather than collapsing to 1. See Note [Product abstraction].
--
-- Currently unused; retained as a building block for an Arith-Strides reduced
-- product.
_arithMeetCoset ::
  (1 <= w) =>
  NatRepr w ->
  -- | The Arith arc to restrict.
  A.Domain w ->
  -- | Result stride @d@: must be positive and at most @2^w - 1@.
  Natural ->
  -- | @start'@: any representative of the target coset.
  Natural ->
  Domain w
_arithMeetCoset w arith d start' =
  assert (d > 0 && d <= m) $
  case A.arithDomainData arith of
    -- Arith is full: result is the full @g@-coset of @start'@. Let 'mk'
    -- canonicalize (it reduces @start@ to its residue mod @g@).
    Nothing -> mk w start' d (orbitLenOf m g - 1)
    Just (lo, sz) ->
      let lo'    = fromInteger lo
          sz'    = fromInteger sz
          clpLo  = firstCosetMember m lo' g start'
          off    = modSub m clpLo lo'
          nSteps = divByPow2 (sz' - off) g
      in mk w clpLo g nSteps
  where
    m = integerToNatural (maxUnsigned w)
    g = lowestSetBit d

-- ------------------------------------------------------------------
-- * Bitwise operations

-- ------------------------------------------------------------------
-- ** Internal helpers

-- | /O(w)/. Sound unsigned @[lo, hi]@ range of an operand's orbit, suitable
-- as input to interval-based bitwise bound algorithms (e.g. 'warrenAndLo').
--
--   * Non-wrap, non-self-wrap: @[start, end]@.
--   * Wrap (orbit straddles 0, but not self-wrap): with @k = (mask - start)
--     `div` stride@ the largest pre-wrap index, the orbit splits into a
--     pre-wrap arc capped at @start + k * stride@ and a post-wrap arc whose
--     least member is @start + (k + 1) * stride - (mask + 1)@. Both endpoints
--     are actual orbit members, so this is the tightest single-interval cover.
--     (A span of exactly @mask@ wraps at most once, so it lands here, not in
--     the self-wrap case — self-wrap requires @span > mask@, matching
--     'isSelfWrapping'.)
--   * Self-wrap: the coset arc @[start mod g, mask - g + 1 + start mod g]@.
operandRange :: Domain w -> (Natural, Natural)
operandRange c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  let !span_ = nn * t
      !lo = s `Prelude.mod` strideGcd c
  in if span_ > m then (lo, m - (strideGcd c - 1) + lo)   -- self-wrap
     else if s + span_ > m then                           -- wrap (not self)
       let !k = (m - s) `Prelude.div` t
           !preMax = s + k * t
           !postMin = s + (k + 1) * t - (m + 1)
       in (postMin, preMax)
     else (s, s + span_)                                  -- no wrap

-- | /O(w^2)/. Tight unsigned lower bound on @{ x .&. y | alo <= x <= ahi,
-- blo <= y <= bhi }@.
--
-- /Hacker's Delight/ §4.3, minAND. Walks @w@ bit positions MSB to LSB,
-- doing /O(w)/ Natural ops per iteration (shifts, masks, comparisons).
warrenAndLo ::
  Natural {- ^ @mask@ -} ->
  Natural {- ^ @alo@ -} ->
  Natural {- ^ @ahi@ -} ->
  Natural {- ^ @blo@ -} ->
  Natural {- ^ @bhi@ -} ->
  Natural
warrenAndLo m alo ahi blo bhi =
  uncurry (Bits..&.) (go alo blo (popCount m - 1))
  where
    notN x = m - x  -- @~x@ at the operand's width.
    go !a !b !i
      | i < 0 = (a, b)
      | otherwise =
          let !bit_ = 1 `shiftL` i
              !aPrime = (a Bits..|. bit_) Bits..&. notN (bit_ - 1)
              !bPrime = (b Bits..|. bit_) Bits..&. notN (bit_ - 1)
              !canFlip = (notN a Bits..&. notN b Bits..&. bit_) /= 0
          in if canFlip && aPrime <= ahi then go aPrime b (i - 1)
             else if canFlip && bPrime <= bhi then go a bPrime (i - 1)
             else go a b (i - 1)

-- | /O(w^2)/. Tight unsigned upper bound on @{ x .&. y | alo <= x <= ahi,
-- blo <= y <= bhi }@.
--
-- /Hacker's Delight/ §4.3, maxAND. Walks @w@ bit positions MSB to LSB,
-- doing /O(w)/ Natural ops per iteration (shifts, masks, comparisons).
warrenAndHi ::
  Natural {- ^ @mask@ -} ->
  Natural {- ^ @alo@ -} ->
  Natural {- ^ @ahi@ -} ->
  Natural {- ^ @blo@ -} ->
  Natural {- ^ @bhi@ -} ->
  Natural
warrenAndHi m alo ahi blo bhi =
  uncurry (Bits..&.) (go ahi bhi (popCount m - 1))
  where
    notN x = m - x
    go !a !b !i
      | i < 0 = (a, b)
      | otherwise =
          let !bit_ = 1 `shiftL` i
              !aPrime = (a Bits..&. notN bit_) Bits..|. (bit_ - 1)
              !bPrime = (b Bits..&. notN bit_) Bits..|. (bit_ - 1)
          in if (a Bits..&. notN b Bits..&. bit_) /= 0 && aPrime >= alo
             then go aPrime b (i - 1)
             else if (notN a Bits..&. b Bits..&. bit_) /= 0 && bPrime >= blo
                  then go a bPrime (i - 1)
                  else go a b (i - 1)

-- ------------------------------------------------------------------
-- ** Definitions

-- | /O(w)/. Bitwise complement.
--
-- == Examples
--
-- Flipping all bits in each even value gives the odds (stride is preserved):
--
-- >>> let evens = mk4 0 2 7
-- >>> display evens
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
-- >>> display (not w4 evens)
-- "[.*.*.*.*.*.*.*.*]  = [1,3,5,7,9,11,13,15]"
not :: (1 <= w) => NatRepr w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.4, BITWISE COMPLEMENT.
--
-- Stride and step count are preserved; the orbit reverses, so the new @start@
-- is the bitwise complement of the old @end@. Exact.
not w c@Domain{stride, n = nn, mask} =
  assert (proper c) $
  mk w (mask - end c) stride nn

-- | /O(w)/. The cheap bitwise-AND kernel: a single arithmetic pass, no parity
-- splitting or Warren bounds. See 'and' for the default ('psplitOp2'-wrapped)
-- variant and 'andPrecise' for the tightest one.
--
-- == Examples
--
-- AND of evens with evens stays in the evens coset (the stride-2 alignment is
-- preserved):
--
-- >>> let evens = mk4 0 2 7
-- >>> display evens
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
-- >>> display (andFast w4 evens evens)
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
--
-- ANDing with the singleton @{12} = 1100@ clears the low two bits of every
-- even, yielding the exact stride-4 result @{0,4,8,12}@:
--
-- >>> display (andFast w4 (mk4 12 1 0) evens)
-- "[*...*...*...*...]  = [0,4,8,12]"
andFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.4 Bit Operations, CLP-CLP @&@ case.
--
-- Per-bit AND rule: bit @k@ of @x .&. y@ is forced to @0@ if bit @k@ is
-- forced to @0@ in /either/ operand; forced to @1@ if bit @k@ is forced to
-- @1@ in /both/; otherwise free. 'fromForcedBits' turns that picture into a
-- progression, intersected with the interval bound @min(hi a, hi b)@ from
-- 'operandRange' (sound since @x & y ≤ min(x, y)@). 'orFast' inherits this
-- rule via De Morgan: @x | y = ~(~x & ~y)@, and complementing an operand
-- swaps its zeros\/ones forced-bits halves. (See 'andPrecise' for the
-- Warren-bounds variant.)
--
-- When either operand is a singleton @{k}@, 'andSingleton' is much tighter —
-- masking by the constant @k@ both fixes the result bits where @k@ is @0@ and
-- can widen the stride — so we special-case it.
andFast w a b =
  assert (proper a) $
  assert (proper b) $
  case (n a, n b) of
    (0, _) -> andSingleton w (start a) b
    (_, 0) -> andSingleton w (start b) a
    _ ->
      let !(za, oa) = forcedBits a
          !(zb, ob) = forcedBits b
          !(_, aHi) = operandRange a
          !(_, bHi) = operandRange b
      in fromForcedBits w (za Bits..|. zb, oa Bits..&. ob) (0, min aHi bHi)

-- | /O(w)/. Bitwise AND. Wraps 'andFast' through 'psplitOp2': each 'psplit'
-- piece of an operand has one more fixed low bit than the operand itself, so
-- running 'andFast' on each pair of pieces and pseudo-joining can be tighter
-- than the single 'andFast' call. The min-by-size guard inside 'psplitOp2'
-- keeps the raw call's result whenever it is at least as tight, so 'and' is
-- never larger than 'andFast' by cardinality. See 'andPrecise' for the
-- variant that also uses Warren bounds.
and :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
and w = psplitOp2 w (andFast w)

-- | /O(w)/. Bitwise AND of a singleton @{k}@ with an arbitrary progression
-- @c@. Sound (over-approximating), and tighter than the generic 'andFast' path.
--
-- Not exact in general: @{ k & y | y ∈ c }@ need not be a single progression.
-- For example at width 4, @{14} & {0,1,2,5,6,7,11,12,13}@ is @{0,2,4,6,10,12}@,
-- which this returns as the cover @{0,2,4,6,8,10,12}@ (the spurious @8@ comes
-- from forcing the result into one arithmetic progression).
andSingleton :: (1 <= w) => NatRepr w -> Natural -> Domain w -> Domain w
-- The result's forced-bit picture is @(~k | zeros, k & ones)@ — a bit is
-- cleared wherever @k@ is @0@ or @c@ forces a @0@, set wherever @k@ is @1@
-- and @c@ forces a @1@, and free only where @k@ is @1@ and @c@\'s bit is
-- free. 'fromForcedBits' turns that into a progression, intersected with
-- the interval bound @hi c@ from 'operandRange' (sound since @k & y ≤ y@).
andSingleton w k c =
  assert (proper c) $
  let !m              = mask c
      !(zeros, ones)  = forcedBits c
      !zeros'         = (m `Bits.xor` k) Bits..|. zeros
      !ones'          = k Bits..&. ones
      !(_, cHi)       = operandRange c
  in fromForcedBits w (zeros', ones') (0, cHi)

-- | /O(w^2)/. Bitwise AND. At least as precise as 'and' on all inputs.
--
-- Wraps 'andPreciseRaw' through 'psplitOp2': each 'psplit' piece of an operand
-- has one more fixed low bit than the operand itself (writing
-- @stride = 2^v · m@, bit @v@ alternates with index parity), and AND
-- distributes over union, so running 'andPreciseRaw' on each pair of pieces
-- and pseudo-joining can be tighter than the single 'andPreciseRaw' call on
-- the unsplit operands.
andPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
andPrecise w = psplitOp2 w (andPreciseRaw w)

-- | /O(w^2)/. The single-progression-pair AND kernel; see 'andPrecise' for
-- the 'psplitOp2' wrapper that should be preferred.
andPreciseRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- The Warren interval bounds and the forced-bits bounds inside
-- 'fromForcedBits' are incomparable (Warren is tight for the interval
-- covers from 'operandRange' but blind to coset structure; forced bits see
-- the coset but not the arc), so feeding the Warren bounds through
-- 'fromForcedBits' takes the tighter of each.
andPreciseRaw w a b =
  assert (proper a) $
  assert (proper b) $
  case (n a, n b) of
    -- 'andSingleton' is at least as tight as the Warren-bounds path here too.
    (0, _) -> andSingleton w (start a) b
    (_, 0) -> andSingleton w (start b) a
    _ ->
      let !m = mask a
          !(za, oa) = forcedBits a
          !(zb, ob) = forcedBits b
          !(aLo, aHi) = operandRange a
          !(bLo, bHi) = operandRange b
          !wLo = warrenAndLo m aLo aHi bLo bHi
          !wHi = warrenAndHi m aLo aHi bLo bHi
      in fromForcedBits w (za Bits..|. zb, oa Bits..&. ob) (wLo, wHi)

-- | /O(w)/. The cheap bitwise-OR kernel (De Morgan over 'andFast'). See 'or'
-- for the default ('psplitOp2'-wrapped) variant and 'orPrecise' for the
-- tightest one.
orFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
orFast w a b = not w (andFast w (not w a) (not w b))

-- | /O(w)/. Bitwise OR (De Morgan over 'and'). At least as precise as 'orFast'
-- by cardinality. See 'orPrecise' for the variant that also uses Warren bounds.
or :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
or w a b = not w (and w (not w a) (not w b))

-- | /O(w^2)/. Bitwise OR. At least as precise as 'or' on all inputs.
orPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
orPrecise w a b = not w (andPrecise w (not w a) (not w b))

-- | /O(w)/. The cheap bitwise-XOR kernel: a single 'forcedBits'-driven pass.
-- See 'xor' for the default variant.
--
-- == Examples
--
-- XOR of evens with evens stays in the evens coset (low bit pinned to 0):
--
-- >>> let evens = mk4 0 2 7
-- >>> display (xorFast w4 evens evens)
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
xorFast :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- Per-bit XOR rule on 'forcedBits' @(zeros, ones)@:
--
--   * forced to @0@ if both operands force the bit to the same value
--     (@(za .&. zb) | (oa .&. ob)@);
--   * forced to @1@ if the operands force the bit to different values
--     (@(za .&. ob) | (oa .&. zb)@);
--   * otherwise free (free in /either/ operand → free in XOR).
--
-- Equivalently, a bit is forced in @x XOR y@ iff it is forced in /both/
-- operands. The result stride is @2^k@ for the lowest free bit @k@; if every
-- bit is forced, the result is the singleton @forcedOnes@.
--
-- The result's forced-bit picture feeds 'fromForcedBits' (with the trivial
-- interval @[0, m]@ — XOR has no useful monotone interval bound). This
-- matches what @liftBitwise2 B.xor@ would derive, but writing the kernel
-- directly lets 'xor' wrap it through 'psplitOp2' for the same precision
-- boost @and@\/@or@ get.
xorFast w a b =
  assert (proper a) $
  assert (proper b) $
  let !m              = mask a
      !(za, oa)       = forcedBits a
      !(zb, ob)       = forcedBits b
      !forcedZeros    = (za Bits..&. zb) Bits..|. (oa Bits..&. ob)
      !forcedOnes     = (za Bits..&. ob) Bits..|. (oa Bits..&. zb)
  in fromForcedBits w (forcedZeros, forcedOnes) (0, m)

-- | /O(w)/. Bitwise XOR. At least as tight (by cardinality) as both the
-- 'psplitOp2'-wrapped 'xorFast' kernel and the De Morgan identity
-- composition @(a | b) & ~(a & b)@.
xor :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- Takes the cardinality-min of two sound candidates:
--
--   * 'xorFast' wrapped through 'psplitOp2' (each 'psplit' piece pins one
--     more low bit than its operand, so XOR-ing the pieces and
--     pseudo-joining can be tighter than the single 'xorFast' call), and
--   * the identity composition over 'andFast'\/'orFast', whose intermediate
--     progressions pick up 'operandRange' interval bounds that the direct
--     forced-bits kernel cannot see (XOR has no monotone interval bound of
--     its own).
--
-- The two candidates are incomparable (each wins on some inputs).
xor w a b =
  let !direct = psplitOp2 w (xorFast w) a b
      !comp = andFast w (orFast w a b) (not w (andFast w a b))
  in if size direct <= size comp then direct else comp

-- ------------------------------------------------------------------
-- * Concatenation, extension, selection, and truncation

-- | Choose between the arith-arc progression and its 'fromForcedBits'
-- refinement for a width-changing conversion.
--
-- The bits candidate is built from the arith result's own 'A.ubounds', so
-- when the arith arc does not wrap modulo the target width those bounds
-- are exactly its endpoints and 'fromForcedBits' can only shrink the arc
-- (the stride is at least 1 and both ends are clamped inward) — the
-- refinement is returned outright. When the arc wraps, 'A.ubounds' hulls
-- to the full range, leaving the two candidates incomparable, and only
-- then is the cardinality comparison needed.
refineConversion ::
  -- | arith-arc progression (via 'fromArith', always stride 1)
  Domain w ->
  -- | 'fromForcedBits' refinement at the arith arc's 'A.ubounds'
  Domain w ->
  Domain w
refineConversion arith bits
  | wrapsU arith = if size bits <= size arith then bits else arith
  | otherwise = bits

-- | /O(w)/. Zero extension.
zext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
-- A non-wrapping orbit is /exact/: its values are plain integers below
-- @2^w@, so the same @(start, stride, n)@ denotes the same set at width
-- @u@. Otherwise, the 'toArith' detour alone would drop all coset
-- structure (zext of the evens would forget evenness), so take the
-- cardinality-min with 'fromForcedBits' at @c@\'s forced bits (the new
-- high bits forced to @0@) and the arith result's 'A.ubounds'.
zext _w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof
      | start c + n c * stride c <= mask c ->
          mk u (start c) (stride c) (n c)
      | otherwise ->
          let !arithD = A.zext (toArith c) u
              !arith = fromJustUnsafe "zext" (fromArith u arithD)
              !mU = integerToNatural (maxUnsigned u)
              !topBits = mU `Bits.xor` mask c
              !(zeros, ones) = forcedBits c
              !(loI, hiI) = A.ubounds arithD
              !bits = fromForcedBits u (zeros Bits..|. topBits, ones)
                        (integerToNatural loI, integerToNatural hiI)
          in refineConversion arith bits

-- | /O(w)/. Sign extension.
sext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Domain u
-- A non-wrapping orbit confined to one sign half is /exact/: non-negative
-- values are unchanged by sign extension, and all-negative values shift
-- uniformly by the sign-extension offset @2^u - 2^w@ (cf. 'ashrRaw'\'s
-- all-negative case). Otherwise, refine the arith result with
-- 'fromForcedBits': the new high bits copy bit @w - 1@, so they are
-- forced (to the corresponding half of the pair) exactly when the sign
-- bit is forced in @c@.
sext w c u =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof
      | arcNoWrap, endC < halfW ->
          mk u (start c) (stride c) (n c)
      | arcNoWrap, start c >= halfW ->
          mk u (start c + (mU - mW)) (stride c) (n c)
      | otherwise ->
          let !arithD = A.sext w (toArith c) u
              !arith = fromJustUnsafe "sext" (fromArith u arithD)
              !topBits = mU `Bits.xor` mW
              !(zeros, ones) = forcedBits c
              !zerosU = zeros Bits..|.
                          (if zeros Bits..&. halfW /= 0 then topBits else 0)
              !onesU = ones Bits..|.
                         (if ones Bits..&. halfW /= 0 then topBits else 0)
              !(loI, hiI) = A.ubounds arithD
              !bits = fromForcedBits u (zerosU, onesU)
                        (integerToNatural loI, integerToNatural hiI)
          in refineConversion arith bits
  where
    mW = mask c
    mU = integerToNatural (maxUnsigned u)
    halfW = (mW + 1) `Bits.shiftR` 1  -- 2^(w-1), the sign bit
    endC = start c + n c * stride c
    arcNoWrap = endC <= mW

-- | /O(u + v)/. Concatenation: @a@ supplies the high @u@ bits, @b@ the low
-- @v@ bits.
concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> NatRepr v -> Domain v -> Domain (u + v)
-- Both operands' forced-bit pictures compose bit-parallel: the result has
-- forced pair @(zeros_a << v .|. zeros_b, ones_a << v .|. ones_b)@. Take
-- the cardinality-min of 'fromForcedBits' on that pair (at the arith
-- result's 'A.ubounds') with the arith-only result.
concat u a v b =
  case NR.leqAddPos u v of
    LeqProof ->
      let !uv = NR.addNat u v
          !arithD = A.concat u (toArith a) v (toArith b)
          !arith = fromJustUnsafe "concat" (fromArith uv arithD)
          !vI = NR.widthVal v
          !(za, oa) = forcedBits a
          !(zb, ob) = forcedBits b
          !(loI, hiI) = A.ubounds arithD
          !bits = fromForcedBits uv
                    ((za `Bits.shiftL` vI) Bits..|. zb,
                     (oa `Bits.shiftL` vI) Bits..|. ob)
                    (integerToNatural loI, integerToNatural hiI)
      in refineConversion arith bits

-- | /O(w)/. Bit slice: the @n@ bits of the operand starting at bit @i@
-- (counting from the least significant bit).
select ::
  forall i n w.
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Domain n
-- Bit @p@ of the result is bit @p + i@ of the operand, so the result's
-- forced pair is the slice @(zeros >> i, ones >> i)@ masked to @n@ bits.
-- Refining the arith result with 'fromForcedBits' recovers e.g.
-- @select 0 2@ of the evens as @{0, 2}@ instead of all of @[0, 3]@.
select i n _w c =
  let !arithD = A.select i n (toArith c)
      !arith = fromJustUnsafe "select" (fromArith n arithD)
      !mN = integerToNatural (maxUnsigned n)
      !iI = NR.widthVal i
      !(zeros, ones) = forcedBits c
      !(loI, hiI) = A.ubounds arithD
      !bits = fromForcedBits n
                ((zeros `Bits.shiftR` iI) Bits..&. mN,
                 (ones `Bits.shiftR` iI) Bits..&. mN)
                (integerToNatural loI, integerToNatural hiI)
  in refineConversion arith bits

-- ------------------------------------------------------------------
-- * Shifts and rotations

-- | /O(w)/. Left shift.
--
-- == Examples
--
-- Shifting @{1,2}@ left by @{1,2}@ yields @{2,4,6,8}@ (stride
-- @gcd(1, 1) · 2^1 = 2@ is preserved across the range of shift amounts):
--
-- >>> let a = mk4 1 1 1; b = mk4 1 1 1
-- >>> display a
-- "[.**.............]  = [1,2]"
-- >>> display b
-- "[.**.............]  = [1,2]"
-- >>> display (shl w4 a b)
-- "[..*.*.*.*.......]  = [2,4,6,8]"
shl :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
shl w = psplitOp2R w (shlRaw w)

-- | /O(w)/. The single-pair shift-left kernel; see 'shl' for the
-- 'psplitOp2R'-wrapped variant.
shlRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.3 Shift Operations:
--
--     (l1, u1, δ1) << (l2, u2, δ2) =
--       (min(l1 << l2, l1 << u2),
--        max(u1 << l2, u1 << u2),
--        gcd(|l1|, δ1) << l2)
--
-- Implemented as @mul a c@, where @c@ over-approximates
-- @{ 2^k mod 2^w | k ∈ b }@ by the progression
-- @(2^l_b, 2^l_b, 2^(u_b - l_b) - 1)@ (i.e., @{2^l_b, 2·2^l_b, ..., 2^u_b}@).
-- 'mul' then yields:
--
--   * start  = l_a · 2^l_b mod 2^w                — matches paper's @l1 << l2@
--   * stride = gcd(l_a, δ_a) · 2^l_b mod 2^w      — matches paper's @gcd(|l1|, δ1) << l2@
--   * n      = the paper's step count
--
-- (Algebra: @mul@'s @gcd(t1·l_c, l_a·t_c, t1·t_c) = 2^l_b · gcd(l_a, t_a)@,
-- and its span unfolds to the same closed form the paper gives.)
--
-- Shift counts ≥ @w@ produce 0, so we cap @l_b'@ and @u_b'@ at @w@. When
-- @l_b' = w@, every result is 0, so we shortcut to @{0}@.
--
-- 'mul' is sound w.r.t. the concrete shl semantics, but its closed-form
-- @n'@ for non-singleton @b@ can land in a coset that extends past
-- @A.shl@'s arc, leaving 'mul' incomparable with @A.shl@. Both candidates
-- are sound, so we keep whichever is tighter by cardinality (which agrees
-- with the old 'leqExact' gate whenever 'mul' was contained in the arith
-- arc, and additionally keeps 'mul' when it is smaller but incomparable).
shlRaw w a b
  | l_b' == wInt = mk w 0 1 0
  | size mulResult <= size arithResult = mulResult
  | otherwise = arithResult
  where
    wInt = NR.intValue w
    (l_b, u_b) = A.ubounds (toArith b)
    l_b' = min l_b wInt
    u_b' = min u_b wInt
    cStride = (1 :: Natural) `shiftL` fromInteger l_b'
    cN      = ((1 :: Natural) `shiftL` fromInteger (u_b' - l_b')) - 1
    c       = mk w cStride cStride cN
    mulResult   = mul w a c
    arithResult = liftArith2 w (A.shl w) a b

-- | /O(w)/. Logical right shift.
--
-- == Examples
--
-- A singleton shift preserves the stride; a non-singleton shift falls back
-- to stride 1:
--
-- >>> let a = mk4 4 1 3; b = mk4 1 1 0
-- >>> display a
-- "[....****........]  = [4,5,6,7]"
-- >>> display b
-- "[.*..............]  = [1]"
-- >>> display (lshr w4 a b)
-- "[..**............]  = [2,3]"
--
-- With a non-singleton shift @{1,2}@, the result widens to stride 1:
--
-- >>> let b2 = mk4 1 1 1
-- >>> display b2
-- "[.**.............]  = [1,2]"
-- >>> display (lshr w4 a b2)
-- "[.***............]  = [1,2,3]"
lshr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
lshr w = psplitOp2R w (lshrRaw w)

-- | /O(w)/. The single-pair logical-right-shift kernel; see 'lshr' for the
-- 'psplitOp2R'-wrapped variant.
lshrRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.3 Shift Operations, Table 3.2 (@s(l1) = +, s(u1) = +@):
--
--     (l1, u1, δ1) >>u (l2, u2, δ2) = (l1 >>u u2, u1 >>u l2, 1)
--
-- For a singleton shift @b = {k}@ with @k ≤ ctz(stride a)@ and an arc that
-- doesn't wrap mod @2^w@: write @stride a = 2^v · m@ (m odd) and decompose
-- each @x = (q + i·m)·2^v + c@ where @c = start a mod 2^v@. For @k ≤ v@,
-- @c >> k@ is constant in @i@, so @x >> k = (start a >> k) + i·(stride a >> k)@
-- — a clean progression with stride @stride a >> k@. (Note this works for any
-- @start a@; the bottom @v@ bits of start are preserved into the result, so
-- we don't need @ctz(start a) ≥ k@.)
--
-- For other singleton shifts @{k}@ (with @k > ctz(stride a)@ or a wrapping
-- arc), the result still inherits @a@\'s 'forcedBits' shifted right by @k@
-- (bit @p@ of @x >> k@ is bit @p + k@ of @x@, and the top @k@ bits are @0@):
-- the lowest free bit of the shifted picture gives a result stride, the
-- forced ones a congruent lower bound, and the forced-zeros complement an
-- upper bound, all intersected with the Table 3.2 arc @[lo, hi]@.
--
-- For non-singleton @b@, different @k ∈ b@ give different shifted strides
-- @stride a >> k@, and the union of those progressions is generally not a
-- single CLP, so we fall back to Table 3.2's stride-1 bounds.
lshrRaw w a b
  | n b == 0
  , kI <= ctzStride
  , kI == 0 || arcNoWrap
  = mk w (start a `Bits.shiftR` kI)
         (stride a `Bits.shiftR` kI) (n a)
  | n b == 0 =
      let !m = mask a
          !(zeros, ones) = forcedBits a
          !zeros' = (zeros `Bits.shiftR` kI)
                      Bits..|. (m `Bits.xor` (m `Bits.shiftR` kI))
          !ones' = ones `Bits.shiftR` kI
      in fromForcedBits w (zeros', ones') (lo, hi)
  | otherwise = mk w lo 1 (hi - lo)
  where
    wInt = NR.intValue w
    kI = fromInteger (min (toInteger (start b)) wInt) :: Int
    ctzStride = countTrailingZerosOr0 (toInteger (stride a))
    arcNoWrap = start a + n a * stride a <= mask a
    (l_a, u_a) = A.ubounds (toArith a)
    (l_b, u_b) = A.ubounds (toArith b)
    l_b' = fromInteger (min l_b wInt) :: Int
    u_b' = fromInteger (min u_b wInt) :: Int
    lo = fromInteger (l_a `Bits.shiftR` u_b')
    hi = fromInteger (u_a `Bits.shiftR` l_b')

-- | /O(w)/. Arithmetic right shift.
ashr :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ashr w = psplitOp2R w (ashrRaw w)

-- | /O(w)/. The single-pair arithmetic-right-shift kernel; see 'ashr' for
-- the 'psplitOp2R'-wrapped variant.
ashrRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
-- References:
--
-- * CLP 3.3.3 Shift Operations, Table 3.2 (sign-based case analysis):
--
--     s(l1) = -, s(u1) = -:  (l1 >>s l2, u1 >>s u2, 1)
--     s(l1) = -, s(u1) = +:  (l1 >>s l2, u1 >>s l2, 1)
--     s(l1) = +, s(u1) = +:  (l1 >>s u2, u1 >>s l2, 1)
--
-- (The @s(l1) = +, s(u1) = -@ case cannot occur for a linearly-ordered range.)
--
-- Same singleton-shift stride preservation as 'lshr', plus a sign-half check:
-- positive orbits behave like 'lshr'; negative orbits get the sign-extension
-- offset @2^w - 2^(w-k)@ added (top @k@ bits of every result are 1).
--
-- For other singleton shifts @{k}@, the result inherits @a@\'s 'forcedBits'
-- shifted right by @k@ with the top @k@ result bits copying @a@\'s sign bit
-- when that bit is itself forced; 'fromForcedBitsSigned' intersects that
-- picture with the Table 3.2 arc @[lo, hi]@ on the signed number line.
ashrRaw w a b
  | n b == 0 && kI == 0 = a
  | n b == 0
  , kI <= ctzStride
  , arcNoWrap
  , allPositive
  = mk w (start a `Bits.shiftR` kI)
         (stride a `Bits.shiftR` kI) (n a)
  | n b == 0
  , kI <= ctzStride
  , arcNoWrap
  , allNegative
  = let off    = (mask a + 1) - (1 `shiftL` (wIntI - kI))  -- 2^w - 2^(w-k)
        start' = (start a `Bits.shiftR` kI) + off
    in mk w start' (stride a `Bits.shiftR` kI) (n a)
  | n b == 0 =
      let !m = mask a
          !(zeros, ones) = forcedBits a
          !topK = m `Bits.xor` (m `Bits.shiftR` kI)
          !zeros' = (zeros `Bits.shiftR` kI)
                      Bits..|. (if zeros Bits..&. halfRange /= 0 then topK else 0)
          !ones' = (ones `Bits.shiftR` kI)
                      Bits..|. (if ones Bits..&. halfRange /= 0 then topK else 0)
      in fromForcedBitsSigned w (zeros', ones') (lo, hi)
  | otherwise = mk w (asN w lo) 1 (asN w (hi - lo))
  where
    wInt = NR.intValue w
    wIntI = fromInteger wInt :: Int
    kI = fromInteger (min (toInteger (start b)) wInt) :: Int
    ctzStride = countTrailingZerosOr0 (toInteger (stride a))
    arcNoWrap = start a + n a * stride a <= mask a
    halfRange = (mask a + 1) `Prelude.div` 2  -- 2^(w-1)
    endA = start a + n a * stride a  -- meaningful only when arcNoWrap
    allPositive = endA < halfRange
    allNegative = start a >= halfRange
    (l_a, u_a) = A.sbounds w (toArith a)
    (l_b, u_b) = A.ubounds (toArith b)
    l_b' = fromInteger (min l_b wInt) :: Int
    u_b' = fromInteger (min u_b wInt) :: Int
    lo = l_a `Bits.shiftR` (if l_a < 0 then l_b' else u_b')
    hi = u_a `Bits.shiftR` (if u_a < 0 then u_b' else l_b')

rol :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rol w = psplitOp2 w (rolRaw w)

-- | /O(w log w)/. The single-pair rotate-left kernel; see 'rol' for the
-- 'psplitOp2'-wrapped variant.
rolRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rolRaw w = liftBitwise2 w (B.rolAbstract w)

ror :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
ror w = psplitOp2 w (rorRaw w)

-- | /O(w log w)/. The single-pair rotate-right kernel; see 'ror' for the
-- 'psplitOp2'-wrapped variant.
rorRaw :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
rorRaw w = liftBitwise2 w (B.rorAbstract w)

-- ------------------------------------------------------------------
-- * Lattice operations

-- $lattice
--
-- As established in the /Signedness-agnostic/ paper, no wrapping interval
-- domain can be a meet-semilattice (resp. join-).
--
-- A true lattice meet ⊓ (resp. join ⊔) on the partial order ⊑ induced by
-- 'leqExact' would satisfy:
--
-- [Soundness] @∀ a b x. x ∈ γ(a) ∧ x ∈ γ(b) ⇒ x ∈ γ(a ⊓ b)@
-- (resp. @x ∈ γ(a) ∨ x ∈ γ(b) ⇒ x ∈ γ(a ⊔ b)@).
--
-- [Idempotence] @∀ a. a ⊓ a = a@ (resp. @a ⊔ a = a@).
--
-- [Commutativity] @∀ a b. a ⊓ b = b ⊓ a@ (resp. @a ⊔ b = b ⊔ a@).
--
-- [Lower bound] @∀ a b. a ⊓ b ⊑ a ∧ a ⊓ b ⊑ b@ or
-- [Upper bound] @a ⊑ a ⊔ b ∧ b ⊑ a ⊔ b@.
--
-- [Associativity] @∀ a b c. (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c)@ (resp. ⊔).
--
-- [Monotonicity] @∀ a b c. a ⊑ b ⇒ a ⊓ c ⊑ b ⊓ c@ (resp. ⊔).
--
-- [Top identity / annihilator] @∀ a. a ⊓ ⊤ = a@ (resp. @a ⊔ ⊤ = ⊤@).
--
-- [Absorption] @∀ a b. a ⊓ (a ⊔ b) = a@ and @a ⊔ (a ⊓ b) = a@.
--
-- This module exports five pseudo-meet\/join operators sitting at different
-- points in the precision\/structure trade-off. The tables below summarize
-- which lattice axioms each one satisfies (y), fails (n), or satisfies only
-- under a side condition (~).
--
-- /Meets:/
--
-- @
--                          pseudoMeet  exactMeet  lowerBound
-- Soundness                    y          y          y
-- Idempotence                  y          ~2         ~2
-- Commutativity                y          y          y
-- Lower bound                  ~3         ~5         y
-- Associativity                n          ~6         n
-- Monotonicity                 n          n          n
-- Top identity                 y          ~2         ~2
-- Absorption                   n          n          n
-- @
--
-- /Joins:/
--
-- @
--                          pseudoJoin  boundingBoxJoin  exactJoin
-- Soundness                    y          y                y
-- Idempotence                  y          ~1               ~2
-- Commutativity                y          y                y
-- Upper bound                  ~3         y                ~5
-- Associativity                n          y                ~6
-- Monotonicity                 n          ~4               n
-- Top annihilator              y          y                ~2
-- Absorption                   n          n                n
-- @
--
-- Side-condition keys for @~@:
--
-- [@~1@] equality holds modulo collapsing the stride to 1 (e.g.
--        @boundingBoxJoin a a@ has the same elements as @a@ but with stride 1).
--
-- [@~2@] axiom holds when the operand doesn't wrap mod @2^w@ as integers
--        (i.e. @start + n·stride <= mask@).
--
-- [@~3@] axiom holds when neither operand self-wraps (i.e. @n·stride <= mask@).
--
-- [@~4@] axiom holds when no operand wraps mod @2^w@ (i.e.
--        @start + n·stride <= mask@). 'A.ubounds' collapses any wrapping
--        interval to @(0, mask)@, so 'hull' is non-monotone on wrapping
--        inputs; 'boundingBoxJoin' inherits that gap.
--
-- [@~5@] axiom holds /when @exactJoin@ returns @Just@/. 'exactJoin' is a
--        partial operator: it returns 'Nothing' when the union isn't
--        exactly representable as a single progression, and the result
--        is undefined in that case.
--
-- [@~6@] axiom holds /when both nested computations return @Just@/.
--        'exactJoin' association orders can disagree on success: one
--        order may produce a single progression while another fails
--        because an intermediate union isn't a progression. When both
--        orders succeed, they produce the same result.
--
-- Notes:
--
-- * Soundness for 'pseudoMeet', 'pseudoJoin', 'boundingBoxJoin', and
--   'exactJoin' is /over/-approximation: every concrete element of the
--   intersection (resp. union) is in the result. 'exactJoin' is uniquely
--   /exact/ when it returns @Just@ — neither under nor over-approximating.
--   Soundness for 'lowerBound' is /under/-approximation: every result
--   element is in both operands (the converse may fail).
--
-- Trade-off summary:
--
-- * 'pseudoMeet' \/ 'pseudoJoin': precision-first. Preserve stride information
--   by coset refinement (over the tightest 'toArith' cover of each operand,
--   including coset arcs on self-wrapping inputs), at the cost of
--   associativity and monotonicity.
--
-- * 'boundingBoxJoin': structure-first. Routes through 'A.range' on the @min@\/@max@
--   of each operand's hull-based unsigned bounds — no shorter-arc heuristic,
--   so the operator is /associative/ and /monotone/. Saturates to 'top'
--   whenever either operand wraps mod @2^w@; pick this for fixpoint
--   iteration or widening, where saturation on wrap is acceptable.
--
-- * 'exactJoin' \/ 'exactMeet': partial, exact. Return @Just c@ only when
--   the union (resp. intersection) is itself representable as a single
--   progression; @Nothing@ otherwise. Let callers distinguish "the
--   operation compactifies cleanly" from "any single-progression cover
--   would either over- or under-approximate".
--
-- * 'lowerBound': sound /under/-approximation. The result's elements are
--   guaranteed to be in both operands (the genuine lower-bound property),
--   at the cost of dropping witnesses 'pseudoMeet' would keep. Use for
--   path-condition refinement, where adding witnesses is unsound.
--
-- /Precision dominance:/ on the over-approximating join side, 'pseudoJoin'
-- and 'boundingBoxJoin' are /incomparable as sets/ (because 'A.join' inside
-- 'pseudoJoin' picks the shorter possibly-wrapping arc while 'boundingBoxJoin' always
-- picks the non-wrapping bounding box), but 'pseudoJoin' is at least as precise
-- by /cardinality/: @size (pseudoJoin a b) <= size (boundingBoxJoin a b)@. See
-- 'pseudoJoinDominatesBoundingBoxJoin'. On the meet side, 'lowerBound' is below
-- 'pseudoMeet' when both are non-empty under subset dominance (they bound
-- the true intersection from opposite sides); see
-- 'lowerBoundDominatedByPseudoMeet'.
--
-- To see that strides do not form a (semi-)lattice, consider that two
-- progressions can have a set of common lower (resp. upper) bounds with no
-- greatest (resp. least) element. Example at @w = 4@: the common lower bounds
-- of @A = (0, 1, 3)@ and @C = (0, 3, 7)@ include @(0, 2, 1) = {0, 2}@, @(0,
-- 3, 1) = {0, 3}@, and @(2, 1, 1) = {2, 3}@, which are pairwise incomparable
-- under 'leqExact'.

-- | /O(w)/. Sound /over/-approximation of the intersection of two progressions.
-- For any concrete value @x@, if @x@ is a member of both @a@ and @b@, then
-- @x@ is a member of @pseudoMeet a b@. Returns 'Nothing' when the result would
-- be empty.
--
-- Uses 'leq' (the cheap reflexive+transitive variant) for the containment
-- short-circuits. See 'pseudoMeetPrecise' for the variant that uses 'leqExact'
-- short-circuits.
--
-- /Lattice axioms:/
--
-- * Soundness (over-approximation): yes ('correct_pseudoMeet').
-- * Idempotence: yes ('pseudoMeetIdempotent').
-- * Commutativity: yes ('pseudoMeetCommutative').
-- * Lower bound: yes when neither operand wraps mod @2^w@ ('pseudoMeetLowerBound').
-- * Top identity: yes ('pseudoMeetTopIdentity').
-- * Associativity: /no/.
-- * Monotonicity: /no/.
-- * Absorption: /no/.
--
-- /Precision:/ contains 'lowerBound' when both are non-empty
-- ('lowerBoundDominatedByPseudoMeet').
--
-- == Examples
--
-- @⊤@ intersected with a stride-2 progression returns that progression:
--
-- >>> let evens = mk4 0 2 7
-- >>> display evens
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
-- >>> fmap display (pseudoMeet w4 (top w4) evens)
-- Just "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
--
-- Progressions from disjoint cosets share no values:
--
-- >>> let a = mk4 0 4 3; b = mk4 2 4 3
-- >>> display a
-- "[*...*...*...*...]  = [0,4,8,12]"
-- >>> display b
-- "[..*...*...*...*.]  = [2,6,10,14]"
-- >>> pseudoMeet w4 a b
-- Nothing
pseudoMeet ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
pseudoMeet w a b =
  assert (proper a) $
  assert (proper b) $
  case () of
    _ | leq a b -> Just a
      | leq b a -> Just b
      | otherwise -> pseudoMeetStridesBy compactify w a b

-- | /O(w^2)/. Like 'pseudoMeet', but uses 'leqExact' for the containment
-- short-circuits. This preserves the smaller operand exactly when one is
-- contained in the other.
pseudoMeetPrecise ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
pseudoMeetPrecise w a b =
  assert (proper a) $
  assert (proper b) $
  case () of
    _ | leqExact a b -> Just a
      | leqExact b a -> Just b
      | otherwise -> pseudoMeetStridesBy compactifyPrecise w a b

-- | The shared structure of 'pseudoMeet' and 'pseudoMeetPrecise', parameterized
-- over the compactify variant.
pseudoMeetStridesBy ::
  (1 <= w) =>
  -- | 'compactify' or 'compactifyPrecise'
  (NatRepr w -> [Domain w] -> [Domain w]) ->
  NatRepr w ->
  Domain w ->
  Domain w ->
  Maybe (Domain w)
-- References:
--
-- * CLP 4.1 Set Operations
pseudoMeetStridesBy compactifyOp w a b
  | cosetsDisjoint a b
  = Nothing
  -- Neither operand self-wraps → 'ssplit' each into non-wrapping pieces, run
  -- 'arcMeetClosed' on each pair, take the union of sub-meets. When neither
  -- operand even wraps mod @2^w@ this collapses to a single 'arcMeetClosed'
  -- call (the exact intersection); when one or both wrap, the union
  -- over-approximates.
  | Prelude.not (isSelfWrapping a || isSelfWrapping b)
  = case compactifyOp w
           [ c | ai <- ssplit w a
               , bj <- ssplit w b
               , Just c <- [arcMeetClosed w ai bj]
           ] of
      []     -> Nothing
      (c:cs) -> Just (Prelude.foldr (pseudoJoin w) c cs)
  | otherwise = do
      -- 'toArith' (rather than 'hull') gives a tighter starting interval
      -- on self-wrapping operands: a self-wrapping orbit with even stride
      -- has 'toArith' return its coset arc rather than saturating to 'top'.
      -- Mirrors what 'pseudoJoinStrides' does on the same wrap-handling
      -- path.
      arith <- fromArith w (A.meet (toArith a) (toArith b))
      -- Refine arith to the coset shared by both operands.
      --
      -- Each operand's orbit lies in @start + ⟨g⟩@ as a subset of
      -- @Z/2^w@, where @g = gcd(stride, 2^w)@ (a power of two). The
      -- intersection of two such cosets, when nonempty, is itself a
      -- coset of @max(g_a, g_b)@ — the larger of the two
      -- powers-of-two — anchored at any common element. We use
      -- whichever of @start a@ or @start b@ has the larger @g@.
      --
      -- Note this restriction is /weaker/ than restricting to
      -- @lcm(stride a, stride b)@: when an operand wraps mod @2^w@
      -- its bounded arc visits multiple residues mod its own stride,
      -- so only the @g@-coset structure survives the wrap.
      let !g_a = strideGcd a
          !g_b = strideGcd b
          !d = max g_a g_b
          !anchor = if g_a >= g_b then start a else start b
      restrictToCoset w arith anchor d

-- | /O(w)/. @lcm(x, y)@ on 'Natural's, computed via @x \/ gcd · y@. Both
-- arguments must be positive.
lcmNat :: Natural -> Natural -> Natural
lcmNat x y = (x `Prelude.div` Prelude.gcd x y) * y
{-# INLINE lcmNat #-}

-- | /O(w)/. Restrict a stride-1 progression @arith@ to the values
-- congruent to @s@ modulo @d@: i.e., produce the stride-@d@ progression
-- whose elements are exactly @arith ∩ (s + d·Z)@.
--
-- Returns 'Nothing' if no element of @arith@ lies on the coset.
restrictToCoset ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Maybe (Domain w)
restrictToCoset w arith s d
  | d <= 1 = Just arith
  | otherwise =
      let m  = mask arith
          lo = start arith
          nn = n arith
          end' = lo + nn  -- arith is stride-1, so end is lo + n
          -- @lo'@: first value in @[lo, end']@ congruent to @s@ mod @d@.
          off = modSub m s lo `Prelude.mod` d
          lo' = lo + off
      in if lo' > end'
           then Nothing
           else let nn' = (end' - lo') `Prelude.div` d
                in Just (mk w (modMask arith lo') d nn')

-- | /O(w)/. CLP-style intersection of two progressions whose orbits lie in
-- @[start, start + n·stride]@ without wrap mod @2^w@ (i.e. plain integer
-- intervals). Returns the exact intersection.
--
-- Precondition: both inputs satisfy @start + n · stride <= mask@.
arcMeetClosed ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
arcMeetClosed w a b
  | n a == 0
  = if member b (start a) then Just (mk w (start a) 1 0) else Nothing
  | n b == 0
  = if member a (start b) then Just (mk w (start b) 1 0) else Nothing
  | otherwise =
      assert (sA + n a * stride a <= mask a) $
      assert (sB + n b * stride b <= mask a) $
      let !d  = lcmNat (stride a) (stride b)
          !lo = max sA sB
          !hi = min endA endB
          mkResult theta =
            let !steps = (hi - theta) `Prelude.div` d
                -- A stride > mask only happens when @lcm@ exceeds @2^w@, in
                -- which case at most one element of either operand falls in
                -- the intersection box, so @steps == 0@ and the result is a
                -- singleton. @mk@ canonicalizes singletons to stride 1 anyway.
                !d' = if d > mask a then 1 else d
            in Just (mk w (modMask a theta) d' steps)
      in if hi < lo then Nothing else
        -- Solve stride a · i − stride b · j = start b − start a
        -- for 0 ≤ i ≤ n a, 0 ≤ j ≤ n b. The lex-least solution gives
        -- the smallest common value; the result stride is
        -- @lcm(stride a, stride b)@.
        let !c = toInteger sB - toInteger sA in
        if c == 0
          then mkResult lo
          else case SI.solveLinearDiophantine
                      (toInteger (stride a)) (toInteger (stride b))
                      c
                      (toInteger (n a)) (toInteger (n b)) of
                 Nothing -> Nothing
                 Just (i, _) ->
                   let !theta = sA + fromInteger i * stride a
                   in if theta > hi
                        then Nothing
                        else mkResult theta
  where
    sA = start a
    sB = start b
    endA = sA + n a * stride a
    endB = sB + n b * stride b

-- | /O(w)/. \"South-pole split\": split at the unsigned boundary (between
-- @umax = 2^w - 1@ and @0@). Returns pieces whose concretizations partition
-- @c@\'s concretization, where no piece crosses 0.
--
--   * Non-wrap-mod-@2^w@: returns @[c]@.
--   * Wrap-mod-@2^w@ but not self-wrapping: two pieces, the high arc
--     @[start, umax]@ and the low arc @[0, end]@.
--   * Self-wrapping: collapses to the full @g@-coset @{ start mod g + i · g
--     | 0 <= i < 2^w \/ g }@, which spans @[0, mask]@ exactly once and so
--     is non-wrap-mod-@2^w@.
--
-- References:
--
-- * WI 3.2 Analysing expressions
ssplit :: NatRepr w -> Domain w -> [Domain w]
ssplit w c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (proper c) $
  case () of
    _ | isSelfWrapping c -> [fullCoset w c]
      | s + nn * t <= m  -> [c]
      | otherwise        ->
          -- Wrap point: largest @i@ with @s + i·t <= m@.
          let !i1 = (m - s) `Prelude.div` t
              !s2 = (s + (i1 + 1) * t) .&. m
              !n2 = nn - i1 - 1
          in [mk w s t i1, mk w s2 t n2]


-- | /O(w)/. \"North-pole split\": split at the signed boundary (between
-- @smax = 2^(w-1) - 1@ and @smin = 2^(w-1)@). Returns pieces whose
-- concretizations partition @c@\'s concretization, where no piece crosses
-- the sign boundary.
--
--   * Doesn't cross sign boundary: returns @[c]@.
--   * Crosses sign boundary but not self-wrapping: two pieces, one ending
--     at @smax@ and one starting at @smin@.
--   * Self-wrapping: collapses to the full @g@-coset, which we then split
--     at the sign boundary (it always spans both halves).
--
-- References:
--
-- * CLP 3.5 Circularity and Overflow
-- * WI 3.2 Analysing expressions
nsplit :: (1 <= w) => NatRepr w -> Domain w -> [Domain w]
nsplit w c
  | isSelfWrapping c = nsplit w (fullCoset w c)
  | otherwise        = nsplitNonSelfWrap w c

-- | Helper: 'nsplit' specialized to non-self-wrapping inputs.
nsplitNonSelfWrap :: (1 <= w) => NatRepr w -> Domain w -> [Domain w]
nsplitNonSelfWrap w c@Domain{start = s, stride = t, n = nn, mask = m} =
  assert (Prelude.not (isSelfWrapping c)) $
  -- Sign boundary @smax / smin@: smax = 2^(w-1) - 1, smin = 2^(w-1).
  -- For ssplit-output (non-wrap-mod-@2^w@), the orbit lies in @[s, s + nn·t]@
  -- as integers. The boundary is crossed iff @s <= smax < s + nn·t@.
  let !smin = 1 `shiftL` (NR.widthVal w - 1)
      !smax = smin - 1
      !endI = s + nn * t
  in if s > smax || endI <= smax
       then [c]  -- no crossing of the sign boundary
       else
         -- Largest @i@ with @s + i·t <= smax@:
         let !i1 = (smax - s) `Prelude.div` t
             !s2 = (s + (i1 + 1) * t) .&. m
             !n2 = nn - i1 - 1
         in [mk w s t i1, mk w s2 t n2]

-- | The full @g@-coset of @c@: the orbit @{ s' + i · g | 0 <= i < 2^w \/ g }@
-- where @g = gcd(stride, 2^w)@ and @s' = start mod g@. This is a
-- non-self-wrapping progression that contains @c@\'s entire concretization
-- (and no more, since both lie in the same coset).
fullCoset :: NatRepr w -> Domain w -> Domain w
fullCoset w c =
  let !g  = strideGcd c
      !s' = start c .&. (g - 1)
  in mk w s' g (orbitLen c - 1)

-- | /O(w^2)/. Exact intersection: returns @Just c@ when the intersection
-- of @a@ and @b@'s element sets is itself representable as a single
-- progression; @Nothing@ otherwise. Mirror of 'exactJoin'.
--
-- Distinct from 'pseudoMeet' (sound /over/-approximation, always returns
-- some progression) and 'lowerBound' (sound /under/-approximation, may
-- drop witnesses): 'exactMeet' returns 'Just' /exactly/ when neither
-- approximation is needed.
--
-- /Lattice axioms:/
--
-- * Soundness (when @Just@): the result is /exact/, equal to @a ∩ b@ —
--   neither under nor over-approximating ('correct_exactMeet').
-- * Idempotence: @exactMeet a a == Just a@ for non-wrap-mod-@2^w@ operands
--   ('exactMeetIdempotent').
-- * Commutativity: yes ('exactMeetCommutative').
-- * Lower bound: when @Just c@, @c@ is contained in both operands
--   ('exactMeetLowerBound').
-- * Top identity: @exactMeet a top == Just a@ for non-wrap-mod-@2^w@ @a@
--   ('exactMeetTopIdentity').
-- * Associativity: yes /when both nested computations return @Just@/
--   ('exactMeetAssociative'). Same partial-operator caveat as 'exactJoin':
--   one association can succeed while another fails.
-- * Monotonicity: /no/ — removing elements can break exact representability.
exactMeet ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
exactMeet w a b =
  assert (proper a) $
  assert (proper b) $
  assert (mask a == mask b) $
  if isSelfWrapping a || isSelfWrapping b
    then Nothing
    else
      let arcMeets =
            [ c
            | ai <- ssplit w a
            , bj <- ssplit w b
            , Just c <- [arcMeetClosed w ai bj]
            ]
      in case compactifyPrecise w arcMeets of
           [c] -> Just c
           _   -> Nothing

-- | /O(w)/. A strided lower bound on the intersection: a sound
-- /under/-approximation. Note this is /not/ the greatest lower bound —
-- the lattice of strided sets has no g.l.b. for incomparable elements (cf.
-- 'pseudoMeet'). For any concrete value @x@, if @x@ is a member of @lowerBound
-- a b@, then @x@ is a member of both @a@ and @b@. The converse may fail:
-- 'lowerBound' may /miss/ witnesses that lie outside its strided shape, but it
-- never invents any.
--
-- Returns the /largest/ candidate (by 'size') from 'lowerBounds'; use
-- 'lowerBounds' directly when you need every sub-progression.
--
-- Distinct from 'pseudoMeet' (a sound /over/-approximation): 'lowerBound' is the
-- right tool for path-condition refinement, where adding witnesses would be
-- unsound.
--
-- /Lattice axioms:/
--
-- * Soundness (under-approximation): yes ('correct_lowerBound') — every
--   element of the result is in both operands.
-- * Lower bound (genuine): yes ('lowerBoundLeqExactBoth') — unconditional,
--   unlike 'pseudoMeetLowerBound' which is restricted to non-wrapping operands.
-- * Idempotence: yes when the operand is non-wrap-mod-@2^w@
--   ('lowerBoundIdempotent'); otherwise the result is a strict subset.
-- * Commutativity: yes ('lowerBoundCommutative').
-- * Top identity: yes when the operand is non-wrap-mod-@2^w@
--   ('lowerBoundTopIdentity').
-- * Associativity: /no/ — picking the largest candidate makes the choice
--   value-dependent, breaking compositionality.
-- * Monotonicity: /no/ — 'lowerBound' may drop witnesses, and which witnesses
--   are dropped depends on stride alignment.
-- * Absorption: /no/.
--
-- /Precision:/ contained in 'pseudoMeet' (when both are non-empty); they
-- bound the true intersection from opposite sides
-- ('lowerBoundDominatedByPseudoMeet').
--
-- @
-- a:      [*.*.*.*.*.......]   start 0,  stride 2, n 4: {0,2,4,6,8}
-- b:      [*..*..*..*..*...]   start 0,  stride 3, n 4: {0,3,6,9,12}
-- 'lowerBound':  [*.....*.........]   start 0,  stride 6, n 1: {0,6}
-- @
lowerBound ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  Domain w ->
  Maybe (Domain w)
-- Operands that wrap mod @2^w@ are handled by 'ssplit'-ing each into its
-- non-wrapping pieces and returning the first non-empty arc-meet; this is
-- still a sound under-approximation, since each piece is a subset of the
-- corresponding operand. Self-wrapping operands (whose orbits revisit the
-- starting point without exhausting the coset) are first dropped to their
-- longest non-self-wrapping prefix @(start, stride, (mask - start)/stride)@
-- — also a subset of the original orbit — and then handled the same way.
lowerBound w a b =
  assert (proper a) $
  assert (proper b) $
  assert (mask a == mask b) $
  case lowerBounds w a b of
    []     -> Nothing
    (c:cs) -> Just (List.foldl' pickLarger c cs)
  where
    pickLarger x y = if size y > size x then y else x

-- | /O(w)/. Like 'lowerBound', but returns /every/ valid sub-progression
-- arc-meet found across the @ssplit@ pairing. Each element is a sound
-- under-approximation of the intersection on its own; the union of all
-- elements is exactly the (split-aware) intersection of @a@ and @b@. Use
-- when the precision of a single 'lowerBound' result is insufficient.
--
-- The list is empty iff 'lowerBound' would return 'Nothing'. Since each
-- operand 'ssplit's into at most two pieces, at most four candidates are
-- returned; they may overlap or be individually mergeable, but are left
-- separate here.
lowerBounds ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  Domain w ->
  [Domain w]
lowerBounds w a b =
  assert (proper a) $
  assert (proper b) $
  assert (mask a == mask b) $
  case () of
    _ | n a == 0 -> [a | member b (start a)]
      | n b == 0 -> [b | member a (start b)]
      -- Self-wrapping operands are first reduced to a non-self-wrapping
      -- sub-progression via 'trimSelfWrap' (still a subset of the original
      -- orbit, so the under-approximation contract is preserved).
      | otherwise ->
          let !aTrim = trimSelfWrap w a
              !bTrim = trimSelfWrap w b
              -- 'ssplit' partitions each operand into 1-or-2 non-wrap-mod-@2^w@
              -- pieces /exactly/. 'arcMeetClosed' on each pair is exact;
              -- collect every non-empty pair.
              pairs = [ (pa, pb) | pa <- ssplit w aTrim, pb <- ssplit w bTrim ]
              raw = [ c | (pa, pb) <- pairs, Just c <- [arcMeetClosed w pa pb] ]
          in compactify w raw

-- | /O(w)/. If @c@ self-wraps, drop to a non-self-wrapping sub-progression
-- of @c@'s orbit. Otherwise return @c@ unchanged. Used by 'lowerBound' to
-- extract a sound under-approximation from a self-wrapping operand.
--
-- Picks the longer of two segments:
--
-- * /Lap 0/: indices @[0, (mask - start)/stride]@ — the naive prefix from
--   @start@ before the orbit first wraps past @mask@.
-- * /Lap 1/: indices @[ceil((2^w - start)/stride), ...]@ — the segment
--   immediately after the first wrap, which has fresh @[0, 2^w)@ runway and
--   so is often longer when @start@ is close to @mask@.
--
-- Both are non-self-wrapping sub-orbits of @c@, so the result is a subset of
-- @c@. Later laps could in principle be even longer, but lap 1's length
-- already matches the maximum interior-lap length up to a single element,
-- so going further is rarely worth the extra arithmetic.
trimSelfWrap :: NatRepr w -> Domain w -> Domain w
trimSelfWrap w c@Domain{start = s, stride = t, n = nn, mask = m}
  | Prelude.not (isSelfWrapping c) = c
  | lap1Count > lap0Count =
      mk w ((s + lap1Start * t) .&. m) t (lap1End - lap1Start)
  | otherwise = mk w s t lap0End
  where
    !modulus = m + 1
    !lap0End   = min nn ((m - s) `Prelude.div` t)
    !lap0Count = lap0End + 1
    -- @lap1Start@: smallest @i ≥ 1@ with @s + i·t ≥ modulus@.
    !lap1Start = ((modulus - s) + t - 1) `Prelude.div` t
    -- @lap1End@: largest @i@ with @s + i·t < 2·modulus@, capped at @n@.
    !lap1End   = min nn ((2 * modulus - 1 - s) `Prelude.div` t)
    !lap1Count = if lap1Start <= nn && lap1Start <= lap1End
                 then lap1End - lap1Start + 1
                 else 0

-- | /O(w)/. Sound /over/-approximation of the union of two progressions:
-- a single progression containing every member of either operand.
--
-- Uses 'leq' for the containment short-circuits. See 'pseudoJoinPrecise' for
-- the variant that uses 'leqExact'.
--
-- /Lattice axioms:/
--
-- * Soundness (over-approximation): yes ('correct_pseudoJoin').
-- * Idempotence: yes ('pseudoJoinIdempotent').
-- * Commutativity: yes ('pseudoJoinCommutative').
-- * Upper bound: yes when neither operand wraps mod @2^w@ ('pseudoJoinUpperBound').
-- * Top annihilator: yes ('pseudoJoinTopAnnihilator').
-- * Associativity: /no/.
-- * Monotonicity: /no/.
-- * Absorption: /no/.
--
-- /Precision:/ the most precise join — contained in 'boundingBoxJoin'
-- ('pseudoJoinDominatesBoundingBoxJoin').
--
-- == Examples
--
-- Joining complementary stride-4 progressions covers all even values:
--
-- >>> let a = mk4 0 4 3; b = mk4 2 4 3
-- >>> display a
-- "[*...*...*...*...]  = [0,4,8,12]"
-- >>> display b
-- "[..*...*...*...*.]  = [2,6,10,14]"
-- >>> display (pseudoJoin w4 a b)
-- "[*.*.*.*.*.*.*.*.]  = [0,2,4,6,8,10,12,14]"
pseudoJoin :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoin w a b
  | leq a b = b
  | leq b a = a
  | otherwise = pseudoJoinStrides w a b

-- | /O(w^2)/. Like 'pseudoJoin', but uses 'leqExact' for the containment
-- short-circuits. This preserves the larger operand exactly when one
-- contains the other.
pseudoJoinPrecise :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoinPrecise w a b
  | leqExact a b = b
  | leqExact b a = a
  | otherwise = pseudoJoinStrides w a b

-- | /O(w)/. Sound (over-approximating) join used as the general
-- (non-short-circuit) path of 'pseudoJoin' and 'pseudoJoinPrecise'.
pseudoJoinStrides :: (1 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoinStrides w a b =
  assert (proper a) $
  assert (proper b) $
  let !delta = modSub (mask a) (start a) (start b)
      -- Result coset stride: powers of two divide gcd-down to the min.
      -- A singleton has canonical stride 1, but a singleton lies on /every/
      -- coset, so take the other operand's coset stride when one is singleton.
      !g0    = case (n a, n b) of
                 (0, 0) -> 1
                 (0, _) -> strideGcd b
                 (_, 0) -> strideGcd a
                 _      -> min (strideGcd a) (strideGcd b)
      !g     = if delta == 0 then g0 else min g0 (lowestSetBit delta)
      !arc   = A.join (toArith a) (toArith b)
  in case fromArith w arc of
       Nothing  -> mk w 0 1 (mask a)  -- shouldn't happen on proper inputs
       Just dom -> case restrictToCoset w dom (start a) g of
         Nothing  -> mk w 0 1 (mask a)
         Just dom' -> dom'

-- | /O(w)/. Bounding-box join: 'A.range' on the @min@\/@max@ of each
-- operand's unsigned bounds. Computed without going through 'A.join's
-- shorter-arc heuristic, so the operator is associative and monotone.
--
-- Saturates to 'top' whenever either operand wraps mod @2^w@, since
-- 'A.ubounds' on a wrapping interval reports @(0, mask)@.
--
-- Use when the lattice properties matter (fixpoint iteration, widening)
-- and saturation on wrap is acceptable.
--
-- /Lattice axioms:/
--
-- * Soundness (over-approximation): yes ('correct_boundingBoxJoin').
-- * Idempotence: yes, modulo collapsing the stride to 1 ('boundingBoxJoinIdempotent').
-- * Commutativity: yes ('boundingBoxJoinCommutative').
-- * Upper bound: yes ('boundingBoxJoinUpperBound'), unconditional.
-- * Top annihilator: yes ('boundingBoxJoinTopAnnihilator').
-- * Associativity: yes ('boundingBoxJoinAssociative'). 'min' and 'max' are
--   associative, and that's the whole computation.
-- * Monotonicity: yes /when no operand wraps mod @2^w@/
--   ('boundingBoxJoinMonotone'); 'hull' is non-monotone on wrapping inputs
--   (because 'A.ubounds' collapses them), and 'boundingBoxJoin' inherits
--   that gap.
-- * Absorption: /no/ (no corresponding meet that performs the dual).
--
-- /Precision:/ the coarsest join here — contains 'pseudoJoin'
-- ('pseudoJoinDominatesBoundingBoxJoin').
boundingBoxJoin ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Domain w
boundingBoxJoin w a b =
  assert (proper a) $
  assert (proper b) $
  let (la, ha) = A.ubounds (hull a)
      (lb, hb) = A.ubounds (hull b)
  in case fromArith w (A.range w (min la lb) (max ha hb)) of
       Just c  -> c
       Nothing -> top w  -- 'A.range' of non-empty bounds is never bottom

-- | /O(w^2)/. Exact union: returns @Just c@ when the union of @a@ and @b@'s
-- element sets is itself representable as a single progression; @Nothing@
-- otherwise. Distinguishes the (common) case where @a ∪ b@ stays inside a
-- single arithmetic progression from the (also common) case where it
-- doesn't and any single-progression cover would over-approximate.
--
-- /Lattice axioms:/
--
-- * Soundness (when @Just@): the result is /exact/, equal to @a ∪ b@ —
--   neither under nor over-approximating ('correct_exactJoin').
-- * Idempotence: @exactJoin a a == Just a@ for non-wrap-mod-@2^w@ operands
--   ('exactJoinIdempotent').
-- * Commutativity: yes ('exactJoinCommutative').
-- * Upper bound: when @Just c@, both operands are subsets of @c@
--   ('exactJoinUpperBound').
-- * Top identity: @exactJoin a top == Just top@
--   ('exactJoinTopAnnihilator') for non-wrap-mod-@2^w@ operands.
-- * Associativity: yes /when both nested computations return @Just@/
--   ('exactJoinAssociative'). One association can succeed while another
--   fails (each intermediate must itself be a single progression), so
--   the property only constrains the @Just@\/@Just@ case.
-- * Monotonicity: /no/ — adding elements can break exact representability,
--   so a larger operand can take @Just@ to @Nothing@.
exactJoin ::
  (1 <= w) =>
  NatRepr w ->
  Domain w -> Domain w -> Maybe (Domain w)
exactJoin w a b =
  assert (proper a) $
  assert (proper b) $
  assert (mask a == mask b) $
  case compactifyPrecise w [a, b] of
    [c] -> Just c
    _   -> Nothing

-- | /O(m^2 · w)/, where @m@ is the input list length. Merges any pair of
-- progressions whose union is /exactly/ representable as a single
-- progression. Iterates until no more merges apply.
--
-- Uses 'leq', see 'compactifyPrecise' for the variant that uses 'leqExact'.
compactify :: (1 <= w) => NatRepr w -> [Domain w] -> [Domain w]
compactify = compactifyBy leq

-- | /O(m^2 · w^2)/. Like 'compactify' but uses 'leqExact' for the
-- containment check, catching all merges at the cost of a higher per-merge
-- complexity.
compactifyPrecise :: (1 <= w) => NatRepr w -> [Domain w] -> [Domain w]
compactifyPrecise = compactifyBy leqExact

-- | The shared structure of 'compactify' and 'compactifyPrecise',
-- parameterized over the containment check used by 'tryMergeBy'.
compactifyBy ::
  (1 <= w) =>
  -- | 'leq' or 'leqExact'
  (Domain w -> Domain w -> Bool) ->
  NatRepr w ->
  [Domain w] ->
  [Domain w]
compactifyBy leqOp w cs0 =
  assert (Prelude.all proper cs0) $
  assert (Prelude.all (\c -> mask c == integerToNatural (maxUnsigned w)) cs0) $
  -- Iterate to a fixed point. A single pass would miss merges where an
  -- early head is non-mergeable until /after/ a later pair merges, leaving
  -- the result order-dependent (and so non-commutative for callers like
  -- 'exactJoin' that compare result lengths).
  fixedPoint cs0
  where
    fixedPoint cs =
      let cs' = onePass cs
      in if Prelude.length cs' == Prelude.length cs
           then cs'
           else fixedPoint cs'

    onePass []     = []
    onePass (c:cs) =
      case tryMergeWithBy leqOp w c cs of
        Just (merged, rest) -> merged : onePass rest
        Nothing             -> c : onePass cs

-- | /O(m · w)/, where @m@ is the length of @xs@. Find the first @x@ in
-- @xs@ such that @c@ and @x@ merge exactly into a single progression. If
-- found, return the merged progression and the remaining list with @x@
-- removed. Uses 'leq'; see 'tryMergeWithPrecise' for the 'leqExact'
-- variant.
tryMergeWith ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  [Domain w] ->
  Maybe (Domain w, [Domain w])
tryMergeWith = tryMergeWithBy leq

-- | /O(m · w^2)/. Like 'tryMergeWith', but uses 'leqExact'.
tryMergeWithPrecise ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  [Domain w] ->
  Maybe (Domain w, [Domain w])
tryMergeWithPrecise = tryMergeWithBy leqExact

-- | The shared structure of 'tryMergeWith' and 'tryMergeWithPrecise'.
tryMergeWithBy ::
  (1 <= w) =>
  (Domain w -> Domain w -> Bool) ->
  NatRepr w ->
  Domain w ->
  [Domain w] ->
  Maybe (Domain w, [Domain w])
tryMergeWithBy leqOp w c = \case
  [] -> Nothing
  (x:xs) ->
    case tryMergeBy leqOp w c x of
      Just merged -> Just (merged, xs)
      Nothing -> case tryMergeWithBy leqOp w c xs of
        Just (merged, rest) -> Just (merged, x : rest)
        Nothing             -> Nothing

-- | /O(w)/. Try to merge two progressions into a single progression
-- representing /exactly/ their union. Returns 'Nothing' if the union
-- isn't itself a progression.
--
-- Operands may wrap mod @2^w@ or self-wrap. Each progression is a
-- contiguous arc on the cyclic index circle of its coset (no element
-- repeats — see 'toListNoDuplicates'). If the union is a progression
-- with @k = |c1| + |c2| - |c1 ∩ c2|@ elements, its anchor must be one
-- of the four operand endpoints @{s1, s1 + n c1 · stride c1, s2,
-- s2 + n c2 · stride c2}@ and its stride is determined by the anchor's
-- cyclic span: @t = span / (k - 1)@. See 'mergeCandidates'.
--
-- Verifies each candidate via @leqOp@ that both operands are subsets,
-- and via 'intersectionSize' that the candidate's size equals @k@.
tryMergeBy ::
  (1 <= w) =>
  -- | 'leq' or 'leqExact'
  (Domain w -> Domain w -> Bool) ->
  NatRepr w ->
  Domain w ->
  Domain w ->
  Maybe (Domain w)
tryMergeBy leqOp w c1 c2 =
  assert (proper c1) $
  assert (proper c2) $
  assert (mask c1 == mask c2) $
  let !overlap   = intersectionSize w c1 c2
      !unionSize = size c1 + size c2 - overlap
      cands = mergeCandidates w c1 c2 unionSize
      ok cand =
        leqOp c1 cand && leqOp c2 cand && size cand == unionSize
  in case List.find ok cands of
       Just c  -> Just c
       Nothing -> Nothing

-- | /O(w)/. Build the merge candidates for 'tryMergeBy'.
--
-- The merged progression — if one exists — has @unionSize@ elements
-- equally spaced around @Z\/2^w@. Its stride is determined by its anchor
-- (any one element) and span (cyclic distance to the farthest element):
-- @t = span / (unionSize - 1)@. Each operand contributes two natural
-- anchors (its @start@ and @end = start + n · stride@), giving up to
-- four candidates. The caller verifies each via 'leqOp' and a cardinality
-- check.
mergeCandidates ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> [Domain w]
mergeCandidates w c1 c2 unionSize
  | n c1 == 0 && n c2 == 0 && start c1 == start c2 = [c1]
  | unionSize == 0 = []
  -- Singleton union after merging two equal-element-set operands.
  | unionSize == 1 = [mk w (start c1) 1 0]
  | otherwise =
      let !m       = mask c1
          !s1      = start c1
          !s2      = start c2
          !end1    = (s1 + n c1 * stride c1) .&. m
          !end2    = (s2 + n c2 * stride c2) .&. m
          !nMerge  = unionSize - 1
          -- For a candidate AP anchored at @a@ with @unionSize@ elements,
          -- its stride is @span(a) / nMerge@ where @span(a)@ is the cyclic
          -- distance from @a@ to the farthest other endpoint of either
          -- operand. We try each endpoint as anchor; non-integer
          -- @span / nMerge@ rules the anchor out.
          endpoints = [s1, end1, s2, end2]
          tryAnchor a =
            let !d1 = modSub m s1   a
                !d2 = modSub m end1 a
                !d3 = modSub m s2   a
                !d4 = modSub m end2 a
                !sp = max (max d1 d2) (max d3 d4)
            in if sp `Prelude.mod` nMerge /= 0
                 then Nothing
                 else
                   let !t = sp `Prelude.div` nMerge
                       -- 'mk' will reject @t == 0@ (singleton fallback) or
                       -- @t > mask@; either signals an invalid candidate.
                   in if t == 0 || t > m || nMerge >= orbitLenOf m (lowestSetBit t)
                        then Nothing
                        else Just (mk w a t nMerge)
      in [c | a <- endpoints, Just c <- [tryAnchor a]]

-- | /O(w^2)/. An upper bound on the size of @c1 ∩ c2@. Splits each
-- operand's wrap and self-wrap structure with 'ssplit', runs
-- 'arcMeetClosed' on each pair of non-wrapping pieces, and sums their
-- sizes; clamps the result at @min |c1| |c2|@.
--
-- The bound is exact when neither operand self-wraps (then 'ssplit' pieces
-- partition each operand). On self-wrapping inputs, 'ssplit' returns the
-- /full coset/, which over-approximates the operand's element set. The
-- clamp keeps the result usable as a value to subtract from
-- @|c1| + |c2|@ without underflow; any over-estimate leads to a smaller
-- @unionSize@ and a tighter cardinality check, which 'tryMergeBy' rejects
-- via @size cand == unionSize@ rather than accepting a wrong merge.
intersectionSize ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Natural
intersectionSize w c1 c2 =
  let !pieces1 = ssplit w c1
      !pieces2 = ssplit w c2
      !raw = List.foldl' (+) 0
               [ size c
               | a <- pieces1, b <- pieces2, Just c <- [arcMeetClosed w a b]
               ]
  in min raw (min (size c1) (size c2))

-- ------------------------------------------------------------------
-- * Branch-condition assumptions

-- $assume
--
-- The 'assumeUlt', 'assumeUle', 'assumeUgt', 'assumeUge', 'assumeSlt',
-- 'assumeSle', 'assumeSgt', and 'assumeSge' operations refine the first
-- operand's progression by a comparison constraint against the second:
-- @assumeOp w a b@ returns a sound over-approximation of
--
-- @
-- { x ∈ γ(a) | ∃ y ∈ γ(b). x \`op\` y }
-- @
--
-- where @op@ is the corresponding (unsigned or signed) bitvector
-- comparison. Returns 'Nothing' when this set is provably empty (the
-- branch is infeasible). When the result is @Just c@, every value in
-- @γ(a)@ that satisfies the constraint with /some/ value in @γ(b)@ is in
-- @γ(c)@; @c@ may also include values not in @γ(a)@ (it is a sound
-- over-approximation, not a strict subset).
--
-- These are the standard transfer functions for branch conditions in
-- abstract interpretation: @if (x < y) then ... else ...@ refines the
-- abstract value of @x@ on the @then@ branch via 'assumeUlt', and on the
-- @else@ branch via 'assumeUge'.
--
-- Implemented by intersecting @a@ with the strided lift of an
-- 'A.Domain' range derived from @b@'s ('A.ubounds' or 'A.sbounds')
-- bounds:
--
--   * 'assumeUlt' / 'assumeUgt': constrain @x@ by @b@'s unsigned max\/min,
--     respectively, narrowed by one (strict).
--   * 'assumeUle' / 'assumeUge': constrain @x@ by @b@'s unsigned max\/min
--     (non-strict).
--   * 'assumeSlt' / 'assumeSle' / 'assumeSgt' / 'assumeSge': same, but
--     against signed bounds; the resulting unsigned range can wrap mod
--     @2^w@ when the signed bound straddles the sign boundary.

-- | /O(w^2)/. Refine @a@ by the assumption @x < y@ (unsigned),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeUlt ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUlt w a b
  | bhi == 0  = Nothing  -- y < bhi == 0 is impossible
  | alo >= bhi = Nothing  -- min(a) >= max(b) so x >= y always
  | otherwise = assumeUnsignedRange w a 0 (bhi - 1)
  where
    (alo, _ahi) = A.ubounds (toArith a)
    (_blo, bhi) = A.ubounds (toArith b)

-- | /O(w^2)/. Refine @a@ by the assumption @x <= y@ (unsigned),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeUle ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUle w a b
  | alo > bhi = Nothing
  | otherwise = assumeUnsignedRange w a 0 bhi
  where
    (alo, _ahi) = A.ubounds (toArith a)
    (_blo, bhi) = A.ubounds (toArith b)

-- | /O(w^2)/. Refine @a@ by the assumption @x > y@ (unsigned),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeUgt ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUgt w a b
  | blo == toInteger (mask a) = Nothing  -- x > 2^w - 1 impossible
  | ahi <= blo = Nothing
  | otherwise = assumeUnsignedRange w a (blo + 1) (toInteger (mask a))
  where
    (_alo, ahi) = A.ubounds (toArith a)
    (blo, _bhi) = A.ubounds (toArith b)

-- | /O(w^2)/. Refine @a@ by the assumption @x >= y@ (unsigned),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeUge ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeUge w a b
  | ahi < blo = Nothing
  | otherwise = assumeUnsignedRange w a blo (toInteger (mask a))
  where
    (_alo, ahi) = A.ubounds (toArith a)
    (blo, _bhi) = A.ubounds (toArith b)

-- | /O(w^2)/. Refine @a@ by the assumption @x < y@ (signed),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeSlt ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSlt w = assumeSignedBy w sltCase
  where
    -- (sign aᵢ, sign bⱼ) → contribution of @aᵢ@ to @{x ∈ aᵢ | ∃y ∈ bⱼ. x_s < y_s}@
    sltCase ai bj sa sb = case (sa, sb) of
      (Pos, Pos) -> assumeUlt w ai bj  -- both non-negative: signed = unsigned
      (Neg, Neg) -> assumeUlt w ai bj  -- both negative: order agrees with unsigned
      (Pos, Neg) -> Nothing            -- x ≥ 0 > y: always false
      (Neg, Pos) -> Just ai            -- x < 0 ≤ y: always true

-- | /O(w^2)/. Refine @a@ by the assumption @x <= y@ (signed),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeSle ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSle w = assumeSignedBy w sleCase
  where
    sleCase ai bj sa sb = case (sa, sb) of
      (Pos, Pos) -> assumeUle w ai bj
      (Neg, Neg) -> assumeUle w ai bj
      (Pos, Neg) -> Nothing
      (Neg, Pos) -> Just ai

-- | /O(w^2)/. Refine @a@ by the assumption @x > y@ (signed),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeSgt ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSgt w = assumeSignedBy w sgtCase
  where
    sgtCase ai bj sa sb = case (sa, sb) of
      (Pos, Pos) -> assumeUgt w ai bj
      (Neg, Neg) -> assumeUgt w ai bj
      (Pos, Neg) -> Just ai            -- x ≥ 0 > y: always true
      (Neg, Pos) -> Nothing

-- | /O(w^2)/. Refine @a@ by the assumption @x >= y@ (signed),
-- @x ∈ γ(a)@, @y ∈ γ(b)@. See the section header for semantics.
assumeSge ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
assumeSge w = assumeSignedBy w sgeCase
  where
    sgeCase ai bj sa sb = case (sa, sb) of
      (Pos, Pos) -> assumeUge w ai bj
      (Neg, Neg) -> assumeUge w ai bj
      (Pos, Neg) -> Just ai
      (Neg, Pos) -> Nothing

-- | Sign of a sign-coherent piece (a piece of 'signPieces', which is
-- non-wrap-mod-@2^w@ and lies entirely in either the non-negative or the
-- negative signed half).
data Sign = Pos | Neg
  deriving (Eq, Show)

-- | /O(w)/. Sign of a sign-coherent piece. Precondition: @c@ is a piece of
-- 'signPieces' (so its 'start' fully determines its sign half).
pieceSign :: NatRepr w -> Domain w -> Sign
pieceSign w c
  | start c < halfR = Pos
  | otherwise       = Neg
  where halfR = 1 `Bits.shiftL` (NR.widthVal w - 1)

-- | /O(w^2)/. Refine @a@ by intersecting with the unsigned range @[lo, hi]@,
-- where @0 <= lo <= hi <= 2^w - 1@. Returns 'Nothing' if the intersection is
-- provably empty.
--
-- The refined set @{x ∈ γ(a) | lo <= x <= hi}@ is a subset of @γ(a)@, so @a@
-- itself is always a sound result. 'pseudoMeet' is sound but not a lower
-- bound on wrapping operands, so when its result is larger than @a@ by
-- cardinality we keep @a@ instead.
assumeUnsignedRange ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Integer -> Integer -> Maybe (Domain w)
assumeUnsignedRange w a lo hi =
  case fromArith w (A.range w lo hi) of
    Nothing -> Nothing
    Just r  -> case pseudoMeet w a r of
      Nothing -> Nothing
      Just c  -> Just (if size c <= size a then c else a)

-- | Shared driver for 'assumeSlt', 'assumeSle', 'assumeSgt', 'assumeSge'.
-- Splits both operands at the sign boundary with 'signPieces', dispatches
-- per sign-pair to the supplied case analysis, and joins the surviving
-- contributions with 'pseudoJoin'.
--
-- For each piece @aᵢ@ of @a@, contributions from different @bⱼ@'s are
-- joined; if any contribution covers @aᵢ@ exactly, that piece is taken
-- whole (this happens for the cross-sign always-true cases). Otherwise
-- the pieces are joined across all @aᵢ@. This preserves @result ⊑ a@
-- piecewise (each contribution is a subset of its @aᵢ@) and
-- 'compactify' merges adjacent pieces when possible.
assumeSignedBy ::
  (1 <= w) =>
  NatRepr w ->
  -- | per-pair case analysis: @ai bj signOf-ai signOf-bj -> contribution of @ai@@
  (Domain w -> Domain w -> Sign -> Sign -> Maybe (Domain w)) ->
  Domain w -> Domain w -> Maybe (Domain w)
assumeSignedBy w perPair a b =
  case compactify w pieces of
    []     -> Nothing
    [c]    -> Just (clampToA c)
    (c:cs) -> Just (clampToA (List.foldl' (pseudoJoin w) c cs))
  where
    aPieces = signPieces w a
    bPieces = signPieces w b
    -- For each aᵢ, fold the contributions from all bⱼ via pseudoJoin and
    -- clamp by aᵢ itself: every contribution is already a subset of aᵢ,
    -- so any join overshoot can be safely capped.
    pieces = [ ci'
             | ai <- aPieces
             , let contribs = [ c
                              | bj <- bPieces
                              , Just c <- [perPair ai bj (pieceSign w ai) (pieceSign w bj)]
                              ]
             , Just ci' <- [combinePieceContribs w ai contribs]
             ]
    -- 'pseudoJoin' across pieces from different sign halves can overshoot
    -- @a@; clamp the final union by @a@ itself. (Each piece is already
    -- contained in some piece of @a@, so the true union is @⊆ a@.)
    clampToA c = if leqExact c a then c else a

-- | Combine per-piece contributions for a single @aᵢ@: join them with
-- 'pseudoJoin', then clamp by @aᵢ@ to preserve the subset invariant
-- (each contribution is already @⊑ aᵢ@, but 'pseudoJoin' may overshoot).
combinePieceContribs ::
  (1 <= w) =>
  NatRepr w -> Domain w -> [Domain w] -> Maybe (Domain w)
combinePieceContribs _w _ai []     = Nothing
combinePieceContribs w  ai  (c:cs) =
  let joined = List.foldl' (pseudoJoin w) c cs
  in Just (if leqExact joined ai then joined else ai)

-- ------------------------------------------------------------------
-- * Reduced product with bitwise

-- $reduced
--
-- A /reduced product/ pairs two abstract domains and exchanges information
-- between them so the joint result is tighter than either component alone.
-- Here that pairing is between strides ('Domain') and the bitwise tristate
-- domain ('B.Domain'). Either domain projects out of the other via
-- 'toBitwise'\/'fromBitwise' (already exported); 'reduceStep' is the
-- /reduction operator/ that exchanges those projections to refine both
-- components in lockstep.
--
-- Refinements only shrink each component, the per-width state space is finite,
-- so iterating to a fixed point ('reduce') terminates. In practice one or two
-- passes suffice.
--
-- Strides and bitwise see different things:
--
-- * Strides tracks the orbit's /coset/ structure (stride and start), which
--   the bitwise domain only captures via low constant bits.
-- * Bitwise tracks /individual bits/ across the whole orbit, which strides
--   can\'t represent above the stride.
--
-- Each side\'s extra information helps refine the other. 'reduceStep' is
-- 'Nothing' precisely when the two components are jointly unsatisfiable.

-- | /O(w log w)/. Refine a progression using a bitwise value.
--
-- Works directly, without going through a lossy 'fromBitwise' projection or
-- 'pseudoMeet'.
--
-- Two refinements compose:
--
-- == 1. Stride lift
--
-- Write @stride s = t = 2^v · m@ with @m@ odd. Every orbit element
-- @start + i·t@ has:
--
--   * bits @0..v-1@ fixed to @start@\'s low bits (the stride doesn\'t
--     touch them, those bits of the stride are 0);
--   * bit @v@ equal to @bit_v(start) XOR (i mod 2)@ (since @m@ is odd, the
--     low bit of @i·m@ is the low bit of @i@);
--   * bits above @v@ varying with @i@.
--
-- So:
--
-- 1. Bits @0..v-1@: if @b@ forces any of them to disagree with @start@,
--    return 'Nothing'.
-- 2. Bit @v@: if @b@ forces it to @q@, then @i mod 2 = q XOR bit_v(start)@,
--    halving the orbit. The new stride is @2·t@; the new start is either
--    @start@ (if @q == bit_v(start)@) or @start + t@ (otherwise); the new
--    @n@ is @floor(n\/2)@ or @ceil((n-1)\/2)@ accordingly.
-- 3. Iterate at the new @v+1@ until @b@ stops forcing bit @v@ — the run
--    of contiguous forced bits starting at the stride boundary lifts the
--    stride exactly that many doublings.
--
-- This step beats 'fromBitwise b': @fromBitwise@ produces a single
-- progression whose stride is set by the lowest /free/ bit of @b@, so
-- forced bits /above/ a free bit collapse on the projection. The lift
-- consumes them one at a time as stride doublings.
--
-- == 2. Arc clip
--
-- Above the contiguous run, scattered forced bits aren't representable
-- as a stride lift, but they show up in @b@\'s numeric bounds
-- @[blo, bhi]@. Intersect the lifted progression with the stride-1
-- arc @[blo, bhi]@ via 'arcMeetClosed' on each 'ssplit' piece. After
-- the lift, @[blo, bhi]@ is the only further info @b@ carries in
-- single-progression form, so this direct intersection is no less
-- precise than @pseudoMeet (fromBitwise b)@ would be on non-self-wrap
-- inputs and avoids 'pseudoMeet'\'s wrap pitfalls.
--
-- The clip is skipped on self-wrapping lift results: 'ssplit' over-
-- approximates them to the full coset, which would break the subset
-- guarantee. The lift alone still shrinks @s@.
--
-- Returns 'Nothing' precisely when the constraints are inconsistent —
-- @start@\'s low bits violate @b@, or the orbit was a singleton whose
-- value violates @b@.
--
-- == Example
--
-- evens × \"bit 1 forced to 1\" = @{2, 6, 10, 14}@ exactly:
--
-- >>> import qualified What4.Domains.BV.Bitwise as B
-- >>> let evens = mk4 0 2 7
-- >>> let bm = B.range w4 0b0010 0b1111
-- >>> fmap display (refineByBits w4 evens bm)
-- Just "[..*...*...*...*.]  = [2,6,10,14]"
refineByBits ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  B.Domain w ->
  Maybe (Domain w)
refineByBits = refineByBitsBy compactify

-- | /O(w^2)/. Like 'refineByBits', but uses 'compactifyPrecise' (and
-- thus 'leqExact') for the post-arc-clip merge. Catches the
-- complementary-singleton case described in 'arcClipBitwise' that
-- 'refineByBits' misses, at the cost of a higher per-call complexity.
refineByBitsPrecise ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  B.Domain w ->
  Maybe (Domain w)
refineByBitsPrecise = refineByBitsBy compactifyPrecise

-- | The shared structure of 'refineByBits' and 'refineByBitsPrecise',
-- parameterized over the compactify variant used inside 'arcClipBitwise'.
refineByBitsBy ::
  (1 <= w) =>
  -- | 'compactify' or 'compactifyPrecise'
  (NatRepr w -> [Domain w] -> [Domain w]) ->
  NatRepr w ->
  Domain w ->
  B.Domain w ->
  Maybe (Domain w)
refineByBitsBy compactifyOp w s b = do
  l <- liftForcedBits w s zo
  arcClipBitwise compactifyOp w l (blo, bhi)
  where
    zo = knownZerosOnesNat b
    (bloI, bhiI) = B.bitbounds b
    blo = integerToNatural bloI
    bhi = integerToNatural bhiI

-- | /O(w)/. Forced bits of a 'B.Domain' as a @(zeros, ones)@ pair of
-- 'Natural's: @zeros@ has a 1 at every position forced to 0, @ones@ at
-- every position forced to 1.
--
-- The two values are bit-disjoint (@zeros .&. ones == 0@), and a value
-- @x@ is a member of @b@ iff its forced positions agree with @(zeros,
-- ones)@: see 'knownZerosOnesNatDisjoint' and 'knownZerosOnesNatMember'.
knownZerosOnesNat :: B.Domain w -> (Natural, Natural)
knownZerosOnesNat b =
  -- @bm = mask@; @lo@ has 1s where every member has a 1 (forced ones);
  -- @hi@ has 1s where any member could have a 1, so @bm `xor` hi@ has 1s
  -- where every member has a 0 (forced zeros).
  let (lo, hi) = B.bitbounds b
      bm       = B.bvdMask b
  in (integerToNatural (bm `Bits.xor` hi), integerToNatural lo)

-- | /O(w log w)/. Refine a progression by the forced-bit pair @(zeros,
-- ones)@ of a 'B.Domain' (see 'knownZerosOnesNat') via stride lifting.
--
-- Walks the contiguous run of forced bits starting at the stride
-- boundary of @s@: each step doubles the stride and halves the orbit
-- (selecting the parity that matches the forced bit). On a singleton
-- input, returns 'Just s' if @start s@ agrees with the forced bits and
-- 'Nothing' otherwise.
--
-- Returns 'Nothing' precisely when @s@ has no element whose low bits
-- match @(zeros, ones)@ on the contiguous-forced-prefix. The result is
-- always a subset of @s@ ('liftForcedBitsShrinks'), preserves every
-- element of @s@ that agrees with the forced bits on positions
-- @0..v - 1@ where @v@ is the lifted stride exponent
-- ('liftForcedBitsCompleteOnLowBits'), and any element of the result is
-- a member of @s@ whose forced positions agree with @(zeros, ones)@
-- ('liftForcedBitsMember').
--
-- This step beats projecting through 'fromBitwise' followed by
-- 'pseudoMeet': @fromBitwise@ produces a single progression whose stride
-- is set by the lowest /free/ bit of @b@, so forced bits /above/ a free
-- bit collapse on the projection. The lift consumes them one at a time
-- as stride doublings.
liftForcedBits ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  -- | @(zeros, ones)@ as produced by 'knownZerosOnesNat'.
  (Natural, Natural) ->
  Maybe (Domain w)
liftForcedBits w s (zeros, ones)
  -- Singleton: the orbit has one value; just check it.
  | n s == 0 =
      if (zeros .&. start s) == 0 && (ones .&. notN (start s)) == 0
        then Just s
        else Nothing
  -- @start@\'s low bits below @v@ are fixed across the whole orbit.
  -- Conflict with any forced bit there means the joint is empty.
  | (zeros .&. start s .&. lowMask) /= 0 = Nothing
  | (ones  .&. notN (start s) .&. lowMask) /= 0 = Nothing
  | otherwise = go s
  where
    m = mask s
    notN x = m `Bits.xor` x
    g = strideGcd s
    lowMask = g - 1  -- bits 0..v-1

    -- Walk the contiguous run of forced bits starting at position @v@.
    -- Each forced bit at the current stride boundary halves the orbit
    -- and doubles the stride.
    go !c
      | n c == 0 = Just c
      | otherwise =
          let v = strideGcd c
              stB = stride c
              vBitMask = v
              forcedZero = (zeros .&. vBitMask) /= 0
              forcedOne  = (ones  .&. vBitMask) /= 0
          in if Prelude.not (forcedZero || forcedOne)
               then Just c
               else
                 let startBitV = (start c .&. vBitMask) /= 0
                     -- Required parity of @i@ to match the bit-@v@ force.
                     wantOdd = case (forcedZero, forcedOne) of
                       (True, _)  -> startBitV
                       (_, True)  -> Prelude.not startBitV
                       _          -> error "liftForcedBits: unreachable"
                     newStride = (stB `shiftL` 1) .&. m
                     newStart =
                       if wantOdd
                         then (start c + stB) .&. m
                         else start c
                 in if newStride == 0
                      -- @stride@ doubles to @2^w mod 2^w = 0@: every step
                      -- lands back on the same value, so the result is a
                      -- singleton.
                      then Just (mk w newStart 1 0)
                      else
                        -- Number of valid @i@'s in @[0..n c]@:
                        --   wantOdd=False: i ∈ {0,2,...,N} → ⌊N\/2⌋+1
                        --   wantOdd=True : i ∈ {1,3,...}   → (N+1)\/2
                        -- @newN = count - 1@.
                        let newN =
                              if wantOdd
                                then (n c - 1) `Prelude.div` 2
                                else n c `Prelude.div` 2
                        in if wantOdd && n c == 0
                             then Nothing  -- only i=0 available, parity wrong
                             else go (mk w newStart newStride newN)

-- | /O(w log w)/, with the supplied 'compactify'-style merger. Intersect
-- a progression with the unsigned arc @[blo, bhi]@ (the unsigned bounds
-- of a 'B.Domain'). Above the contiguous run of forced bits
-- 'liftForcedBits' consumes, scattered forced bits aren\'t representable
-- as a stride lift, but they still show up in @b@\'s numeric bounds —
-- e.g. @b@ with bit 1 forced and bit 0 free at @w = 2@ has
-- @(blo, bhi) = (2, 3)@.
--
-- 'ssplit's the input at the unsigned pole and runs 'arcMeetClosed' on
-- each non-wrap piece, then folds with the supplied merger. Pass
-- 'compactify' for /O(w log w)/ overall, or 'compactifyPrecise' for an
-- /O(w^2)/ variant that catches one extra merge — two complementary
-- singletons whose union is a stride-@(2^w − 1)@ progression — that the
-- 'leq'-based 'compactify' misses since it lacks the singleton-on-orbit
-- containment check (kept out of 'leq' to preserve its /O(w)/ bound).
-- When the result splits into multiple progressions (because the input
-- wraps mod @2^w@ and the arc carves out two disjoint pieces), the input
-- is returned unchanged rather than over-approximating with a
-- single-progression cover.
--
-- /Skipped/ on self-wrapping inputs: 'ssplit' over-approximates them to
-- the full coset, which would break the subset guarantee. The caller
-- gets 'Just' the unmodified input in that case.
--
-- The result (when 'Just') is a subset of the input
-- ('arcClipBitwiseShrinks'); every input element in @[blo, bhi]@ is
-- preserved ('arcClipBitwiseMember').
arcClipBitwise ::
  (1 <= w) =>
  -- | 'compactify' or 'compactifyPrecise'
  (NatRepr w -> [Domain w] -> [Domain w]) ->
  NatRepr w ->
  Domain w ->
  -- | @(blo, bhi)@: an unsigned arc with @blo <= bhi <= mask@.
  (Natural, Natural) ->
  Maybe (Domain w)
arcClipBitwise compactifyOp w l (blo, bhi)
  -- 'ssplit' on a self-wrapping orbit over-approximates to the full
  -- coset — fine for over-approximating ops, but here the result would
  -- no longer be a subset of @l@. Skip the arc clip in that case.
  | isSelfWrapping l = Just l
  | otherwise =
      let arc = mk w blo 1 (bhi - blo)
          pieces = [ p | li <- ssplit w l
                       , Just p <- [arcMeetClosed w li arc] ]
      in case compactifyOp w pieces of
           []  -> Nothing
           [c] -> Just c
           -- Multiple pieces means @l@ wraps mod 2^w and @[blo, bhi]@
           -- carves out two disjoint arcs of @l@. A single-progression
           -- cover would over-approximate beyond @l@. Fall back to @l@.
           _   -> Just l

-- | /O(w log w)/. Refine a bitwise domain @b@ using a strides domain @s@.
--
-- Always at least as precise as @B.meet b (toBitwise s)@
-- ('refineBitsByStridesDominatesMeetToBitwise'), and strictly tighter on
-- some wrap-mod-@2^w@ inputs whose pieces are partly carved away by
-- @b@\'s arc.
--
-- == Why a piecewise extraction beats @toBitwise s@ directly
--
-- 'toBitwise' calls 'forcedBits', whose span-pinning clause requires
-- @2^k > n · stride@ to fix bit @k@. When @s@ wraps mod @2^w@, the
-- integer span is @>= 2^w@ and span pinning fixes /no/ high bits, even
-- though each non-wrap piece individually has a small span and
-- typically pins many high bits.
--
-- 'ssplit' decomposes @s@ at the unsigned pole into one or two non-wrap
-- pieces. On non-wrap pieces 'forcedBits' is bit-complete (every bit
-- constant across the piece is detected). Joining @toBitwise@ of the
-- pieces yields a bitwise domain dominated by @toBitwise s@ and
-- typically strictly tighter.
--
-- == Why pre-clipping each piece to @b@\'s arc helps further
--
-- Pieces disjoint from @b@\'s numeric bounds @[blo, bhi]@ contribute
-- nothing to the joint: dropping them removes per-bit disagreements
-- that 'B.join' would otherwise smear into \"free\". Pieces that
-- partially overlap shrink to the surviving sub-arc, so 'forcedBits'
-- pins more high bits on the smaller span.
--
-- == Self-wrap fallback
--
-- If @s@ is self-wrapping, 'ssplit' collapses it to the full coset; the
-- piecewise extraction matches @toBitwise s@ exactly, so we just take
-- the single-shot meet.
--
-- == Soundness
--
-- @gamma(s) = union of gamma(piece_i)@ ('ssplitUnion'); for each piece,
-- @gamma(piece) `subseteq` gamma(toBitwise piece)@ ('toBitwiseCorrect');
-- 'arcMeetClosed' on a non-wrap piece preserves every element in
-- @[blo, bhi]@; @B.join@\/@B.meet@ are sound. Hence
-- @gamma(s) `cap` gamma(b) `subseteq` gamma(result)@
-- ('correct_refineBitsByStrides').
--
-- == Example
--
-- @s@ wraps the unsigned pole; @b@ forces the top bit to 0:
--
-- >>> import qualified What4.Domains.BV.Bitwise as B
-- >>> let w8 = knownNat @8
-- >>> let s = mk w8 0xF0 1 0x1F  -- {0xF0..0xFF, 0x00..0x0F}
-- >>> let b = B.range w8 0 0x7F  -- top bit forced 0
-- >>> -- @toBitwise s@ is top (span = 0x1F crosses every high bit), so
-- >>> -- @B.meet b (toBitwise s)@ is just @b@. Per-piece extraction
-- >>> -- drops the high arc and tightens to @[0x00, 0x0F]@:
-- >>> fmap B.bitbounds (refineBitsByStrides w8 b s)
-- Just (0,15)
refineBitsByStrides ::
  (1 <= w) =>
  NatRepr w ->
  B.Domain w ->
  Domain w ->
  Maybe (B.Domain w)
refineBitsByStrides w b s
  | isSelfWrapping s =
      let b' = B.meet b (toBitwise s)
      in if B.isBottom b' then Nothing else Just b'
  | otherwise =
      let (bloI, bhiI) = B.bitbounds b
          blo  = integerToNatural bloI
          bhi  = integerToNatural bhiI
          arc  = mk w blo 1 (bhi - blo)
          -- 'ssplit' yields non-wrap pieces; 'arcMeetClosed' is
          -- well-defined on each.
          clipped =
            [ p' | p <- ssplit w s, Just p' <- [arcMeetClosed w p arc] ]
      in case clipped of
           []     -> Nothing
           c : cs ->
             let stridesB =
                   foldr (B.join . toBitwise) (toBitwise c) cs
                 b' = B.meet b stridesB
             in if B.isBottom b' then Nothing else Just b'

-- | /O(w log w)/. One round of mutual refinement of a strides\/bitwise
-- pair.
--
-- Refines the strides component using the bitwise component via
-- 'refineByBits' — a direct stride-lift plus arc clip that doesn\'t
-- detour through 'fromBitwise' or 'pseudoMeet'. Then refines the bitwise
-- component using the already-refined strides component via
-- 'refineBitsByStrides', which is at least as precise as
-- @B.meet b (toBitwise s')@ and strictly tighter on some wrap-mod-@2^w@
-- inputs. Returns 'Nothing' iff the joint represents an empty set.
--
-- Each component of the result is a subset of the corresponding input
-- component ('reduceStepShrinks'). When @x@ lies in both inputs, @x@ lies
-- in both outputs ('correct_reduceStep') — refinement only drops witnesses
-- that the /other/ component already excluded.
--
-- == Example
--
-- evens × \"bit 1 forced to 1\" reduces to the exact joint @{2, 6, 10, 14}@:
--
-- >>> import qualified What4.Domains.BV.Bitwise as B
-- >>> let evens = mk4 0 2 7
-- >>> let bm = B.range w4 0b0010 0b1111
-- >>> :{
-- fmap (\(s, b) -> (display s, B.bitbounds b))
--      (reduceStep w4 evens bm)
-- :}
-- Just ("[..*...*...*...*.]  = [2,6,10,14]",(2,14))
reduceStep ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  B.Domain w ->
  Maybe (Domain w, B.Domain w)
reduceStep w s b
  -- Bitwise bottom: @b@ is empty, so the joint is empty. Short-circuit
  -- before 'refineByBits' would compute @bhi - blo@ on the canonical
  -- bottom @(mask, 0)@ and underflow on 'Natural'.
  | B.isBottom b = Nothing
  | otherwise = do
      s' <- refineByBits w s b
      b' <- refineBitsByStrides w b s'
      Just (s', b')

-- | /O(w log w)/. Apply 'reduceStep' at most a small constant number of
-- times. Each step strictly reduces one component on a non-fixpoint
-- iteration, so a true fixpoint is reached in at most @O(w)@ steps;
-- capping to a constant turns this into a /widening/: the result is
-- sound but not necessarily fully-reduced. This keeps every reduced-
-- product operation at the same asymptotic cost as its underlying
-- components, which matters more in practice than fully closing the
-- lattice. Use 'reduceFixpoint' when you actually need the closed form.
reduce ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  B.Domain w ->
  Maybe (Domain w, B.Domain w)
reduce w = go (3 :: Int)
  where
    go 0 s b = Just (s, b)
    go n s b = do
      (s', b') <- reduceStep w s b
      if s' == s && b' == b
        then Just (s, b)
        else go (n - 1) s' b'

-- | /O(w^2 log w)/. Iterate 'reduceStep' to a true fixed point. Each
-- non-trivial step strictly reduces 'size' of one component, so the loop
-- runs at most @O(w)@ times before stabilizing. Prefer 'reduce' in
-- per-operation hot paths; this is for tests and callers that actually
-- need the closed form.
reduceFixpoint ::
  (1 <= w) =>
  NatRepr w ->
  Domain w ->
  B.Domain w ->
  Maybe (Domain w, B.Domain w)
reduceFixpoint w = go
  where
    go s b = do
      (s', b') <- reduceStep w s b
      if s' == s && b' == b
        then Just (s, b)
        else go s' b'

-- ------------------------------------------------------------------
-- * Generators

-- | Generator for a proper 'Domain' at width @w@.
genDomain :: NatRepr w -> Gen (Domain w)
genDomain w = do
  let m = integerToNatural (maxUnsigned w)
  s <- integerToNatural <$> chooseInteger (0, toInteger m)
  -- Stride must be in @[1, 2^w - 1]@; we pick from @[1, 2^w]@ and clamp by mask
  -- so that stride is uniformly distributed over [1, 2^w-1] (a stride of 2^w
  -- mod mask = 0 would be improper).
  st <- integerToNatural <$> chooseInteger (1, toInteger m)
  -- Pick a step count @i@ in @[0, orbit)@, where @orbit = 2^w \/ g@ and
  -- @g = gcd(stride, 2^w)@.
  let g = st .&. ((m + 1) - st)
  let orbit = (m + 1) `divByPow2` g
  i <- integerToNatural <$> chooseInteger (0, toInteger orbit - 1)
  pure (mk w s st i)

-- | Generate a random element of the given (proper) progression.
genElement :: Domain w -> Gen Natural
genElement c = do
  i <- integerToNatural <$> chooseInteger (0, toInteger (n c))
  pure (valueAt c i)

-- | Generate a random progression and an element contained in it.
genPair :: NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  c <- genDomain w
  x <- genElement c
  pure (c, x)

-- ------------------------------------------------------------------
-- * Properties

-- ------------------------------------------------------------------
-- ** Internal helpers

-- | @x + modNeg (2^k - 1) x ≡ 0 (mod 2^k)@.
modNegCorrect :: Natural -> Int -> Property
modNegCorrect x k =
  k >= 1 ==> property ((x' + modNeg m x') .&. m == 0)
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | @modSub (2^k - 1) x y + y ≡ x (mod 2^k)@.
modSubCorrect :: Natural -> Natural -> Int -> Property
modSubCorrect x y k =
  k >= 1 ==> property ((modSub m x' y' + y') .&. m == x')
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m
    y' = y .&. m

-- | At width @k@ with @g = 2^j@ (@j ≤ k@): the result @v = firstCosetMember
-- (2^k - 1) lo g x@ is in the @g@-coset of @x@ (i.e. @(v - x) mod g == 0@),
-- and the wrap-around offset @(v - lo) mod 2^k@ is less than @g@ (so @v@ is
-- the /first/ such value at or after @lo@ on the wrapped arc).
firstCosetMemberCorrect :: Natural -> Natural -> Int -> Int -> Property
firstCosetMemberCorrect lo x k j =
  k >= 1 ==> j >= 0 ==> j <= k ==>
    property ((modSub m v x' .&. (g - 1) == 0)
           && (modSub m v lo' < g))
  where
    m   = (1 `shiftL` k) - 1
    g   = 1 `shiftL` j
    lo' = lo .&. m
    x'  = x .&. m
    v   = firstCosetMember m lo' g x'

-- | @start + wrapOffset c v ≡ v (mod 2^w)@.
wrapOffsetCorrect :: Domain w -> Natural -> Property
wrapOffsetCorrect c v =
  proper c ==>
    property (modMask c (start c + wrapOffset c v) == modMask c v)

-- | @strideGcd c@ divides @stride c@ and divides @2^w@.
strideGcdDividesStride :: Domain w -> Property
strideGcdDividesStride c =
  proper c ==>
    property (stride c `mod` strideGcd c == 0
           && (mask c + 1) `mod` strideGcd c == 0)

-- | @strideGcd c@ is a power of two (i.e. @g .&. (g - 1) == 0@).
strideGcdIsPow2 :: Domain w -> Property
strideGcdIsPow2 c =
  proper c ==> property (g > 0 && g .&. (g - 1) == 0)
  where g = strideGcd c

-- | 'orbitLen' upper-bounds the length of 'toList': it equals the number of
-- distinct values reachable from @start@ by stepping by @stride@, while
-- 'toList' stops early at @end@.
orbitLenViaToList :: Domain w -> Property
orbitLenViaToList c =
  proper c ==> property (fromIntegral (length (toList c)) <= orbitLen c)

-- | @divByPow2 (q * 2^k) (2^k) == q@.
divByPow2Correct :: Natural -> Int -> Property
divByPow2Correct q k =
  k >= 0 ==> property (divByPow2 (q * p) p == q)
  where p = 1 `shiftL` k

-- | @(a * invModPow2 a (2^k)) ≡ 1 (mod 2^k)@ for odd @a@ and @k >= 1@.
invModPow2Correct :: Natural -> Int -> Property
invModPow2Correct a k =
  k >= 1 ==> a `mod` 2 == 1 ==>
    property ((a * invModPow2 a m) `mod` m == 1)
  where m = 1 `shiftL` k

-- | 'floorSum' agrees with the naive sum:
-- @floorSum n m a b == sum_{i=0}^{n-1} ((a*i + b) \`Prelude.div\` m)@.
-- @n@, @a@, @b@ are clamped to small ranges to keep the naive sum cheap.
floorSumCorrect :: Natural -> Natural -> Natural -> Natural -> Property
floorSumCorrect n m a b =
  m' > 0 ==>
    property (floorSum n' m' a' b' == naive)
  where
    n' = n `mod` 64
    m' = (m `mod` 32) + 1
    a' = a `mod` 64
    b' = b `mod` 64
    naive = sum [ (a' * i + b') `Prelude.div` m'
                | n' > 0, i <- [0 .. n' - 1] ]

-- | @valueAt c (valueIndex c v) ≡ v (mod 2^w)@ whenever @v@ is on the
-- progression (i.e. @strideGcd c@ divides @wrapOffset c v@).
valueIndexCorrect :: Domain w -> Natural -> Property
valueIndexCorrect c v =
  proper c ==> wrapOffset c v' `mod` strideGcd c == 0 ==>
    property (valueAt c (valueIndex c v') == v')
  where v' = modMask c v

-- | 'valueIndexMaybe' returns 'Just' iff @v@ is on @c@\'s coset, and the
-- payload agrees with 'valueIndex'.
valueIndexMaybeCorrect :: Domain w -> Natural -> Property
valueIndexMaybeCorrect c v =
  proper c ==>
    let v' = modMask c v
        onCoset = wrapOffset c v' `mod` strideGcd c == 0
    in property $ case valueIndexMaybe c v' of
         Just i  -> onCoset && i == valueIndex c v'
         Nothing -> Prelude.not onCoset

-- | @valueIndex c (valueAt c i) == i@ for any @i@ in @[0, orbitLen c)@.
valueAtCorrect :: Domain w -> Natural -> Property
valueAtCorrect c i =
  proper c ==>
    let i' = i `mod` orbitLen c in
    property (valueIndex c (valueAt c i') == i')

-- | @circLeq m 0@ degenerates to ordinary unsigned @<=@.
circLeqAtZero :: Natural -> Natural -> Int -> Property
circLeqAtZero a b k =
  k >= 1 ==> property (circLeq m 0 a' b' == (a' <= b'))
  where
    m  = (1 `shiftL` k) - 1
    a' = a .&. m
    b' = b .&. m

-- | The anchor @x@ is the minimum: @circLeq m x x v@ always holds.
circLeqAnchorMin :: Natural -> Natural -> Int -> Property
circLeqAnchorMin x v k =
  k >= 1 ==> property (circLeq m (x .&. m) (x .&. m) (v .&. m))
  where m = (1 `shiftL` k) - 1

-- | The predecessor of @x@ is the maximum: @circLeq m x v (x - 1)@ always holds.
circLeqAnchorMax :: Natural -> Natural -> Int -> Property
circLeqAnchorMax x v k =
  k >= 1 ==>
    property (circLeq m x' (v .&. m) ((x' + m) .&. m))
  where
    m  = (1 `shiftL` k) - 1
    x' = x .&. m

-- | 'isSelfWrapping' agrees with the orbit length: a progression is self-wrapping iff
-- stepping through every element of 'toList' travels strictly more than @2^w@
-- in total. Concretely, @isSelfWrapping c@ iff
-- @(length (toList c) - 1) * stride > 2^w - 1@.
isSelfWrappingViaToList :: Domain w -> Property
isSelfWrappingViaToList c@Domain{stride, mask} =
  proper c ==> property (isSelfWrapping c == (k * stride > mask))
  where
    k = fromIntegral (length (toList c) - 1) :: Natural

-- ------------------------------------------------------------------
-- ** Construction

-- | /Soundness of 'fromAscEltList'/: every element of an ascending,
-- distinct, in-range input list is a member of the resulting progression.
fromAscEltListMember :: (1 <= w) => NatRepr w -> [Natural] -> Property
fromAscEltListMember w xs =
  ascendingDistinctInRange ==>
    case fromAscEltList w xs of
      Nothing -> property (null xs)
      Just c  -> property (Prelude.all (member c) xs)
  where
    m = integerToNatural (maxUnsigned w)
    inRange = Prelude.all (\x -> x .&. m == x)
    strictlyAscending ys = Prelude.and (zipWith (<) ys (drop 1 ys))
    ascendingDistinctInRange = inRange xs && strictlyAscending xs

-- | /Round-trip exactness on monotonic orbits/: for a progression @c@ whose
-- orbit doesn't cross @0@ (@start + n·stride < 2^w@), 'toList' is already
-- sorted as a regular AP with step @stride c@, so the gcd of consecutive
-- differences is exactly @stride c@ and the recovered progression has the
-- same elements as @c@.
fromAscEltListToListExactNonWrapping ::
  (1 <= w) => NatRepr w -> Domain w -> Property
fromAscEltListToListExactNonWrapping w c =
  proper c ==> orbitDoesNotCrossZero ==>
    case fromAscEltList w (List.sort (toList c)) of
      Nothing -> property False
      Just c' -> property (leqExact c c' && leqExact c' c)
  where
    orbitDoesNotCrossZero = start c + n c * stride c <= mask c

-- ------------------------------------------------------------------
-- ** Canonicalization

-- | 'canonicalize' denotes the same set as its input.
canonLossless :: Domain w -> Property
canonLossless c = proper c ==> property (eqExact (getCanonical (canonicalize c)) c)

-- | 'canonicalize' produces a 'proper' representation.
canonProper :: Domain w -> Property
canonProper c = proper c ==> property (proper (getCanonical (canonicalize c)))

-- | The hash-consing property: equal sets have equal canonical forms. This is
-- what makes 'eq' (O(1)\/O(w) equality after canonicalization) sound.
canonUnique :: Domain w -> Domain w -> Property
canonUnique a b =
  proper a ==> proper b ==> mask a == mask b ==> eqExact a b ==>
    property (canonicalize a == canonicalize b)

-- | 'canonicalize' is idempotent (re-canonicalizing the underlying form is a
-- no-op).
canonIdempotent :: Domain w -> Property
canonIdempotent c =
  proper c ==>
    property (canonicalize (getCanonical (canonicalize c)) == canonicalize c)

-- | 'eq' (canonical-form equality) agrees with the 'eqExact' oracle, hence
-- decides exact set equality.
eqCorrect :: Domain w -> Domain w -> Property
eqCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eq a b == eqExact a b)

-- | The minimal-stride rule subsumes a separate orientation tie-break: the
-- canonical form never has stride strictly greater than its reverse (except in
-- the full-coset regime, which 'mk' already pins).
canonForwardOriented :: Domain w -> Property
canonForwardOriented c =
  proper c ==>
    property (stride cc <= modNeg (mask cc) (stride cc)
              || n cc + 1 == orbitLen cc)
  where cc = getCanonical (canonicalize c)

-- | The @O(w)@ 'canonicalize' formula agrees with an exhaustive search over all
-- 'proper' representations (lex-least by stride, then start, then n).
canonMatchesSearch :: (1 <= w) => NatRepr w -> Domain w -> Property
canonMatchesSearch w c =
  proper c ==> property (getCanonical (canonicalize c) == canonicalizeSearch w c)

-- | The 'Hashable' instance for 'Canonical' respects its 'Eq': equal canonical
-- forms (i.e. equal denoted sets) hash equally, the law required for
-- 'Canonical' to be a sound hash-cons\/memo key. Combined with 'canonUnique'
-- this means set-equal progressions hash equally.
canonHashRespectsEq :: Domain w -> Domain w -> Property
canonHashRespectsEq a b =
  proper a ==> proper b ==> mask a == mask b ==>
    canonicalize a == canonicalize b ==>
      property (hash (canonicalize a) == hash (canonicalize b))

-- | Reference implementation of 'canonicalize': the lex-least (by stride, then
-- start, then n) 'proper' progression denoting the same set as @c@. Exponential
-- in @w@; used only to validate the @O(w)@ 'canonicalize'.
canonicalizeSearch :: (1 <= w) => NatRepr w -> Domain w -> Domain w
canonicalizeSearch w c =
  List.foldl' pick c
    [ d
    | st <- [1 .. m]
    , s  <- [0 .. m]
    , let g = lowestSetBit st
    , nv <- [0 .. orbitLenOf m g - 1]
    , let d = Domain { start = s, stride = st, n = nv, mask = m }
    , proper d
    , eqExact d c
    ]
  where
    m = integerToNatural (maxUnsigned w)
    pick best d = if lexLt d best then d else best
    lexLt x y =
      (stride x, start x, n x) < (stride y, start y, n y)

-- ------------------------------------------------------------------
-- ** Conversion

-- | Every element in a progression is also in its 'toArith' conversion.
toArithCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toArithCorrect _w c x =
  proper c ==> member c x' ==>
    property (A.member (toArith c) (toInteger x'))
  where
    x' = modMask c x

-- | On non-self-wrapping progressions, every orbit member lies in 'startEndArc'.
startEndArcCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
startEndArcCorrect _w c x =
  proper c ==> Prelude.not (isSelfWrapping c) ==> member c x' ==>
    property (A.member (startEndArc c) (toInteger x'))
  where
    x' = modMask c x

-- | On self-wrapping progressions, every orbit member lies in 'cosetArc'.
cosetArcCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
cosetArcCorrect _w c x =
  proper c ==> isSelfWrapping c ==> member c x' ==>
    property (A.member (cosetArc c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in an arithmetic domain is also in its 'fromArith' conversion
-- (when that conversion produces a progression).
fromArithCorrect :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
fromArithCorrect w a x =
  A.proper w a ==> A.member a x ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- | Converting from Arith to a progression and back is exact: the round-tripped domain
-- contains exactly the same elements as the original.
roundtripArith :: (1 <= w) => NatRepr w -> A.Domain w -> Integer -> Property
roundtripArith w a x =
  A.proper w a ==>
    case fromArith w a of
      Nothing -> property True
      Just c -> property (A.member a x == A.member (toArith c) x)

-- | Every element in a progression is also in its 'toBitwise' conversion.
toBitwiseCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
toBitwiseCorrect _w c x =
  proper c ==> member c x' ==>
    property (B.member (toBitwise c) (toInteger x'))
  where
    x' = modMask c x

-- | Every element in a progression is also in its 'strideBitwise'
-- conversion (i.e., shares its low @v@ bits with @start@, where
-- @stride = 2^v · m@ for odd @m@).
strideBitwiseCorrect :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
strideBitwiseCorrect _w c x =
  proper c ==> member c x' ==>
    property (B.member (strideBitwise c) (toInteger x'))
  where
    x' = modMask c x

-- | The two halves of 'forcedBits' are bit-disjoint: no bit is both
-- forced-to-0 and forced-to-1.
forcedBitsDisjoint :: Domain w -> Property
forcedBitsDisjoint c =
  proper c ==>
    let (zeros, ones) = forcedBits c
    in property ((zeros .&. ones) == 0)

-- | Every element of a progression agrees with the forced-bits picture:
-- bits in @zeros@ are @0@ in @x@; bits in @ones@ are @1@ in @x@.
forcedBitsMember :: Domain w -> Natural -> Property
forcedBitsMember c x =
  proper c ==> member c x' ==>
    let (zeros, ones) = forcedBits c
    in property ((zeros .&. x') == 0
              && (ones .&. (mask c `Bits.xor` x')) == 0)
  where
    x' = modMask c x

-- | 'fromForcedBits' covers: every value that agrees with the forced bits
-- and lies in the interval is a member of the result.
--
-- The raw draws are normalized inside the property — @zeros@ is made
-- disjoint from @ones@, @x@ is rewritten to agree with both, and the
-- interval endpoints are ordered — so that only @x@'s interval membership
-- remains as a real precondition.
fromForcedBitsCorrect ::
  (1 <= w) =>
  NatRepr w ->
  Natural -> Natural -> Natural -> Natural -> Natural -> Property
fromForcedBitsCorrect w zRaw oRaw loRaw hiRaw xRaw =
  lo <= x ==> x <= hi ==>
    property (member (fromForcedBits w (zeros, ones) (lo, hi)) x)
  where
    m     = integerToNatural (maxUnsigned w)
    ones  = oRaw .&. m
    zeros = zRaw .&. m .&. (m `Bits.xor` ones)
    x     = ((xRaw .&. m) .&. (m `Bits.xor` zeros)) Bits..|. ones
    lo    = min (loRaw .&. m) (hiRaw .&. m)
    hi    = max (loRaw .&. m) (hiRaw .&. m)

-- | 'fromForcedBitsSigned' covers: every value that agrees with the forced
-- bits and whose /signed/ value lies in the interval is a member of the
-- result. Raw draws are normalized as in 'fromForcedBitsCorrect', with the
-- interval endpoints read as signed values.
fromForcedBitsSignedCorrect ::
  (1 <= w) =>
  NatRepr w ->
  Natural -> Natural -> Natural -> Natural -> Natural -> Property
fromForcedBitsSignedCorrect w zRaw oRaw loRaw hiRaw xRaw =
  lo <= xS ==> xS <= hi ==>
    property (member (fromForcedBitsSigned w (zeros, ones) (lo, hi)) x)
  where
    m     = integerToNatural (maxUnsigned w)
    ones  = oRaw .&. m
    zeros = zRaw .&. m .&. (m `Bits.xor` ones)
    x     = ((xRaw .&. m) .&. (m `Bits.xor` zeros)) Bits..|. ones
    xS    = toSigned w (toInteger x)
    loS   = toSigned w (toInteger (loRaw .&. m))
    hiS   = toSigned w (toInteger (hiRaw .&. m))
    lo    = min loS hiS
    hi    = max loS hiS

-- | Every element in a bitwise domain is also in its 'fromBitwise' conversion
-- (when that conversion produces a progression).
fromBitwiseCorrect :: (1 <= w) => NatRepr w -> B.Domain w -> Integer -> Property
fromBitwiseCorrect w b x =
  B.proper w b ==> B.member b x ==>
    case fromBitwise w b of
      Nothing -> property True
      Just c -> property (member c (integerToNatural (x .&. maxUnsigned w)))

-- ------------------------------------------------------------------
-- ** Queries

-- | A progression always contains its own @start@.
startMember :: Domain w -> Property
startMember c = proper c ==> property (member c (start c))

-- | A progression always contains its own @end@.
endMember :: Domain w -> Property
endMember c = proper c ==> property (member c (end c))

-- | Every element produced by 'toList' is a member of the progression.
toListMember :: Domain w -> Property
toListMember c =
  proper c ==> property (Prelude.all (member c) (toList c))

-- | If 'member' returns 'True' for some bitvector @x@, then @x@ appears in
-- 'toList'.
memberToList :: Domain w -> Natural -> Property
memberToList c x =
  proper c ==> (member c x' ==> property (x' `elem` toList c))
  where x' = modMask c x

-- | 'toList' produces no duplicate elements.
toListNoDuplicates :: Domain w -> Property
toListNoDuplicates c = proper c ==> property (noDuplicates (toList c))
  where
    noDuplicates xs = length xs == Set.size (Set.fromList xs)

-- | Soundness of 'leq': if @a \`leq\` b@ then every element of @a@ is in @b@.
leqCorrect :: Domain w -> Domain w -> Property
leqCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leq a b ==> property (Prelude.all (member b) (toList a))

-- | 'leq' is reflexive.
leqReflexive :: Domain w -> Property
leqReflexive a = proper a ==> property (leq a a)

-- | 'leq' is transitive: if @a \`leq\` b@ and @b \`leq\` c@ then
-- @a \`leq\` c@. (Both 'leqPrecise' and 'leqExact' are reflexive but not
-- guaranteed transitive at the syntactic level; only 'leq' is.)
leqTransitive :: Domain w -> Domain w -> Domain w -> Property
leqTransitive a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      leq a b ==> leq b c ==> property (leq a c)

-- | 'leq' refines 'leqExact': @leq a b ==> leqExact a b@. ('leq' and
-- 'leqPrecise' are not comparable in general — neither refines the other.)
leqRefinesLeqExact :: Domain w -> Domain w -> Property
leqRefinesLeqExact a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leq a b ==> property (leqExact a b)

-- | Soundness of 'leqPrecise': if @a \`leqPrecise\` b@ then every element
-- of @a@ is in @b@.
leqPreciseCorrect :: Domain w -> Domain w -> Property
leqPreciseCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leqPrecise a b ==> property (Prelude.all (member b) (toList a))

-- | 'leqPrecise' is reflexive.
leqPreciseReflexive :: Domain w -> Property
leqPreciseReflexive a = proper a ==> property (leqPrecise a a)

-- | 'leqPrecise' refines 'leqExact': @leqPrecise a b ==> leqExact a b@.
-- Equivalently, 'leqPrecise' is a sound approximation of the semantic
-- containment that 'leqExact' decides.
leqPreciseRefinesLeqExact :: Domain w -> Domain w -> Property
leqPreciseRefinesLeqExact a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leqPrecise a b ==> property (leqExact a b)

-- | Soundness of 'leqExact': @leqExact a b@ implies every element of @a@ is
-- in @b@.
leqExactCorrect :: Domain w -> Domain w -> Property
leqExactCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    leqExact a b ==> property (Prelude.all (member b) (toList a))

-- | Completeness of 'leqExact': if every element of @a@ is in @b@, then
-- @leqExact a b@. Together with 'leqExactCorrect' this says @leqExact@
-- decides semantic containment exactly.
leqExactComplete :: Domain w -> Domain w -> Property
leqExactComplete a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.all (member b) (toList a) ==> property (leqExact a b)

-- | 'leqExact' is reflexive.
leqExactReflexive :: Domain w -> Property
leqExactReflexive a = proper a ==> property (leqExact a a)

-- | 'leqExact' is transitive: if @a \`leqExact\` b@ and @b \`leqExact\` c@
-- then @a \`leqExact\` c@.
leqExactTransitive :: Domain w -> Domain w -> Domain w -> Property
leqExactTransitive a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      leqExact a b ==> leqExact b c ==> property (leqExact a c)

-- | 'leqExactPartial' is exact wherever it is defined: when it returns
-- @Just r@, that @r@ matches semantic containment (every element of @a@ is in
-- @b@). Compared against membership directly, not against 'leqExact', since
-- 'leqExact' is /defined/ in terms of 'leqExactPartial' and so would make the
-- check vacuous on the @Just@ branch. (On 'Nothing' the partial check
-- declines, and 'leqExact' falls back to 'leqExactWindow'.)
leqExactPartialAgrees :: Domain w -> Domain w -> Property
leqExactPartialAgrees a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case leqExactPartial a b of
      Just r  -> property (r == Prelude.all (member b) (toList a))
      Nothing -> property True

-- | 'leqExactWindow' decides the 'leqExactPartial' 'Nothing' case correctly:
-- on the inputs where the partial check declines, the window count matches
-- semantic containment. Together with 'leqExactPartialAgrees' this validates
-- both arms of 'leqExact' against membership independently.
leqExactWindowAgrees :: Domain w -> Domain w -> Property
leqExactWindowAgrees a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case leqExactPartial a b of
      Just _  -> property True
      Nothing -> property (leqExactWindow a b == Prelude.all (member b) (toList a))

-- | 'size' agrees with the length of 'toList'.
sizeViaToList :: Domain w -> Property
sizeViaToList c =
  proper c ==> property (size c == fromIntegral (length (toList c)))

-- | Soundness of 'cosetsDisjoint': if it returns 'True', then @a@ and @b@
-- share no values. The contrapositive is the useful direction here — any
-- shared element witnesses non-disjoint cosets.
cosetsDisjointCorrect :: Domain w -> Domain w -> Natural -> Property
cosetsDisjointCorrect a b x =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x' ==> member b x' ==>
      property (Prelude.not (cosetsDisjoint a b))
  where
    x' = modMask a x

-- | Soundness of 'eqExact': it agrees with set equality of the orbits.
eqExactCorrect :: Domain w -> Domain w -> Property
eqExactCorrect a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqExact a b == (Set.fromList (toList a) == Set.fromList (toList b)))

-- | 'eqExact' is reflexive.
eqExactReflexive :: Domain w -> Property
eqExactReflexive a = proper a ==> property (eqExact a a)

-- | 'eqExact' is symmetric.
eqExactSymmetric :: Domain w -> Domain w -> Property
eqExactSymmetric a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqExact a b == eqExact b a)

-- | 'eqExact' is transitive.
eqExactTransitive :: Domain w -> Domain w -> Domain w -> Property
eqExactTransitive a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask b == mask c ==>
      eqExact a b ==> eqExact b c ==> property (eqExact a c)

-- ------------------------------------------------------------------
-- ** Arithmetic

correct_neg :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w c x =
  proper c ==> member c x ==>
    property (member (negate w c) (asN w (Prelude.negate (toInteger x))))

correct_add ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_add w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (add w a b) (asN w (toInteger x + toInteger y)))

correct_sub ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sub w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sub w a b) (asN w (toInteger x - toInteger y)))

-- | 'reverseD' denotes exactly the same set as its argument: the orbit walked
-- backwards visits the same values. This is what makes the orientation-robust
-- 'add'\/'sub'\/'mul' sound — both representatives abstract the same set.
reverseDSameSet :: (1 <= w) => NatRepr w -> Domain w -> Property
reverseDSameSet w c =
  proper c ==>
    property (Set.fromList (toList (reverseD w c)) == Set.fromList (toList c))

-- | Every piece returned by 'psplit' is 'proper'.
psplitProper :: (1 <= w) => NatRepr w -> Domain w -> Property
psplitProper w c =
  proper c ==> property (all proper (psplit w c))

-- | Every member of a 'psplit' piece is a member of the original.
psplitCovers :: (1 <= w) => NatRepr w -> Domain w -> Property
psplitCovers w c =
  proper c ==>
    property (Set.unions (map (Set.fromList . toList) (psplit w c))
              `Set.isSubsetOf` Set.fromList (toList c))

-- | The pieces returned by 'psplit' partition the original set: their
-- elementwise union equals the original, and they cover it without omission.
psplitPartitions :: (1 <= w) => NatRepr w -> Domain w -> Property
psplitPartitions w c =
  proper c ==>
    property (Set.unions (map (Set.fromList . toList) (psplit w c))
              == Set.fromList (toList c))

-- | 'psplitOp2' is sound for any sound binary operation: every concrete
-- @x \`op\` y@ for @x ∈ a, y ∈ b@ is in the abstract result. We verify this
-- by specializing to 'andFast' (a known-sound binary op): @x .&. y ∈ psplitOp2
-- (andFast w) a b@.
psplitOp2Sound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
psplitOp2Sound w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (psplitOp2 w (andFast w) a b) (x Bits..&. y))

correct_scale ::
  (1 <= w) =>
  NatRepr w -> Integer -> Domain w -> Natural -> Property
correct_scale w k c x =
  proper c ==> member c x ==>
    property (member (scale w k c) (asN w (k * toInteger x)))

correct_mul ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (mul w a b) (asN w (toInteger x * toInteger y)))

-- | The closed-form 'addSubSize' equals the materialized size of 'addRaw' (and,
-- since @start'@ doesn\'t affect the count, of 'subRaw') at /every/ orientation
-- pair. This is what lets 'orientRobustAddSub' score orientations without
-- building each candidate.
addSubSizeCorrect ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
addSubSizeCorrect w a b =
  proper a ==> proper b ==>
    property (Prelude.and
      [ addSubSize (mask a) (n ai) (stride ai) (n bj) (stride bj)
          == size (addRaw w ai bj)
        && addSubSize (mask a) (n ai) (stride ai) (n bj) (stride bj)
          == size (subRaw w ai bj)
      | ai <- orientationsOf a, bj <- orientationsOf b ])
  where
    orientationsOf c = let r = reverseD w c in if r == c then [c] else [c, r]

-- | The closed-form orientation picker 'orientRobustAddSub' produces a result
-- of the same size as the brute-force 'orientRobust' (which materializes all
-- four orientations). Sizes — not the domains themselves — because distinct
-- orientations can tie on size while differing in @start@; 'add' breaks the tie
-- toward the forward orientation, 'orientRobust' toward whichever 'foldl1''
-- visits first, and both are equally precise.
addRobustClosedFormAgrees ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
addRobustClosedFormAgrees w a b =
  proper a ==> proper b ==>
    property (size (add w a b) == size (orientRobust w (addRaw w) a b)
           && size (sub w a b) == size (orientRobust w (subRaw w) a b))

-- | The orientation-robust 'add' is never larger than the single-orientation
-- 'addRaw': trying both representatives and keeping the cardinality-minimum can
-- only help.
addRobustDominatesRaw ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
addRobustDominatesRaw w a b =
  proper a ==> proper b ==>
    property (size (add w a b) <= size (addRaw w a b))

-- | The orientation-robust 'sub' is never larger than the single-orientation
-- 'subRaw'.
subRobustDominatesRaw ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
subRobustDominatesRaw w a b =
  proper a ==> proper b ==>
    property (size (sub w a b) <= size (subRaw w a b))

-- | The orientation-robust 'mul' is never larger than the single-orientation
-- 'mulRaw'.
mulRobustDominatesRaw ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
mulRobustDominatesRaw w a b =
  proper a ==> proper b ==>
    property (size (mul w a b) <= size (mulRaw w a b))


correct_mulCorners ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulCorners w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (mulCorners w a b) (asN w (toInteger x * toInteger y)))

-- | 'mulNoStraddleU' is sound on inputs that don't straddle the unsigned
-- boundary (its precondition, met by 'cut' pieces): every concrete product
-- lies in the result. We restrict to 'cut' outputs here so the precondition
-- holds.
correct_mulNoStraddleU ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulNoStraddleU w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (Prelude.and
      [ member (mulNoStraddleU w u v) (asN w (toInteger x * toInteger y))
      | u <- cut w a, member u x
      , v <- cut w b, member v y
      ])

-- | 'mulNoStraddleS' is sound on inputs that don't straddle the signed
-- boundary (met by 'cut' pieces).
correct_mulNoStraddleS ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mulNoStraddleS w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (Prelude.and
      [ member (mulNoStraddleS w u v) (asN w (toInteger x * toInteger y))
      | u <- cut w a, member u x
      , v <- cut w b, member v y
      ])

-- | 'scaleSingleton' is sound: @{k} × c = (k·s, k·t, n) mod 2^w@ contains
-- every concrete product @k · y@ for @y \in c@.
correct_scaleSingleton ::
  (1 <= w) =>
  NatRepr w -> Natural -> Domain w -> Natural -> Property
correct_scaleSingleton w k c y =
  proper c ==> member c y ==>
    property (member (scaleSingleton w k' c) (asN w (toInteger k' * toInteger y)))
  where
    k' = k Bits..&. mask c

-- | 'zboundsArc' returns an integer arc that represents the same modular
-- set as the operand: the arc-length matches @n · stride@, and the result's
-- @lo@ differs from @start@ by a multiple of @2^w@.
zboundsArcSameModular :: Domain w -> Property
zboundsArcSameModular c =
  proper c ==>
    let !(lo, hi) = zboundsArc c
        !sz = toInteger (n c) * toInteger (stride c)
        !modulus = toInteger (mask c) + 1
    in property (hi - lo == sz
              && (lo - toInteger (start c)) `Prelude.mod` modulus == 0)

-- | 'zboundsArc' picks the representative whose midpoint is closer to zero
-- (or at least no farther than the unsigned representative's midpoint).
zboundsArcMinMidpoint :: Domain w -> Property
zboundsArcMinMidpoint c =
  proper c ==>
    let !(lo, hi) = zboundsArc c
        !uLo = toInteger (start c)
        !uHi = uLo + toInteger (n c) * toInteger (stride c)
    in property (Prelude.abs (lo + hi) <= Prelude.abs (uLo + uHi))

-- | 'cornerArc' encloses every concrete product of the bilinear form: for
-- @0 ≤ i ≤ n_a, 0 ≤ j ≤ n_b@, @lo ≤ (al + i·t1)(bl + j·t2) ≤ hi@ as
-- integers. Tested with @al, bl@ from 'zboundsArc' (so non-self-wrapping
-- operands).
cornerArcEncloses ::
  Domain w -> Domain w -> Natural -> Natural -> Property
cornerArcEncloses a b i j =
  proper a ==> proper b ==>
    Prelude.not (isSelfWrapping a) ==> Prelude.not (isSelfWrapping b) ==>
    i <= n a ==> j <= n b ==>
      let !(al, ah) = zboundsArc a
          !(bl, bh) = zboundsArc b
          !(lo, hi) = cornerArc al ah bl bh
          !p = (al + toInteger i * toInteger (stride a))
             * (bl + toInteger j * toInteger (stride b))
      in property (lo <= p && p <= hi)

-- | 'cornerProductStride' divides every concrete product's offset from the
-- anchor @al·bl@: for @0 ≤ i ≤ n_a, 0 ≤ j ≤ n_b@,
-- @cornerProductStride@ divides @(al + i·t1)(bl + j·t2) − al·bl@.
cornerProductStrideDivides ::
  Domain w -> Domain w -> Natural -> Natural -> Property
cornerProductStrideDivides a b i j =
  proper a ==> proper b ==>
    Prelude.not (isSelfWrapping a) ==> Prelude.not (isSelfWrapping b) ==>
    i <= n a ==> j <= n b ==>
      let !(al, _ah) = zboundsArc a
          !(bl, _bh) = zboundsArc b
          !d = cornerProductStride a b al bl
          !p = (al + toInteger i * toInteger (stride a))
             * (bl + toInteger j * toInteger (stride b))
          !offset = p - al * bl
      in property (d == 0 && offset == 0
                || d /= 0 && offset `Prelude.mod` d == 0)

-- | 'clpStepBound' is a sound upper bound on the number of stride-@d@ steps
-- between any concrete product and the anchor: for every @0 ≤ i ≤ n_a@,
-- @0 ≤ j ≤ n_b@, @|product − al·bl| / d ≤ clpStepBound@.
clpStepBoundSound ::
  Domain w -> Domain w -> Natural -> Natural -> Property
clpStepBoundSound a b i j =
  proper a ==> proper b ==>
    Prelude.not (isSelfWrapping a) ==> Prelude.not (isSelfWrapping b) ==>
    i <= n a ==> j <= n b ==>
      let !(al, _ah) = zboundsArc a
          !(bl, _bh) = zboundsArc b
          !d = cornerProductStride a b al bl
          !bound = clpStepBound a b al bl d
          !p = (al + toInteger i * toInteger (stride a))
             * (bl + toInteger j * toInteger (stride b))
          !offset = Prelude.abs (p - al * bl)
      in property (d == 0 && offset == 0
                || d /= 0 && offset `Prelude.div` d <= bound)

-- | 'arcStepBound' is a sound upper bound on the number of stride-@d@
-- integer steps between @lo@ and any concrete product. Tested at the
-- @cornerArc@/'cornerProductStride' values from a pair of cut pieces.
arcStepBoundSound ::
  Domain w -> Domain w -> Natural -> Natural -> Property
arcStepBoundSound a b i j =
  proper a ==> proper b ==>
    Prelude.not (isSelfWrapping a) ==> Prelude.not (isSelfWrapping b) ==>
    i <= n a ==> j <= n b ==>
      let !(al, ah) = zboundsArc a
          !(bl, bh) = zboundsArc b
          !(lo, hi) = cornerArc al ah bl bh
          !d = cornerProductStride a b al bl
          !bound = arcStepBound lo hi d
          !p = (al + toInteger i * toInteger (stride a))
             * (bl + toInteger j * toInteger (stride b))
          !offset = p - lo
      in property (d == 0 && offset == 0
                || d /= 0 && offset `Prelude.div` d <= bound)

correct_udiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (udiv w a b) (x `quot` y))

correct_urem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_urem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> y /= 0 ==>
    property (member (urem w a b) (x `rem` y))

correct_sdiv ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdiv w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (sdiv w a b) (asN w (xs `quot` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)

correct_srem ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_srem w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==> ys /= 0 ==>
    property (member (srem w a b) (asN w (xs `rem` ys)))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)

-- ------------------------------------------------------------------
-- *** Exactness

spanExact :: Domain w -> Natural
spanExact c = n c * stride c

nonWrapping :: Domain w -> Bool
nonWrapping c = Prelude.not (start c + n c * stride c > mask c)

addSoundCond :: Domain w -> Domain w -> Bool
addSoundCond a b = spanExact a + spanExact b <= mask a

addStrideCond :: Domain w -> Domain w -> Bool
addStrideCond a b =
  (stride b `mod` stride a == 0 && size a >= stride b `div` stride a) ||
  (stride a `mod` stride b == 0 && size b >= stride a `div` stride b)

addExactCond :: Domain w -> Domain w -> Bool
addExactCond a b =
  nonWrapping a && nonWrapping b && addSoundCond a b && addStrideCond a b

exactAddImage :: NatRepr w -> Domain w -> Domain w -> Set.Set Natural
exactAddImage w a b =
  Set.fromList [ asN w (toInteger x + toInteger y)
               | x <- toList a
               , y <- toList b
               ]

exactSubImage :: NatRepr w -> Domain w -> Domain w -> Set.Set Natural
exactSubImage w a b =
  Set.fromList [ asN w (toInteger x - toInteger y)
               | x <- toList a
               , y <- toList b
               ]

-- | Under the CLP/ASE side conditions for non-wrapping aligned addition, the
-- abstract result is exact: it contains exactly the concrete pointwise sums.
addExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
addExact w a b =
  proper a ==> proper b ==> mask a == mask b ==> addExactCond a b ==>
    property (Set.fromList (toList (add w a b)) == exactAddImage w a b)

-- | Under the same side conditions, subtraction is exact.
subExact ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
subExact w a b =
  proper a ==> proper b ==> mask a == mask b ==> addExactCond a b ==>
    property (Set.fromList (toList (sub w a b)) == exactSubImage w a b)

mulConstExactCond :: Domain w -> Natural -> Bool
mulConstExactCond a k =
  k /= 0 && nonWrapping a &&
  k * stride a <= mask a &&
  k * spanExact a <= mask a

exactScaleImage :: NatRepr w -> Natural -> Domain w -> Set.Set Natural
exactScaleImage w k a =
  Set.fromList [ asN w (toInteger k * toInteger x)
               | x <- toList a
               ]

-- | Multiplication by a positive constant is exact when neither the resulting
-- stride nor the non-wrapping span overflows.
mulConstExact ::
  (1 <= w) =>
  NatRepr w -> Natural -> Domain w -> Property
mulConstExact w k a =
  proper a ==> mulConstExactCond a k' ==>
    property (Set.fromList (toList (scaleSingleton w k' a)) == exactScaleImage w k' a)
  where
    k' = k Bits..&. mask a

udivConstExactCond :: Domain w -> Natural -> Bool
udivConstExactCond a k =
  k /= 0 && nonWrapping a &&
  (stride a < k || stride a `mod` k == 0)

exactUdivImage :: Natural -> Domain w -> Set.Set Natural
exactUdivImage k a =
  Set.fromList [ x `quot` k | x <- toList a ]

-- | Unsigned division by a positive constant is exact on non-wrapping inputs
-- when the stride is either smaller than the divisor or divisible by it.
udivConstExact ::
  (1 <= w) =>
  NatRepr w -> Natural -> Domain w -> Property
udivConstExact w k a =
  proper a ==> udivConstExactCond a k' ==>
    property (Set.fromList (toList (udiv w a divisor)) == exactUdivImage k' a)
  where
    k' = k Bits..&. mask a
    divisor = mk w k' 1 0

uremConstSameQuotCond :: Domain w -> Natural -> Bool
uremConstSameQuotCond a k =
  stride a == 1 &&
  start a `quot` k == end a `quot` k

uremConstFullResidueCond :: Domain w -> Natural -> Bool
uremConstFullResidueCond a k =
  start a `quot` k /= end a `quot` k &&
  Prelude.gcd (stride a) k == 1 &&
  spanExact a >= lcmNat (stride a) k - stride a

uremConstExactCond :: Domain w -> Natural -> Bool
uremConstExactCond a k =
  k /= 0 && nonWrapping a &&
  (uremConstSameQuotCond a k || uremConstFullResidueCond a k)

exactUremImage :: Natural -> Domain w -> Set.Set Natural
exactUremImage k a =
  Set.fromList [ x `rem` k | x <- toList a ]

-- | Unsigned remainder by a positive constant is exact on non-wrapping
-- inputs in the paper's single-quotient case when the operand is already
-- contiguous, and in the full-coverage case when the residue set is the full
-- interval @[0, k-1]@ (here, the coprime @gcd(stride, k)=1@ subcase
-- representable by a single progression result).
uremConstExact ::
  (1 <= w) =>
  NatRepr w -> Natural -> Domain w -> Property
uremConstExact w k a =
  proper a ==> uremConstExactCond a k' ==>
    property (Set.fromList (toList (urem w a divisor)) == exactUremImage k' a)
  where
    k' = k Bits..&. mask a
    divisor = mk w k' 1 0

-- | In the separated case @end a < start b@ for non-wrapping operands, every
-- concrete pair satisfies unsigned less-than.
ultExactTrueSeparated ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
ultExactTrueSeparated _w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    nonWrapping a ==> nonWrapping b ==> end a < start b ==>
      property (Prelude.and [ x < y | x <- toList a, y <- toList b ])

-- | In the separated case @end b <= start a@ for non-wrapping operands, no
-- concrete pair satisfies unsigned less-than.
ultExactFalseSeparated ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
ultExactFalseSeparated _w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    nonWrapping a ==> nonWrapping b ==> end b <= start a ==>
      property (Prelude.and [ Prelude.not (x < y) | x <- toList a, y <- toList b ])

-- ------------------------------------------------------------------
-- *** Arithmetic (SMT-LIB div-by-zero semantics)

correct_udivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_udivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (udivSmtlib w a b) z)
  where
    z = if y == 0
          then fromInteger (maxUnsigned w)
          else x `quot` y

correct_uremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_uremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (uremSmtlib w a b) z)
  where
    z = if y == 0 then x else x `rem` y

correct_sdivSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sdivSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sdivSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0
           then if xs >= 0 then -1 else 1
           else xs `quot` ys

correct_sremSmtlib ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_sremSmtlib w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (sremSmtlib w a b) (asN w z))
  where
    xs = toSigned w (toInteger x)
    ys = toSigned w (toInteger y)
    z  = if ys == 0 then xs else xs `rem` ys

-- ------------------------------------------------------------------
-- ** Bitwise operations

correct_not :: (1 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_not w c x =
  proper c ==> member c x ==>
    property (member (not w c) (asN w (Bits.complement (toInteger x))))

correct_and ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_and w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (and w a b) (x Bits..&. y))

correct_or ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_or w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (or w a b) (x Bits..|. y))

correct_xor ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_xor w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (xor w a b) (Bits.xor x y))

correct_andPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_andPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (andPrecise w a b) (x Bits..&. y))

correct_orPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_orPrecise w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (orPrecise w a b) (x Bits..|. y))

-- | 'andSingleton' is sound: @k & y@ is a member for every @y@ in @c@.
correct_andSingleton ::
  (1 <= w) => NatRepr w -> Natural -> Domain w -> Natural -> Property
correct_andSingleton w k c y =
  proper c ==> member c y ==>
    property (member (andSingleton w (k Bits..&. mask c) c) (k Bits..&. y))

-- | 'warrenAndLo' is a sound lower bound on @{ x .&. y | alo <= x <= ahi,
-- blo <= y <= bhi }@, where all values are at width @k@.
warrenAndLoCorrect ::
  Natural -> Natural -> Natural -> Natural -> Natural -> Natural -> Int -> Property
warrenAndLoCorrect alo ahi blo bhi x y k =
  k >= 1 ==> alo' <= ahi' ==> blo' <= bhi' ==>
    alo' <= x' ==> x' <= ahi' ==> blo' <= y' ==> y' <= bhi'
      ==> property (warrenAndLo m alo' ahi' blo' bhi' <= x' .&. y')
  where
    m    = (1 `shiftL` k) - 1
    alo' = alo .&. m
    ahi' = ahi .&. m
    blo' = blo .&. m
    bhi' = bhi .&. m
    x'   = x .&. m
    y'   = y .&. m

-- | 'warrenAndHi' is a sound upper bound on the AND, at width @k@.
warrenAndHiCorrect ::
  Natural -> Natural -> Natural -> Natural -> Natural -> Natural -> Int -> Property
warrenAndHiCorrect alo ahi blo bhi x y k =
  k >= 1 ==> alo' <= ahi' ==> blo' <= bhi' ==>
    alo' <= x' ==> x' <= ahi' ==> blo' <= y' ==> y' <= bhi'
      ==> property (x' .&. y' <= warrenAndHi m alo' ahi' blo' bhi')
  where
    m    = (1 `shiftL` k) - 1
    alo' = alo .&. m
    ahi' = ahi .&. m
    blo' = blo .&. m
    bhi' = bhi .&. m
    x'   = x .&. m
    y'   = y .&. m

-- | 'operandRange' soundly bounds the orbit: every member lies in @[lo, hi]@.
operandRangeCorrect :: Domain w -> Natural -> Property
operandRangeCorrect c x =
  proper c ==> member c x' ==>
    let !(lo, hi) = operandRange c
    in property (lo <= x' && x' <= hi)
  where
    x' = x Bits..&. mask c

-- | 'andPrecise' is at least as precise as 'andFast' /by cardinality/.
--
-- The chain @size andPrecise ≤ size andPreciseRaw ≤ size andFast@ holds
-- structurally: the second inequality is the Warren-vs-naive bound, the
-- first is the 'psplitOp2' min-by-size guard.
--
-- The corresponding relation against 'and' (also 'psplitOp2'-wrapped) does
-- /not/ hold: 'pseudoJoin' is non-monotone, so the pseudo-joined result of
-- the tighter Warren pieces can land on a coset that is /larger/ than the
-- pseudo-joined result of the looser 'andFast' pieces.
andPreciseDominatesAndFast ::
  (1 <= w) => NatRepr w -> Domain w -> Domain w -> Property
andPreciseDominatesAndFast w a b =
  proper a ==> proper b ==>
    property (size (andPrecise w a b) <= size (andFast w a b))

-- ------------------------------------------------------------------
-- ** Concatenation, extension, selection, and truncation

correct_zero_ext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_zero_ext w c u x =
  proper c ==> member c x ==> property (member (zext w c u) x)

correct_sign_ext ::
  forall w u.
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Domain w -> NatRepr u -> Natural -> Property
correct_sign_ext w c u x =
  case NR.leqTrans (NR.leqAdd (LeqProof :: LeqProof 1 w) (NR.knownNat @1))
                   (LeqProof :: LeqProof (w + 1) u) of
    LeqProof ->
      proper c ==> member c x ==>
        property (member (sext w c u) (asN u (toSigned w (toInteger x))))

correct_concat ::
  forall u v.
  (1 <= u, 1 <= v) =>
  NatRepr u -> Domain u -> Natural ->
  NatRepr v -> Domain v -> Natural ->
  Property
correct_concat u a x v b y =
  case NR.leqAddPos u v of
    LeqProof ->
      let z = (x `Bits.shiftL` NR.widthVal v) Bits..|. y in
      proper a ==> proper b ==> member a x ==> member b y ==>
        property (member (concat u a v b) z)

correct_select ::
  forall i n w.
  (1 <= n, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Domain w -> Natural -> Property
correct_select i n w c x =
  case NR.leqTrans (LeqProof :: LeqProof 1 n)
                   (NR.leqTrans (NR.addPrefixIsLeq i n)
                                (LeqProof :: LeqProof (i + n) w)) of
    LeqProof ->
      let y = fromInteger ((toInteger x `Bits.shiftR` NR.widthVal i) Bits..&. maxUnsigned n) in
      proper c ==> member c x ==>
        property (member (select i n w c) y)

-- ------------------------------------------------------------------
-- ** Shifts and rotations

correct_shl ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_shl w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (shl w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toInteger x `Bits.shiftL` s)

correct_lshr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_lshr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (lshr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = fromInteger (toInteger x `Bits.shiftR` s)

correct_ashr ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ashr w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (ashr w a b) z)
  where
    s = fromInteger (min (NR.intValue w) (toInteger y))
    z = asN w (toSigned w (toInteger x) `Bits.shiftR` s)

correct_rol ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_rol w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (rol w a b) (fromInteger (Arith.rotateLeft w (toInteger x) (toInteger y))))

correct_ror ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_ror w a x b y =
  proper a ==> proper b ==> member a x ==> member b y ==>
    property (member (ror w a b) (fromInteger (Arith.rotateRight w (toInteger x) (toInteger y))))

-- ------------------------------------------------------------------
-- ** Lattice operations

-- ------------------------------------------------------------------
-- *** Splitting helpers

-- | 'nsplit' is a sound cover: every member of @a@ lies in some piece. (When
-- @a@ self-wraps, pieces may also contain values outside @a@, since the split
-- collapses to the full coset; otherwise the pieces partition @a@ exactly.)
nsplitUnion ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
nsplitUnion w a x =
  proper a ==>
    member a x ==>
      let pieces = nsplit w a in
      property (Prelude.or [ member p x | p <- pieces ])

-- | 'nsplit' returns one or two pieces, and when two, their concretizations
-- are disjoint.
nsplitDisjoint ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
nsplitDisjoint w a x =
  proper a ==>
    case nsplit w a of
      [_]      -> property True
      [p1, p2] -> property (Prelude.not (member p1 x && member p2 x))
      _        -> property False  -- nsplit must return 1 or 2 pieces

-- | 'ssplit' is a sound cover: every member of @a@ lies in some piece. (When
-- @a@ self-wraps, pieces may also contain values outside @a@.)
ssplitUnion ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
ssplitUnion w a x =
  proper a ==>
    member a x ==>
      let pieces = ssplit w a in
      property (Prelude.or [ member p x | p <- pieces ])

-- | 'ssplit' returns one or two pieces, and when two, their concretizations
-- are disjoint.
ssplitDisjoint ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Property
ssplitDisjoint w a x =
  proper a ==>
    case ssplit w a of
      [_]      -> property True
      [p1, p2] -> property (Prelude.not (member p1 x && member p2 x))
      _        -> property False  -- ssplit must return 1 or 2 pieces

-- ------------------------------------------------------------------
-- *** Meets

-- | 'pseudoMeet' is sound: every element of both operands is in the result.
correct_pseudoMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_pseudoMeet w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b x ==>
      case pseudoMeet w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'pseudoMeetPrecise' is sound: every element of both operands is in the result.
correct_pseudoMeetPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_pseudoMeetPrecise w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b x ==>
      case pseudoMeetPrecise w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'pseudoMeet' is a lower bound when neither operand wraps mod @2^w@: in
-- that regime the closed-form CLP intersection is exact, and the
-- result is contained in both @a@ and @b@ under 'leqExact'. (For wrapping
-- operands 'pseudoMeet' is sound but not generally a lower bound; see the
-- note on 'pseudoMeet'.)
pseudoMeetLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoMeetLowerBound _w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
      case pseudoMeet _w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a && leqExact c b)
  where
    wraps c = start c + n c * stride c > mask c

-- | 'pseudoMeetPrecise' is a lower bound when neither operand wraps mod @2^w@.
pseudoMeetPreciseLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoMeetPreciseLowerBound _w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
      case pseudoMeetPrecise _w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a && leqExact c b)
  where
    wraps c = start c + n c * stride c > mask c

-- | 'pseudoMeet' is commutative up to 'leqExact' equivalence.
pseudoMeetCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoMeetCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (pseudoMeet w a b) (pseudoMeet w b a))

-- | 'pseudoMeetPrecise' is commutative up to 'leqExact' equivalence.
pseudoMeetPreciseCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoMeetPreciseCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (pseudoMeetPrecise w a b) (pseudoMeetPrecise w b a))

-- | 'pseudoMeet' is idempotent: @pseudoMeet a a == Just a@.
pseudoMeetIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoMeetIdempotent w a =
  proper a ==> property (pseudoMeet w a a == Just a)

-- | 'pseudoMeetPrecise' is idempotent.
pseudoMeetPreciseIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoMeetPreciseIdempotent w a =
  proper a ==> property (pseudoMeetPrecise w a a == Just a)

-- | @pseudoMeet a top ≡ a@: 'top' is the identity for 'pseudoMeet'.
pseudoMeetTopIdentity ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoMeetTopIdentity w a =
  proper a ==>
    case pseudoMeet w a (top w) of
      Just c  -> property (leqExact c a && leqExact a c)
      Nothing -> property False

-- | @pseudoMeetPrecise a top ≡ a@.
pseudoMeetPreciseTopIdentity ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoMeetPreciseTopIdentity w a =
  proper a ==>
    case pseudoMeetPrecise w a (top w) of
      Just c  -> property (leqExact c a && leqExact a c)
      Nothing -> property False

-- | When 'exactMeet' returns @Just c@, @c@ is the /exact/ intersection:
-- @x ∈ c@ iff @x ∈ a ∧ x ∈ b@.
correct_exactMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_exactMeet w a b x =
  proper a ==> proper b ==> mask a == mask b ==>
    case exactMeet w a b of
      Nothing -> property True
      Just c  -> property (member c x == (member a x && member b x))

-- | 'exactMeet' is commutative.
exactMeetCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
exactMeetCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (exactMeet w a b) (exactMeet w b a))

-- | 'exactMeet' is idempotent on non-wrap-mod-@2^w@ operands:
-- @exactMeet a a == Just a@.
exactMeetIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
exactMeetIdempotent w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      property (exactMeet w a a == Just a)

-- | When 'exactMeet' returns @Just c@, @c@ is a lower bound: @c@ is
-- contained in both operands under 'leqExact'.
exactMeetLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
exactMeetLowerBound w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case exactMeet w a b of
      Nothing -> property True
      Just c  -> property (leqExact c a && leqExact c b)

-- | @exactMeet a top == Just a@ for non-wrap-mod-@2^w@ @a@.
exactMeetTopIdentity ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
exactMeetTopIdentity w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      case exactMeet w a (top w) of
        Just c  -> property (leqExact c a && leqExact a c)
        Nothing -> property False

-- | 'exactMeet' is associative /when both nested computations return @Just@/.
-- Same partial-operator caveat as 'exactJoinAssociative': one association
-- can succeed while another fails because an intermediate intersection
-- isn't itself a single progression.
exactMeetAssociative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
exactMeetAssociative w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask a == mask c ==>
      let lhs = exactMeet w a b >>= exactMeet w c
          rhs = exactMeet w b c >>= exactMeet w a
      in case (lhs, rhs) of
           (Just x, Just y) -> property (leqExact x y && leqExact y x)
           _                -> property True

-- | 'lowerBound' is an /under/-approximation of intersection: every element of the
-- result is a member of both operands.
correct_lowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_lowerBound w a b x =
  proper a ==> proper b ==> mask a == mask b ==>
    case lowerBound w a b of
      Nothing -> property True
      Just c  -> member c x ==> property (member a x && member b x)

-- | 'lowerBound' is a true lower bound: every element of the result is in both
-- operands under 'leqExact'. Unlike 'pseudoMeetLowerBound' this holds
-- unconditionally (no non-wrapping restriction), because 'lowerBound' bails out
-- to 'Nothing' on wrapping inputs.
lowerBoundLeqExactBoth ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
lowerBoundLeqExactBoth w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case lowerBound w a b of
      Nothing -> property True
      Just c  -> property (leqExact c a && leqExact c b)

-- | 'lowerBound' is commutative.
lowerBoundCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
lowerBoundCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (lowerBound w a b) (lowerBound w b a))

-- | 'lowerBound' is idempotent on non-wrapping operands: @lowerBound a a == Just a@. (On
-- wrapping operands 'lowerBound' returns 'Nothing' even when @a@ is non-empty —
-- this is the under-approximation contract.)
lowerBoundIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
lowerBoundIdempotent w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      property (lowerBound w a a == Just a)

-- | @lowerBound a top == Just a@ on non-wrapping operands.
lowerBoundTopIdentity ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
lowerBoundTopIdentity w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      case lowerBound w a (top w) of
        Just c  -> property (leqExact c a && leqExact a c)
        Nothing -> property False

-- | 'lowerBound' returns the largest candidate from 'lowerBounds' by 'size'.
-- This is the documented contract that distinguishes 'lowerBound' from a
-- "first non-empty arc-meet" implementation.
lowerBoundIsLargestLowerBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
lowerBoundIsLargestLowerBound w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case (lowerBound w a b, lowerBounds w a b) of
      (Nothing, [])     -> property True
      (Nothing, _)      -> property False
      (Just _,  [])     -> property False
      (Just c,  cs)     ->
        property (size c == Prelude.maximum (map size cs))

-- | 'lowerBounds' is sound: every element of every returned sub-progression
-- is in both operands.
correct_lowerBounds ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_lowerBounds w a b x =
  proper a ==> proper b ==> mask a == mask b ==>
    property (Prelude.and
                [ Prelude.not (member c x) || (member a x && member b x)
                | c <- lowerBounds w a b
                ])

-- | Every result in 'lowerBounds' is contained in both operands under
-- 'leqExact'. Stronger structural form of 'correct_lowerBounds'.
lowerBoundsAllSubsets ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
lowerBoundsAllSubsets w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (Prelude.and [ leqExact c a && leqExact c b
                          | c <- lowerBounds w a b
                          ])

-- | Precision dominance, cross-direction: 'lowerBound' is contained in
-- 'pseudoMeet' (when both are non-empty). They bound the true intersection
-- from opposite sides — 'lowerBound' from below (under-approx),
-- 'pseudoMeet' from above (over-approx) — so any value in 'lowerBound a b'
-- is in the true intersection, and hence in 'pseudoMeet a b'.
--
-- This implies @size (lowerBound a b) <= size (pseudoMeet a b)@.
lowerBoundDominatedByPseudoMeet ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
lowerBoundDominatedByPseudoMeet w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case (lowerBound w a b, pseudoMeet w a b) of
      (Nothing, _)        -> property True
      (Just _, Nothing)   -> property False  -- lowerBound non-empty implies intersection non-empty
      (Just lo, Just up)  -> property (leqExact lo up)

-- ------------------------------------------------------------------
-- *** Joins

-- | The stride-1 arith hull of @c@, embedded back into the strides domain.
-- A helper for the upper-bound and idempotence properties of 'hullJoin' and
-- 'boundingBoxJoin'.
hullCover :: (1 <= w) => NatRepr w -> Domain w -> Domain w
hullCover w c = case fromArith w (hull c) of
  Just c' -> c'
  Nothing -> c

-- | 'pseudoJoin' is sound: every member of either operand is in the result.
correct_pseudoJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_pseudoJoin w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==>
      property (member (pseudoJoin w a b) x)

-- | 'pseudoJoinPrecise' is sound: every member of either operand is in the result.
correct_pseudoJoinPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_pseudoJoinPrecise w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==>
      property (member (pseudoJoinPrecise w a b) x)

-- | 'pseudoJoin' is an upper bound when neither operand wraps mod @2^w@: in
-- that regime the closed-form path returns a sound cover whose hull is the
-- arith join of the operand hulls, and both operands are contained in it
-- under 'leqExact'. With wrap, the hull-based projection may not contain
-- either operand exactly.
pseudoJoinUpperBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoJoinUpperBound w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
      let ab = pseudoJoin w a b
      in property (leqExact a ab && leqExact b ab)
  where
    wraps c = start c + n c * stride c > mask c

-- | 'pseudoJoinPrecise' is an upper bound when neither operand wraps mod @2^w@.
pseudoJoinPreciseUpperBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoJoinPreciseUpperBound w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wraps a) ==> Prelude.not (wraps b) ==>
      let ab = pseudoJoinPrecise w a b
      in property (leqExact a ab && leqExact b ab)
  where
    wraps c = start c + n c * stride c > mask c

-- | 'pseudoJoin' is commutative up to 'leqExact'.
pseudoJoinCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoJoinCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    let ab = pseudoJoin w a b
        ba = pseudoJoin w b a
    in property (leqExact ab ba && leqExact ba ab)

-- | 'pseudoJoinPrecise' is commutative up to 'leqExact'.
pseudoJoinPreciseCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoJoinPreciseCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    let ab = pseudoJoinPrecise w a b
        ba = pseudoJoinPrecise w b a
    in property (leqExact ab ba && leqExact ba ab)

-- | 'pseudoJoin' is idempotent up to 'leqExact'.
pseudoJoinIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoJoinIdempotent w a =
  proper a ==>
    let aa = pseudoJoin w a a
    in property (leqExact aa a && leqExact a aa)

-- | 'pseudoJoinPrecise' is idempotent up to 'leqExact'.
pseudoJoinPreciseIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoJoinPreciseIdempotent w a =
  proper a ==>
    let aa = pseudoJoinPrecise w a a
    in property (leqExact aa a && leqExact a aa)

-- | 'pseudoJoinPrecise' refines 'pseudoJoin': anything 'pseudoJoinPrecise'
-- contains, 'pseudoJoin' contains too.
pseudoJoinPreciseRefinesJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoJoinPreciseRefinesJoin w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (leqExact (pseudoJoinPrecise w a b) (pseudoJoin w a b))

-- | @pseudoJoin a top ≡ top@: 'top' is an annihilator for 'pseudoJoin'.
pseudoJoinTopAnnihilator ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoJoinTopAnnihilator w a =
  proper a ==>
    let ab = pseudoJoin w a (top w)
    in property (leqExact ab (top w) && leqExact (top w) ab)

-- | @pseudoJoinPrecise a top ≡ top@.
pseudoJoinPreciseTopAnnihilator ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
pseudoJoinPreciseTopAnnihilator w a =
  proper a ==>
    let ab = pseudoJoinPrecise w a (top w)
    in property (leqExact ab (top w) && leqExact (top w) ab)

-- | 'boundingBoxJoin' is sound: every element of either operand is in the result.
correct_boundingBoxJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_boundingBoxJoin w a x b _y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==>
      property (member (boundingBoxJoin w a b) x)

-- | 'boundingBoxJoin' is commutative.
boundingBoxJoinCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
boundingBoxJoinCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    let ab = boundingBoxJoin w a b
        ba = boundingBoxJoin w b a
    in property (leqExact ab ba && leqExact ba ab)

-- | 'boundingBoxJoin' is idempotent up to 'leqExact' (collapses to the stride-1
-- arith hull of the operand) when the operand doesn't wrap mod @2^w@.
-- Wrapping operands saturate 'A.ubounds' to @(0, mask)@, so 'boundingBoxJoin' on
-- two copies of a wrapping operand returns 'top', not the operand.
boundingBoxJoinIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
boundingBoxJoinIdempotent w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      let aa = boundingBoxJoin w a a
      in property (leqExact aa (hullCover w a) && leqExact (hullCover w a) aa)

-- | @boundingBoxJoin a top@ is 'top'.
boundingBoxJoinTopAnnihilator ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
boundingBoxJoinTopAnnihilator w a =
  proper a ==>
    let ab = boundingBoxJoin w a (top w)
    in property (leqExact ab (top w) && leqExact (top w) ab)

-- | 'boundingBoxJoin' is an upper bound on the stride-1 hull of each operand.
boundingBoxJoinUpperBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
boundingBoxJoinUpperBound w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    let ab = boundingBoxJoin w a b
    in property (leqExact (hullCover w a) ab && leqExact (hullCover w b) ab)

-- | 'boundingBoxJoin' is associative — the headline win over 'hullJoin' and 'pseudoJoin'.
boundingBoxJoinAssociative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
boundingBoxJoinAssociative w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask a == mask c ==>
      let lhs = boundingBoxJoin w (boundingBoxJoin w a b) c
          rhs = boundingBoxJoin w a (boundingBoxJoin w b c)
      in property (leqExact lhs rhs && leqExact rhs lhs)

-- | 'boundingBoxJoin' is monotone in the strides order /when no operand
-- wraps mod @2^w@/ (i.e. @start + n·stride <= mask@). 'A.ubounds' collapses
-- any wrapping interval to @(0, mask)@, so @hull@ is non-monotone on
-- wrapping inputs; that gap leaks through 'boundingBoxJoin'.
boundingBoxJoinMonotone ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
boundingBoxJoinMonotone w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask a == mask c ==>
      Prelude.not (wraps a) ==>
        Prelude.not (wraps b) ==>
          Prelude.not (wraps c) ==>
            leqExact a b ==>
              property (leqExact (boundingBoxJoin w a c) (boundingBoxJoin w b c))
  where
    wraps d = start d + n d * stride d > mask d

-- | Precision dominance (cardinality only): the result of 'pseudoJoin' has
-- no more elements than 'boundingBoxJoin'. Subset dominance does /not/ hold —
-- 'A.join' inside 'pseudoJoin' picks the shorter (possibly-wrapping) arc
-- while 'boundingBoxJoin' always picks the non-wrapping bounding box, and these can be
-- incomparable as sets. They agree on size ordering because 'A.join' picks
-- the /shorter/ of the two arcs and 'boundingBoxJoin' picks the (possibly longer)
-- non-wrapping one, then 'pseudoJoin' further restricts to a coset.
--
-- Counterexample for subset dominance at @w=5@: @a={21}, b={0}@.
-- @pseudoJoin@ wraps to @{21..31, 0}@ (12 elements); @boundingBoxJoin@ stays
-- non-wrapping at @{0..21}@ (22 elements). Incomparable, but
-- @|pseudoJoin| = 12 <= 22 = |boundingBoxJoin|@.
pseudoJoinDominatesBoundingBoxJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
pseudoJoinDominatesBoundingBoxJoin w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (size (pseudoJoin w a b) <= size (boundingBoxJoin w a b))

-- | When 'exactJoin' returns @Just c@, @c@ is the /exact/ union: every
-- element of either operand is in @c@, and every element of @c@ is in one
-- of the operands.
correct_exactJoin ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_exactJoin w a b x =
  proper a ==> proper b ==> mask a == mask b ==>
    case exactJoin w a b of
      Nothing -> property True
      Just c  -> property (member c x == (member a x || member b x))

-- | 'exactJoin' is commutative.
exactJoinCommutative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
exactJoinCommutative w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    property (eqMaybe (exactJoin w a b) (exactJoin w b a))

-- | 'exactJoin' is idempotent on non-wrap-mod-@2^w@ operands:
-- @exactJoin a a == Just a@. Wrapping operands return 'Nothing' (their
-- 'ssplit' pieces don't recompose into a single progression after
-- 'compactifyPrecise').
exactJoinIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
exactJoinIdempotent w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      property (exactJoin w a a == Just a)

-- | When 'exactJoin' returns @Just c@, @c@ is an upper bound: both
-- operands are subsets of @c@ under 'leqExact'.
exactJoinUpperBound ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
exactJoinUpperBound w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    case exactJoin w a b of
      Nothing -> property True
      Just c  -> property (leqExact a c && leqExact b c)

-- | @exactJoin a top@ exists iff the union @a ∪ top@ is a single
-- progression, which means @top@ itself. Holds for non-wrap-mod-@2^w@ @a@.
exactJoinTopAnnihilator ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Property
exactJoinTopAnnihilator w a =
  proper a ==>
    Prelude.not (start a + n a * stride a > mask a) ==>
      case exactJoin w a (top w) of
        Just c  -> property (leqExact c (top w) && leqExact (top w) c)
        Nothing -> property False

-- | 'exactJoin' is associative /when both nested computations succeed/:
-- if @LHS = Just x@ and @RHS = Just y@, then @x ≡ y@. The other-side-fails
-- case is real and unavoidable: one association order can succeed while
-- another fails, since each intermediate must itself be a single
-- progression.
--
-- Counterexample at @w=3@: @a={1}, b={2}, c={0,3}@. @(a⊔b)⊔c = {0..3}@
-- but @b⊔c = {0,2,3}@ isn't a progression, so @a⊔(b⊔c) = Nothing@.
exactJoinAssociative ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Domain w -> Property
exactJoinAssociative w a b c =
  proper a ==> proper b ==> proper c ==>
    mask a == mask b ==> mask a == mask c ==>
      let lhs = exactJoin w a b >>= exactJoin w c
          rhs = exactJoin w b c >>= exactJoin w a
      in case (lhs, rhs) of
           (Just x, Just y) -> property (leqExact x y && leqExact y x)
           _                -> property True

-- ------------------------------------------------------------------
-- *** Compactification

-- | 'compactify' preserves the union of element sets exactly: every input
-- element is in some output progression, and every output element is in
-- some input progression.
--
-- 'compactify' assumes all inputs are non-wrap-mod-@2^w@
-- (@start + n·stride <= mask@), which the property guards.
correct_compactify ::
  (1 <= w) =>
  NatRepr w -> [Domain w] -> Property
correct_compactify w cs =
  Prelude.and [ proper c | c <- cs ] ==>
    sameWidth ==>
      Prelude.and [ Prelude.not (wrapsMod c) | c <- cs ] ==>
        let inUnion  = Set.fromList (concatMap toList cs)
            outUnion = Set.fromList (concatMap toList (compactify w cs))
        in property (inUnion == outUnion)
  where
    sameWidth = case cs of
      []     -> True
      (c:cs') -> Prelude.and [ mask c == mask c' | c' <- cs' ]
    wrapsMod c = start c + n c * stride c > mask c

-- ------------------------------------------------------------------
-- ** Branch-condition assumptions

-- | 'assumeUlt' is sound: every value @x ∈ a@ that satisfies @x < y@ for
-- some @y ∈ b@ remains in the result.
correct_assumeUlt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUlt w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> x < y ==>
      case assumeUlt w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeUle' is sound.
correct_assumeUle ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUle w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> x <= y ==>
      case assumeUle w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeUgt' is sound.
correct_assumeUgt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUgt w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> x > y ==>
      case assumeUgt w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeUge' is sound.
correct_assumeUge ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeUge w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> x >= y ==>
      case assumeUge w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeSlt' is sound: every value @x ∈ a@ that satisfies @x < y@
-- (signed) for some @y ∈ b@ remains in the result.
correct_assumeSlt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSlt w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> toSigned w (toInteger x) < toSigned w (toInteger y) ==>
      case assumeSlt w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeSle' is sound.
correct_assumeSle ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSle w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> toSigned w (toInteger x) <= toSigned w (toInteger y) ==>
      case assumeSle w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeSgt' is sound.
correct_assumeSgt ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSgt w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> toSigned w (toInteger x) > toSigned w (toInteger y) ==>
      case assumeSgt w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeSge' is sound.
correct_assumeSge ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_assumeSge w a x b y =
  proper a ==> proper b ==> mask a == mask b ==>
    member a x ==> member b y ==> toSigned w (toInteger x) >= toSigned w (toInteger y) ==>
      case assumeSge w a b of
        Just c  -> property (member c x)
        Nothing -> property False

-- | 'assumeUlt' shrinks: when neither operand wraps mod @2^w@, the
-- result is contained in the input under 'leqExact'. (Without the
-- non-wrap guard, 'pseudoMeet' is sound but not generally a lower
-- bound; cf. 'pseudoMeetLowerBound'.)
assumeUltShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUltShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUlt w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeUle' shrinks (under the non-wrap guard).
assumeUleShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUleShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUle w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeUgt' shrinks (under the non-wrap guard).
assumeUgtShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUgtShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUgt w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeUge' shrinks (under the non-wrap guard).
assumeUgeShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUgeShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUge w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSlt' shrinks (under the non-wrap guard).
assumeSltShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSltShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSlt w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSle' shrinks (under the non-wrap guard).
assumeSleShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSleShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSle w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSgt' shrinks (under the non-wrap guard).
assumeSgtShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSgtShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSgt w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSge' shrinks (under the non-wrap guard).
assumeSgeShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSgeShrinks w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSge w a b of
        Nothing -> property True
        Just c  -> property (leqExact c a)
  where wrapsMod c = start c + n c * stride c > mask c

-- $idempotence
--
-- The 'assume*' operations are tested for idempotence: applying the same
-- assumption twice yields the same result as applying it once,
-- @assumeOp (assumeOp a b) b ≡ assumeOp a b@. Idempotence is /not/ a
-- consequence of 'pseudoMeet'\'s self-idempotence (which only says
-- @a ⊓ a = a@): each call meets @a@ with a fresh range built from @b@,
-- and 'pseudoMeet' is non-associative, so we cannot derive
-- @(a ⊓ r) ⊓ r = a ⊓ r@ from @r ⊓ r = r@ alone. The properties below
-- check the equation empirically (under the non-wrap guard, where
-- 'pseudoMeet' actually behaves as a lower bound).

-- | 'assumeUlt' is idempotent under the non-wrap guard.
assumeUltIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUltIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUlt w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeUlt w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeUle' is idempotent under the non-wrap guard.
assumeUleIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUleIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUle w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeUle w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeUgt' is idempotent under the non-wrap guard.
assumeUgtIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUgtIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUgt w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeUgt w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeUge' is idempotent under the non-wrap guard.
assumeUgeIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeUgeIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeUge w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeUge w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSlt' is idempotent under the non-wrap guard.
assumeSltIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSltIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSlt w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeSlt w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSle' is idempotent under the non-wrap guard.
assumeSleIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSleIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSle w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeSle w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSgt' is idempotent under the non-wrap guard.
assumeSgtIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSgtIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSgt w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeSgt w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | 'assumeSge' is idempotent under the non-wrap guard.
assumeSgeIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Domain w -> Property
assumeSgeIdempotent w a b =
  proper a ==> proper b ==> mask a == mask b ==>
    Prelude.not (wrapsMod a) ==> Prelude.not (wrapsMod b) ==>
      case assumeSge w a b of
        Nothing -> property True
        Just c  -> property (eqMaybeAssume (assumeSge w c b) (Just c))
  where wrapsMod c = start c + n c * stride c > mask c

-- | Equality of @Maybe (Domain w)@ via 'leqExact' on the @Just@ payloads.
-- Used only by the assume idempotence properties; named to avoid clashing
-- with other module-private @eqMaybe@ helpers.
eqMaybeAssume :: Maybe (Domain w) -> Maybe (Domain w) -> Bool
eqMaybeAssume Nothing  Nothing  = True
eqMaybeAssume (Just x) (Just y) = leqExact x y && leqExact y x
eqMaybeAssume _        _        = False

-- ------------------------------------------------------------------
-- ** Reduced product with bitwise

-- | The two halves of 'knownZerosOnesNat' are bit-disjoint: no bit is
-- both forced-to-0 and forced-to-1 (which would mean @b@ has no
-- members). Equivalently, the @lo .|. hi@ representation of a 'B.Domain'
-- never has @lo@ exceeding @hi@.
knownZerosOnesNatDisjoint :: B.Domain w -> Property
knownZerosOnesNatDisjoint b =
  let (zeros, ones) = knownZerosOnesNat b
  in property ((zeros .&. ones) == 0)

-- | A value @x@ is a member of @b@ iff its forced positions agree with
-- @(zeros, ones)@: bits forced to 0 are 0 in @x@, bits forced to 1 are
-- 1 in @x@.
knownZerosOnesNatMember :: B.Domain w -> Natural -> Property
knownZerosOnesNatMember b x =
  let (zeros, ones) = knownZerosOnesNat b
      bm            = integerToNatural (B.bvdMask b)
      x'            = x .&. bm
      agrees        = (zeros .&. x') == 0 && (ones .&. (bm `Bits.xor` x')) == 0
  in property (B.member b (toInteger x') == agrees)

-- | 'liftForcedBits' shrinks: when 'Just', the result is contained in
-- the input under 'leqExact'.
liftForcedBitsShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
liftForcedBitsShrinks w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case liftForcedBits w s (knownZerosOnesNat b) of
      Nothing -> property True
      Just s' -> property (leqExact s' s)

-- | 'liftForcedBits' produces a result whose low bits are consistent
-- with the forced bits of @b@: the @start@ of the result (and hence
-- every member, since they share their low @strideGcd s'@ bits) agrees
-- with @(zeros, ones)@ at positions @0..log2 (strideGcd s') - 1@.
liftForcedBitsMember ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
liftForcedBitsMember w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case liftForcedBits w s (knownZerosOnesNat b) of
      Nothing -> property True
      Just s' ->
        let (zeros, ones) = knownZerosOnesNat b
            lowMask = strideGcd s' - 1
            startLow = start s' .&. lowMask
        in property ((zeros .&. startLow) == 0
                  && (ones .&. (lowMask `Bits.xor` startLow)) == 0)

-- | 'arcClipBitwise' shrinks: when 'Just', the result is contained in
-- the input under 'leqExact'.
arcClipBitwiseShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Property
arcClipBitwiseShrinks w s lo hi =
  proper s ==>
    let lo' = lo .&. mask s
        hi' = hi .&. mask s
    in lo' <= hi' ==>
       case arcClipBitwise compactify w s (lo', hi') of
         Nothing -> property True
         Just s' -> property (leqExact s' s)

-- | 'arcClipBitwise' is sound: any element of the input that lies in
-- @[blo, bhi]@ is in the result. (Conversely, any element of the result
-- is in the input by 'arcClipBitwiseShrinks'.)
arcClipBitwiseMember ::
  (1 <= w) =>
  NatRepr w -> Domain w -> Natural -> Natural -> Natural -> Property
arcClipBitwiseMember w s lo hi x =
  proper s ==>
    let lo' = lo .&. mask s
        hi' = hi .&. mask s
        x'  = x .&. mask s
    in lo' <= hi' ==>
       member s x' ==>
       Prelude.not (isSelfWrapping s) ==>
       lo' <= x' && x' <= hi' ==>
         case arcClipBitwise compactify w s (lo', hi') of
           Nothing -> property False
           Just s' -> property (member s' x')

-- | 'refineByBits' is sound: any @x@ in both inputs is in the result
-- (and the result is 'Nothing' only when no such @x@ exists).
correct_refineByBits ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Natural -> Property
correct_refineByBits w s b x =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    member s x ==> B.member b (toInteger x) ==>
      case refineByBits w s b of
        Nothing -> property False
        Just s' -> property (member s' x)

-- | 'refineByBits' shrinks: the result is contained in the input strides
-- component (under 'leqExact').
refineByBitsShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
refineByBitsShrinks _w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case refineByBits _w s b of
      Nothing -> property True
      Just s' -> property (leqExact s' s)

-- | 'refineByBitsPrecise' is sound: any @x@ in both inputs is in the result
-- (and the result is 'Nothing' only when no such @x@ exists).
correct_refineByBitsPrecise ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Natural -> Property
correct_refineByBitsPrecise w s b x =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    member s x ==> B.member b (toInteger x) ==>
      case refineByBitsPrecise w s b of
        Nothing -> property False
        Just s' -> property (member s' x)

-- | 'refineByBitsPrecise' shrinks: the result is contained in the input
-- strides component (under 'leqExact').
refineByBitsPreciseShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
refineByBitsPreciseShrinks _w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case refineByBitsPrecise _w s b of
      Nothing -> property True
      Just s' -> property (leqExact s' s)

-- | 'refineByBitsPrecise' is at least as precise as the round-trip
-- @pseudoMeet s (fromBitwise b)@ /on non-self-wrapping/ inputs.
-- 'pseudoMeet' lacks the lower-bound axiom on wrapping operands, so the
-- round-trip can return a result not contained in @s@; on self-wrapping
-- inputs the comparison has no clear winner.
--
-- The plain 'refineByBits' does /not/ satisfy this property: its
-- 'compactify' merger uses 'leq', which lacks the singleton-on-orbit
-- containment check, so two complementary singletons (like @{1}@ and
-- @{0}@) fail to merge into the stride-@(2^w − 1)@ progression that
-- the round-trip's 'pseudoMeet' produces.
refineByBitsPreciseDominatesRoundTripNonSelfWrap ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
refineByBitsPreciseDominatesRoundTripNonSelfWrap w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    Prelude.not (isSelfWrapping s) ==>
      case (refineByBitsPrecise w s b, fromBitwise w b >>= pseudoMeet w s) of
        (Nothing, _)        -> property True
        (Just s', Nothing)  -> property (leqExact s' s)
        (Just s', Just rt)
          | leqExact rt s   -> property (size s' <= size rt)
          | otherwise       -> property True

-- | 'refineBitsByStrides' is sound: any @x@ in both inputs is in the
-- result (and 'Nothing' only when no such @x@ exists).
correct_refineBitsByStrides ::
  (1 <= w) =>
  NatRepr w -> B.Domain w -> Domain w -> Natural -> Property
correct_refineBitsByStrides w b s x =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    member s x ==> B.member b (toInteger x) ==>
      case refineBitsByStrides w b s of
        Nothing -> property False
        Just b' -> property (B.member b' (toInteger x))

-- | 'refineBitsByStrides' shrinks: the result is contained in the input
-- bitwise component.
refineBitsByStridesShrinks ::
  (1 <= w) =>
  NatRepr w -> B.Domain w -> Domain w -> Property
refineBitsByStridesShrinks w b s =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case refineBitsByStrides w b s of
      Nothing -> property True
      Just b' -> property (B.leq b' b)

-- | 'refineBitsByStrides' is at least as precise as the single-shot
-- @B.meet b (toBitwise s)@.
--
-- /Why this holds./ The piecewise stride bitwise
-- @stridesB = B.join (toBitwise piece_i)@ over @ssplit s@ is dominated
-- by @toBitwise s@: every bit forced by the whole orbit is forced by
-- each piece (pieces only contain orbit elements), so the join forces
-- it too. Pre-clipping pieces to @b@\'s arc only tightens further.
-- Therefore @B.meet b stridesB \`B.leq\` B.meet b (toBitwise s)@ — and
-- when the latter is bottom, so is the former (returned as 'Nothing').
refineBitsByStridesDominatesMeetToBitwise ::
  (1 <= w) =>
  NatRepr w -> B.Domain w -> Domain w -> Property
refineBitsByStridesDominatesMeetToBitwise w b s =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    let baseline = B.meet b (toBitwise s)
    in case refineBitsByStrides w b s of
         Nothing -> property True  -- already bottom, dominates anything
         Just b' -> property (B.leq b' baseline)

-- | 'reduceStep' is sound: any value @x@ in /both/ input components is in
-- both output components when the step succeeds; if the step returns
-- 'Nothing', no such @x@ exists.
correct_reduceStep ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Natural -> Property
correct_reduceStep w s b x =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    member s x ==> B.member b (toInteger x) ==>
      case reduceStep w s b of
        Nothing       -> property False
        Just (s', b') ->
          property (member s' x && B.member b' (toInteger x))

-- | 'reduce' is sound under the same correctness statement as 'reduceStep'.
correct_reduce ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Natural -> Property
correct_reduce w s b x =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    member s x ==> B.member b (toInteger x) ==>
      case reduce w s b of
        Nothing       -> property False
        Just (s', b') ->
          property (member s' x && B.member b' (toInteger x))

-- | 'reduceStep' only shrinks: each output component is contained in the
-- corresponding input.
reduceStepShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
reduceStepShrinks w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case reduceStep w s b of
      Nothing       -> property True
      Just (s', b') -> property (leqExact s' s && B.leq b' b)

-- | 'reduce' only shrinks (the iterated form of 'reduceStepShrinks').
reduceShrinks ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
reduceShrinks w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case reduce w s b of
      Nothing       -> property True
      Just (s', b') -> property (leqExact s' s && B.leq b' b)

-- | 'reduceFixpoint' reaches a fixed point: re-running it on its own
-- output changes nothing. ('reduce' is a widening, not a fixpoint, so
-- this property is stated against 'reduceFixpoint'.)
reduceIdempotent ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Property
reduceIdempotent w s b =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case reduceFixpoint w s b of
      Nothing       -> property True
      Just (s', b') ->
        property (reduceFixpoint w s' b' == Just (s', b'))

-- | When 'reduceFixpoint' returns 'Nothing', the joint really is empty:
-- no @x@ can be a member of both components. Contrapositive of soundness,
-- but a useful direct check that we don\'t spuriously reject.
reduceConflictMeansEmpty ::
  (1 <= w) =>
  NatRepr w -> Domain w -> B.Domain w -> Natural -> Property
reduceConflictMeansEmpty w s b x =
  proper s ==> toInteger (mask s) == B.bvdMask b ==>
    case reduceFixpoint w s b of
      Just _  -> property True
      Nothing -> property (Prelude.not (member s x && B.member b (toInteger x)))

-- | 'trimSelfWrap' produces a non-self-wrapping result.
trimSelfWrapNotSelfWrapping ::
  NatRepr w -> Domain w -> Property
trimSelfWrapNotSelfWrapping w a =
  proper a ==>
    property (Prelude.not (isSelfWrapping (trimSelfWrap w a)))

-- | 'trimSelfWrap' is sound as an under-approximation: the trimmed result
-- is contained in the original orbit (every result element is in @a@).
trimSelfWrapSubset ::
  NatRepr w -> Domain w -> Property
trimSelfWrapSubset w a =
  proper a ==>
    property (leqExact (trimSelfWrap w a) a)

-- | 'trimSelfWrap' is the identity on non-self-wrapping inputs.
trimSelfWrapIdentity ::
  NatRepr w -> Domain w -> Property
trimSelfWrapIdentity w a =
  proper a ==>
    Prelude.not (isSelfWrapping a) ==>
      property (trimSelfWrap w a == a)

-- | 'trimSelfWrap' is idempotent: applying it twice gives the same result
-- as applying it once. Follows from 'trimSelfWrapNotSelfWrapping' (the
-- result is non-self-wrapping) and 'trimSelfWrapIdentity' (a non-self-
-- wrapping input is preserved).
trimSelfWrapIdempotent ::
  NatRepr w -> Domain w -> Property
trimSelfWrapIdempotent w a =
  proper a ==>
    let !once  = trimSelfWrap w a
        !twice = trimSelfWrap w once
    in property (once == twice)

-- | Equality of 'Maybe (Domain w)' under 'leqExact' (i.e., mutual containment).
eqMaybe :: Maybe (Domain w) -> Maybe (Domain w) -> Bool
eqMaybe Nothing Nothing = True
eqMaybe (Just x) (Just y) = leqExact x y && leqExact y x
eqMaybe _ _ = False

-- ------------------------------------------------------------------
-- ** Helpers

-- | Reduce an 'Integer' modulo @2^w@ and return it as a 'Natural'.
asN :: NatRepr w -> Integer -> Natural
asN w x = fromInteger (x Bits..&. maxUnsigned w)

-- | Interpret the unsigned representation @x@ at width @w@ as a signed
-- 'Integer'.
toSigned :: (1 <= w) => NatRepr w -> Integer -> Integer
toSigned w x =
  if x' Bits..&. signBit == 0 then x' else x' - (signBit `Bits.shiftL` 1)
  where
    x' = x Bits..&. maxUnsigned w
    signBit = 1 `Bits.shiftL` (NR.widthVal w - 1)

{-|
Module      : What4.Domains.BV.Geometric
Copyright   : (c) Galois Inc, 2026
License     : BSD3

The geometric abstract domain: the lattice completion of the
"What4.Domains.BV.GeoStrides" kernel. The kernel represents nonempty sets of
/nonzero/ bitvectors (the multiplicative structure @2^v · (-1)^κ · 5^k@); this
module adds the elements the kernel structurally cannot hold:

  * 'GBot' — the empty set;
  * 'GZero' — exactly @{0}@, which has no logarithm;
  * 'GMaybeZero' — a kernel set together with @0@.

This mirrors how "What4.Domains.BV.StridedInterval" completes
"What4.Domains.BV.Strides" with an explicit bottom. The extra @0@-carrying
states are forced by the ring: multiplication has zero divisors (e.g.
@2 · 8 ≡ 0 (mod 16)@), so the product of two nonzero kernel sets can include
@0@. The kernel's arithmetic reports this possibility, and this module places
@0@ accordingly.

Like the kernel, this domain is defined only for @w ≥ 3@ and abstains on
order-sensitive operations (comparisons, @assume@) and on @add@\/@and@\/@or@,
where the multiplicative coordinates carry no information.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module What4.Domains.BV.Geometric
  ( -- * Construction
    Domain(..)
  , top
  , bottom
  , zero
  , fromKernel
    -- * Queries
  , isBottom
  , member
  , toList
  , size
  , leq
    -- * Arithmetic
  , negate
  , mul
  , square
  , pow
  , shl
    -- * Lattice operations
    -- ** Joins
  , pseudoJoin
    -- ** Meets
  , pseudoMeet
    -- * Generators
  , genDomain
  , genElement
  , genPair
    -- * Properties
    -- ** Queries
  , memberToList
  , toListMember
    -- ** Arithmetic
  , correct_neg
  , correct_mul
  , correct_square
  , correct_pow
  , correct_shl
    -- ** Lattice
  , correct_pseudoJoin
  , correct_pseudoMeet
  , leqReflexive
  , leqTransitive
  ) where

import           Data.Bits (shiftL)
import qualified Data.Set as Set
import           GHC.TypeNats (Nat, type (<=))
import           Numeric.Natural (Natural)
import           Prelude hiding (negate)

import           Data.Parameterized.NatRepr (NatRepr)
import qualified Data.Parameterized.NatRepr as NR

import qualified What4.Domains.BV.GeoStrides as G
import           What4.Domains.Verification (Property, property, (==>), Gen, chooseInt)

-- ------------------------------------------------------------------
-- * Construction

-- | A geometric-domain element at width @w@: a set of bitvectors.
data Domain (w :: Nat)
  = GBot
    -- ^ The empty set.
  | GZero
    -- ^ Exactly @{0}@.
  | GNonzero !(G.Domain w)
    -- ^ A nonempty set of nonzero values (a kernel element).
  | GMaybeZero !(G.Domain w)
    -- ^ A kernel element together with @0@.
  deriving (Eq, Ord, Show)

-- | The top element: all bitvectors (every nonzero value, plus @0@).
top :: (3 <= w) => NatRepr w -> Domain w
top w = GMaybeZero (G.top w)

-- | The empty set.
bottom :: Domain w
bottom = GBot

-- | The singleton @{0}@.
zero :: Domain w
zero = GZero

-- | Inject a kernel element (a set of nonzero values) into the domain.
fromKernel :: G.Domain w -> Domain w
fromKernel = GNonzero

-- ------------------------------------------------------------------
-- * Queries

-- | Is this the empty set?
isBottom :: Domain w -> Bool
isBottom = \case
  GBot -> True
  _    -> False

-- | Test membership.
member :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Bool
member w d x = case d of
  GBot          -> False
  GZero         -> x == 0
  GNonzero c    -> G.member w c x
  GMaybeZero c  -> x == 0 || G.member w c x

-- | Enumerate the members (ascending, no duplicates).
toList :: (3 <= w) => NatRepr w -> Domain w -> [Natural]
toList w d = case d of
  GBot          -> []
  GZero         -> [0]
  GNonzero c    -> G.toList w c
  GMaybeZero c  -> Set.toAscList (Set.insert 0 (Set.fromList (G.toList w c)))

-- | The number of distinct members.
size :: (3 <= w) => NatRepr w -> Domain w -> Natural
size w d = case d of
  GBot          -> 0
  GZero         -> 1
  GNonzero c    -> G.size w c
  GMaybeZero c  -> 1 + G.size w c   -- @0@ is never in a kernel set

-- | Lattice order.
leq :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Bool
leq w a b = case (a, b) of
  (GBot, _) -> True
  (_, GBot) -> False
  (GZero, GZero) -> True
  (GZero, GMaybeZero _) -> True
  (GZero, _) -> False
  (GNonzero c, GNonzero d) -> G.leq w c d
  (GNonzero c, GMaybeZero d) -> G.leq w c d
  (GNonzero _, _) -> False
  (GMaybeZero c, GMaybeZero d) -> G.leq w c d
  (GMaybeZero _, _) -> False

-- ------------------------------------------------------------------
-- * Arithmetic

-- | Negate every member. @0@ negates to @0@; nonzero values stay nonzero (the
-- kernel 'G.negate' is total).
negate :: (3 <= w) => NatRepr w -> Domain w -> Domain w
negate w = \case
  GBot         -> GBot
  GZero        -> GZero
  GNonzero c   -> GNonzero (G.negate w c)
  GMaybeZero c -> GMaybeZero (G.negate w c)

-- | Multiply two sets. @0@ is absorbing; otherwise the nonzero parts multiply
-- via the kernel, and @0@ is added to the result whenever it can arise — either
-- because some operand already contained @0@, or because the kernel product can
-- overflow to @0@ (reported by 'G.mul').
mul :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
mul w a b = case (a, b) of
  (GBot, _) -> GBot
  (_, GBot) -> GBot
  (GZero, _) -> GZero
  (_, GZero) -> GZero
  _ ->
    -- Both operands have a nonzero part; either may also carry @0@.
    let (ka, za) = splitZero a
        (kb, zb) = splitZero b
        (mc, mayZero) = G.mul w ka kb
        -- @0@ is in the product if either factor contributed @0@, or the
        -- nonzero product overflowed to @0@.
        zeroPossible = za || zb || mayZero
    in assemble mc zeroPossible

-- | Square every member.
square :: (3 <= w) => NatRepr w -> Domain w -> Domain w
square w = \case
  GBot         -> GBot
  GZero        -> GZero
  GNonzero c   -> uncurry assemble (G.square w c)
  GMaybeZero c ->
    -- @0² = 0@, so @0@ is in the result regardless of overflow.
    let (mc, _) = G.square w c in assemble mc True

-- | Raise every member to a fixed nonnegative power. @0^0 = 1@ by convention
-- (matching 'G.pow'); @0^e = 0@ for @e ≥ 1@.
pow :: (3 <= w) => NatRepr w -> Integer -> Domain w -> Domain w
pow w e = \case
  GBot       -> GBot
  GZero      -> if e == 0 then oneSet w else GZero
  GNonzero c -> uncurry assemble (G.pow w e c)
  GMaybeZero c
    -- every member (including 0) raised to the 0th power is 1
    | e == 0 -> oneSet w
      -- @0^e = 0@ for e ≥ 1, so 0 stays in the result
    | otherwise -> let (mc, _) = G.pow w e c in assemble mc True

-- | Left shift by a constant amount. @x << s = x · 2^s@, so the valuation gains
-- @s@; values whose valuation would reach @w@ become @0@. @0 << s = 0@.
-- Delegates to the kernel's 'G.shl', which reports whether @0@ can arise.
shl :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Domain w
shl w d s = case d of
  GBot         -> GBot
  GZero        -> GZero
  GNonzero c   -> uncurry assemble (G.shl w c s)
  GMaybeZero c ->
    -- @0 << s = 0@, so @0@ remains regardless of overflow.
    let (mc, _) = G.shl w c s in assemble mc True

-- | The set @{1}@ as a 'Domain' (the multiplicative identity).
oneSet :: (3 <= w) => NatRepr w -> Domain w
oneSet w = GNonzero (G.one w)

-- | Split a 'GNonzero' \/ 'GMaybeZero' value into its kernel part and a flag for
-- whether @0@ is present. Other constructors are not expected here.
splitZero :: Domain w -> (G.Domain w, Bool)
splitZero = \case
  GNonzero c   -> (c, False)
  GMaybeZero c -> (c, True)
  _            -> error "Geometric.splitZero: expected a kernel-bearing value"

-- | Assemble an arithmetic result from a kernel result @(Maybe kernel)@ and a
-- flag for whether @0@ is in the result.
assemble :: Maybe (G.Domain w) -> Bool -> Domain w
assemble mc zeroPossible = case (mc, zeroPossible) of
  (Nothing, False) -> GBot           -- impossible for total ops, but safe
  (Nothing, True)  -> GZero
  (Just c, False)  -> GNonzero c
  (Just c, True)   -> GMaybeZero c

-- ------------------------------------------------------------------
-- * Lattice operations

-- ------------------------------------------------------------------
-- ** Joins

-- | Join (least upper bound). @0@ is tracked through 'GZero' \/ 'GMaybeZero';
-- nonzero parts join via the kernel.
pseudoJoin :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w
pseudoJoin w a b = case (a, b) of
  (GBot, y) -> y
  (x, GBot) -> x
  (GZero, GZero) -> GZero
  (GZero, y) -> addZero y
  (x, GZero) -> addZero x
  _ ->
    let (ka, za) = splitZero a
        (kb, zb) = splitZero b
        k = G.pseudoJoin w ka kb
    in if za || zb then GMaybeZero k else GNonzero k

-- | Add @0@ to a set (used by 'pseudoJoin' with 'GZero').
addZero :: Domain w -> Domain w
addZero = \case
  GBot         -> GZero
  GZero        -> GZero
  GNonzero c   -> GMaybeZero c
  GMaybeZero c -> GMaybeZero c

-- ------------------------------------------------------------------
-- ** Meets

-- | Meet (a sound over-approximation of intersection). @0@ is in the meet iff
-- it is in both operands; the nonzero parts meet via the kernel.
pseudoMeet :: (3 <= w) => NatRepr w -> Domain w -> Domain w -> Maybe (Domain w)
pseudoMeet w a b = case (a, b) of
  (GBot, _) -> Nothing
  (_, GBot) -> Nothing
  (GZero, y) -> if member w y 0 then Just GZero else Nothing
  (x, GZero) -> if member w x 0 then Just GZero else Nothing
  _ ->
    let (ka, za) = splitZero a
        (kb, zb) = splitZero b
        bothZero = za && zb
        kmeet = G.pseudoMeet w ka kb
    in case (kmeet, bothZero) of
         (Just k, False) -> Just (GNonzero k)
         (Just k, True)  -> Just (GMaybeZero k)
         (Nothing, True) -> Just GZero
         (Nothing, False) -> Nothing

-- ------------------------------------------------------------------
-- * Generators

-- | Generate a random domain element, including the sentinels.
genDomain :: (3 <= w) => NatRepr w -> Gen (Domain w)
genDomain w = do
  tag <- chooseInt (0, 4)
  case tag of
    0 -> pure GBot
    1 -> pure GZero
    2 -> GNonzero <$> G.genDomain w
    _ -> GMaybeZero <$> G.genDomain w

-- | Generate a random element of a (nonempty) domain value.
genElement :: (3 <= w) => NatRepr w -> Domain w -> Gen Natural
genElement w d = case d of
  GBot         -> pure 0   -- empty; caller filters via membership precondition
  GZero        -> pure 0
  GNonzero c   -> G.genElement w c
  GMaybeZero c -> do
    b <- chooseInt (0, 1)
    if b == 0 then pure 0 else G.genElement w c

-- | Generate a domain value paired with a member of it.
genPair :: (3 <= w) => NatRepr w -> Gen (Domain w, Natural)
genPair w = do
  c <- genDomain w
  x <- genElement w c
  pure (c, x)

-- ------------------------------------------------------------------
-- * Properties

-- ------------------------------------------------------------------
-- ** Queries

-- | Every member produced by 'toList' is a 'member'.
memberToList :: (3 <= w) => NatRepr w -> Domain w -> Property
memberToList w c = property (Prelude.all (member w c) (toList w c))

-- | A generated member appears in 'toList'.
toListMember :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Property
toListMember w c x = member w c x ==> property (x `elem` toList w c)

-- ------------------------------------------------------------------
-- ** Arithmetic

-- | Soundness of 'negate'.
correct_neg :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_neg w c x =
  member w c x ==> property (member w (negate w c) (modNeg w x))

-- | Soundness of 'mul'.
correct_mul ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_mul w a x b y =
  member w a x ==> member w b y ==>
    property (member w (mul w a b) (modMul w x y))

-- | Soundness of 'square'.
correct_square :: (3 <= w) => NatRepr w -> Domain w -> Natural -> Property
correct_square w c x =
  member w c x ==> property (member w (square w c) (modMul w x x))

-- | Soundness of 'pow' for small nonnegative exponents.
correct_pow ::
  (3 <= w) => NatRepr w -> Int -> Domain w -> Natural -> Property
correct_pow w eRaw c x =
  member w c x ==> property (member w (pow w e c) (modPow w x e))
  where e = toInteger (eRaw `mod` 6)

-- | Soundness of 'shl' for small constant shifts.
correct_shl ::
  (3 <= w) => NatRepr w -> Int -> Domain w -> Natural -> Property
correct_shl w sRaw c x =
  member w c x ==>
    property (member w (shl w c s) (modShl w x s))
  where s = fromIntegral (sRaw `mod` (fromIntegral (NR.natValue w) + 2))

-- ------------------------------------------------------------------
-- ** Lattice

-- | Soundness of 'pseudoJoin'.
correct_pseudoJoin ::
  (3 <= w) =>
  NatRepr w -> Domain w -> Natural -> Domain w -> Natural -> Property
correct_pseudoJoin w a x b y = property (leftOK && rightOK)
  where
    j = pseudoJoin w a b
    leftOK  = not (member w a x) || member w j x
    rightOK = not (member w b y) || member w j y

-- | Soundness of 'pseudoMeet': a value in both operands is in the meet.
correct_pseudoMeet ::
  (3 <= w) => NatRepr w -> Domain w -> Domain w -> Natural -> Property
correct_pseudoMeet w a b x =
  (member w a x && member w b x) ==>
    property (case pseudoMeet w a b of
                Nothing -> False
                Just c  -> member w c x)

-- | 'leq' is reflexive.
leqReflexive :: (3 <= w) => NatRepr w -> Domain w -> Property
leqReflexive w c = property (leq w c c)

-- | 'leq' is transitive.
leqTransitive ::
  (3 <= w) => NatRepr w -> Domain w -> Domain w -> Domain w -> Property
leqTransitive w a b c =
  (leq w a b && leq w b c) ==> property (leq w a c)

-- ------------------------------------------------------------------
-- Concrete oracles for the property tests.

modMask :: NatRepr w -> Natural -> Natural
modMask w x = x `mod` (1 `shiftL` NR.widthVal w)

modNeg :: NatRepr w -> Natural -> Natural
modNeg w x = modMask w (m - modMask w x) where m = 1 `shiftL` NR.widthVal w

modMul :: NatRepr w -> Natural -> Natural -> Natural
modMul w x y = modMask w (x * y)

modPow :: NatRepr w -> Natural -> Integer -> Natural
modPow w x e = go 1 (modMask w x) e
  where
    go acc _ 0 = acc
    go acc b e' =
      let acc' = if Prelude.odd e' then modMul w acc b else acc
      in go acc' (modMul w b b) (e' `div` 2)

modShl :: NatRepr w -> Natural -> Natural -> Natural
modShl w x s = modMask w (x * (1 `shiftL` fromIntegral s))

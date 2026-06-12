{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Abstract values used to drive Who2 simplification.
--
-- This module defines a Who2-local abstract-value type family, 'AbsVal', that
-- replaces 'What4.Utils.AbstractDomains.AbstractValue' for bitvectors with
-- the strides domain ('What4.Domains.BV.Strides.Domain'). Non-bitvector base
-- types fall back to What4's own abstract-value type.
module Who2.Expr.AbsVal
  ( -- * Type family
    AbsVal
    -- * Class
  , HasAbsVal(..)
    -- * Construction
  , avTop
  , avSingle
    -- * Bitvector helpers
  , bvSingleton
  , bvAsSingleton
  , bvUbounds
  , bvSbounds
  , bvUlt
  , bvSlt
    -- * Equality on abstract values
  , avCheckEq
  , avJoin
    -- * Compatibility with What4's 'AD.AbstractValue'
  , toW4AbsValue
    -- * Strides domain wrappers (mirror the names of @What4.Utils.BVDomain@)
  , bvTop
  , bvAdd
  , bvNegate
  , bvSub
  , bvMul
  , bvScale
  , bvUdiv
  , bvUrem
  , bvSdiv
  , bvSrem
  , bvAnd
  , bvOr
  , bvXor
  , bvNot
  , bvShl
  , bvLshr
  , bvAshr
  , bvRol
  , bvRor
  , bvZext
  , bvSext
  , bvConcat
  , bvSelect
  , bvFromBV
  ) where

import Data.Bits ((.&.))
import Data.Kind (Type)
import Numeric.Natural (Natural)

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.NatRepr (NatRepr, type (<=), type (+))
import qualified Data.Parameterized.NatRepr as NR

import qualified What4.BaseTypes as BT
import           What4.BaseTypes
                   ( BaseType
                   , BaseBoolType
                   , BaseBVType
                   , BaseIntegerType
                   , BaseRealType
                   , BaseStringType
                   , BaseFloatType
                   , BaseComplexType
                   , BaseArrayType
                   , BaseStructType
                   )
import qualified What4.Utils.AbstractDomains as AD

import qualified What4.Domains.BV as BVD
import qualified What4.Domains.BV.Strides as Str
import qualified What4.Domains.BV.Arith as A

------------------------------------------------------------------------
-- Type family

-- | Who2's abstract-value family. Like
-- 'What4.Utils.AbstractDomains.AbstractValue', but bitvectors are represented
-- by a strides 'Str.Domain' instead of @What4.Domains.BV.BVDomain@.
type family AbsVal (tp :: BaseType) :: Type where
  AbsVal BaseBoolType        = Maybe Bool
  AbsVal (BaseBVType w)      = Str.Domain w
  AbsVal BaseIntegerType     = AD.AbstractValue BaseIntegerType
  AbsVal BaseRealType        = AD.AbstractValue BaseRealType
  AbsVal (BaseStringType si) = AD.AbstractValue (BaseStringType si)
  AbsVal (BaseFloatType fpp) = AD.AbstractValue (BaseFloatType fpp)
  AbsVal BaseComplexType     = AD.AbstractValue BaseComplexType
  AbsVal (BaseArrayType idx b) = AbsVal b
  AbsVal (BaseStructType ctx)  = AD.AbstractValue (BaseStructType ctx)

------------------------------------------------------------------------
-- Class

-- | Carriers of an 'AbsVal'.
class HasAbsVal f where
  getAbsVal :: f tp -> AbsVal tp

------------------------------------------------------------------------
-- Construction

-- | Top element: contains every concrete value.
avTop :: BT.BaseTypeRepr tp -> AbsVal tp
avTop = \case
  BT.BaseBoolRepr    -> Nothing
  BT.BaseBVRepr w    -> Str.top w
  BT.BaseIntegerRepr -> AD.avTop BT.BaseIntegerRepr
  BT.BaseRealRepr    -> AD.avTop BT.BaseRealRepr
  BT.BaseStringRepr si -> AD.avTop (BT.BaseStringRepr si)
  BT.BaseComplexRepr -> AD.avTop BT.BaseComplexRepr
  r@BT.BaseFloatRepr{} -> AD.avTop r
  BT.BaseArrayRepr _ b -> avTop b
  r@BT.BaseStructRepr{} -> AD.avTop r

-- | Singleton: contains exactly the given concrete value.
avSingle :: BT.BaseTypeRepr tp -> AD.ConcreteValue tp -> AbsVal tp
avSingle r v = case r of
  BT.BaseBoolRepr    -> Just v
  BT.BaseBVRepr w    -> bvSingleton w (toNat w v)
  BT.BaseIntegerRepr -> AD.avSingle BT.BaseIntegerRepr v
  BT.BaseRealRepr    -> AD.avSingle BT.BaseRealRepr v
  BT.BaseStringRepr si -> AD.avSingle (BT.BaseStringRepr si) v
  BT.BaseComplexRepr -> AD.avSingle BT.BaseComplexRepr v
  rf@BT.BaseFloatRepr{} -> AD.avSingle rf v
  BT.BaseArrayRepr _ b -> avTop b
  rs@BT.BaseStructRepr{} -> AD.avSingle rs v
  where
    toNat :: NatRepr w -> Integer -> Natural
    toNat w i = fromInteger (i .&. NR.maxUnsigned w)

------------------------------------------------------------------------
-- Bitvector helpers

-- | Strides singleton domain. Masks @v@ to the given width before construction.
bvSingleton :: NatRepr w -> Natural -> Str.Domain w
bvSingleton w v =
  Str.mk w (v .&. fromInteger (NR.maxUnsigned w)) 1 0

-- | If the domain represents exactly one concrete value, return it.
bvAsSingleton :: Str.Domain w -> Maybe Integer
bvAsSingleton d
  | Str.n d == 0 = Just (toInteger (Str.start d))
  | otherwise    = Nothing

-- | Unsigned bounds @(low, high)@.
bvUbounds :: Str.Domain w -> (Integer, Integer)
bvUbounds = A.ubounds . Str.toArith

-- | Signed bounds @(low, high)@.
bvSbounds :: (1 <= w) => NatRepr w -> Str.Domain w -> (Integer, Integer)
bvSbounds w = A.sbounds w . Str.toArith

-- | Unsigned-less-than: @Just b@ iff every member of one domain is on the
-- correct side of every member of the other.
bvUlt :: (1 <= w) => Str.Domain w -> Str.Domain w -> Maybe Bool
bvUlt a b = A.ult (Str.toArith a) (Str.toArith b)

-- | Signed-less-than, analogous to 'bvUlt'.
bvSlt :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Maybe Bool
bvSlt w a b = A.slt w (Str.toArith a) (Str.toArith b)

------------------------------------------------------------------------
-- Equality

-- | Decide @a = b@ on abstract values where possible.
avCheckEq :: forall tp. BT.BaseTypeRepr tp -> AbsVal tp -> AbsVal tp -> Maybe Bool
avCheckEq r x y = case r of
  BT.BaseBoolRepr -> case (x, y) of
    (Just a, Just b) -> Just (a == b)
    _ -> Nothing
  BT.BaseBVRepr _ -> bvCheckEq x y
  BT.BaseIntegerRepr -> AD.avCheckEq BT.BaseIntegerRepr x y
  BT.BaseRealRepr    -> AD.avCheckEq BT.BaseRealRepr x y
  BT.BaseStringRepr si -> AD.avCheckEq (BT.BaseStringRepr si) x y
  BT.BaseComplexRepr -> AD.avCheckEq BT.BaseComplexRepr x y
  rf@BT.BaseFloatRepr{} -> AD.avCheckEq rf x y
  BT.BaseArrayRepr _ b -> avCheckEq b x y
  rs@BT.BaseStructRepr{} -> AD.avCheckEq rs x y
  where
    bvCheckEq :: Str.Domain w -> Str.Domain w -> Maybe Bool
    bvCheckEq a b
      -- Both singletons: their concrete values determine equality.
      | Just av <- bvAsSingleton a
      , Just bv <- bvAsSingleton b = Just (av == bv)
      -- Disjoint domains: no concrete value lies in both, so the
      -- underlying expressions must differ.
      | not (A.domainsOverlap (Str.toArith a) (Str.toArith b)) = Just False
      | otherwise = Nothing

-- | Sound join (least upper bound).
avJoin :: forall tp. BT.BaseTypeRepr tp -> AbsVal tp -> AbsVal tp -> AbsVal tp
avJoin r x y = case r of
  BT.BaseBoolRepr | x == y -> x
                  | otherwise -> Nothing
  BT.BaseBVRepr w -> Str.pseudoJoin w x y
  BT.BaseIntegerRepr -> AD.withAbstractable r (AD.avJoin r x y)
  BT.BaseRealRepr    -> AD.withAbstractable r (AD.avJoin r x y)
  BT.BaseStringRepr _ -> AD.withAbstractable r (AD.avJoin r x y)
  BT.BaseComplexRepr -> AD.withAbstractable r (AD.avJoin r x y)
  BT.BaseFloatRepr{} -> AD.withAbstractable r (AD.avJoin r x y)
  BT.BaseArrayRepr _ b -> avJoin b x y
  BT.BaseStructRepr{} -> AD.withAbstractable r (AD.avJoin r x y)

------------------------------------------------------------------------
-- Compatibility with What4's 'AD.AbstractValue'

-- | Convert an 'AbsVal' back to the What4 'AD.AbstractValue' family. For
-- bitvectors this lifts the strides domain to a 'BVD.BVDomain' via
-- 'Str.toArith'; for other types this is the identity.
--
-- Used at the 'WI.IsExpr' interface boundary, where consumers expect
-- 'AD.AbstractValue tp'.
toW4AbsValue :: forall tp. BT.BaseTypeRepr tp -> AbsVal tp -> AD.AbstractValue tp
toW4AbsValue r v = case r of
  BT.BaseBoolRepr -> v
  BT.BaseBVRepr _ -> BVD.BVDArith (Str.toArith v)
  BT.BaseIntegerRepr -> v
  BT.BaseRealRepr    -> v
  BT.BaseStringRepr _ -> v
  BT.BaseComplexRepr -> v
  BT.BaseFloatRepr{} -> v
  BT.BaseArrayRepr _ b -> toW4AbsValue b v
  BT.BaseStructRepr{} -> v

------------------------------------------------------------------------
-- Strides-domain wrappers
--
-- Each of these mirrors the same-named operation in @What4.Utils.BVDomain@,
-- but threads the 'NatRepr' through the strides API.

bvTop :: NatRepr w -> Str.Domain w
bvTop = Str.top

bvAdd :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvAdd = Str.add

bvNegate :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w
bvNegate = Str.negate

bvSub :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvSub = Str.sub

bvMul :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvMul = Str.mul

bvScale :: (1 <= w) => NatRepr w -> Natural -> Str.Domain w -> Str.Domain w
bvScale w k = Str.scale w (toInteger k)

bvUdiv :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvUdiv = Str.udiv

bvUrem :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvUrem = Str.urem

bvSdiv :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvSdiv = Str.sdiv

bvSrem :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvSrem = Str.srem

bvAnd :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvAnd = Str.and

bvOr :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvOr = Str.or

bvXor :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvXor = Str.xor

bvNot :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w
bvNot = Str.not

bvShl :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvShl = Str.shl

bvLshr :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvLshr = Str.lshr

bvAshr :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvAshr = Str.ashr

bvRol :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvRol = Str.rol

bvRor :: (1 <= w) => NatRepr w -> Str.Domain w -> Str.Domain w -> Str.Domain w
bvRor = Str.ror

bvZext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Str.Domain w -> NatRepr u -> Str.Domain u
bvZext = Str.zext

bvSext ::
  (1 <= w, w + 1 <= u) =>
  NatRepr w -> Str.Domain w -> NatRepr u -> Str.Domain u
bvSext = Str.sext

bvConcat ::
  (1 <= u, 1 <= v) =>
  NatRepr u -> Str.Domain u -> NatRepr v -> Str.Domain v -> Str.Domain (u + v)
bvConcat = Str.concat

bvSelect ::
  (1 <= n, 1 <= w, i + n <= w) =>
  NatRepr i -> NatRepr n -> NatRepr w -> Str.Domain w -> Str.Domain n
bvSelect = Str.select

-- | Convert a concrete 'BV.BV' to a singleton strides domain.
bvFromBV :: NatRepr w -> BV.BV w -> Str.Domain w
bvFromBV w bv = bvSingleton w (fromInteger (BV.asUnsigned bv))

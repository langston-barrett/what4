{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Who2.Expr.SymExpr
  ( SymExpr(SymExpr, getSymExpr)
  ) where

import qualified Data.BitVector.Sized as BV
import qualified Prettyprinter as PP

import qualified Data.Parameterized.Classes as PC

import qualified What4.BaseTypes as BT
import qualified What4.Interface as WI
import qualified What4.Utils.AbstractDomains as AD

import Who2.Expr.App (App)
import Who2.Expr (Expr)
import qualified Who2.Expr as E
import qualified Who2.Expr.AbsVal as AV
import qualified Who2.Expr.App as App
import Who2.Unsupported (unsupported)

newtype SymExpr t tp
  = SymExpr { getSymExpr :: Expr t (App t) tp }

deriving instance AV.HasAbsVal (SymExpr t)
deriving instance E.HasBaseType (SymExpr t)

-- | What4's 'AD.HasAbsValue' is required as a superclass of 'WI.IsExpr'. We
-- bridge by translating Who2's strides-backed 'AV.AbsVal' into What4's
-- 'AD.AbstractValue' type family.
instance AD.HasAbsValue (SymExpr t) where
  getAbsValue e = AV.toW4AbsValue (E.baseType e) (AV.getAbsVal e)
  {-# INLINE getAbsValue #-}

-- test-law: propTestEqualityHashConsistent
deriving instance PC.HashableF (SymExpr t)

-- test-law: propOrdFReflexive
-- test-law: propOrdFAntisymmetric
-- test-law: propOrdFTransitive
-- test-law: propOrdFConsistentWithTestEquality
deriving instance PC.OrdF (SymExpr t)

-- test-law: propTestEqualityReflexive
-- test-law: propTestEqualitySymmetric
-- test-law: propTestEqualityTransitive
-- test-law: propTestEqualityHashConsistent
deriving instance PC.TestEquality (SymExpr t)

instance PP.Pretty (SymExpr t tp) where
  pretty = ppSymExpr
    where
      ppSymExpr :: forall ann tp'. SymExpr t tp' -> PP.Doc ann
      ppSymExpr (SymExpr e) = E.pretty ppApp e

      ppApp :: forall ann tp'. App t (Expr t (App t)) tp' -> PP.Doc ann
      ppApp = App.pretty (ppSymExpr . SymExpr)

instance WI.IsExpr (SymExpr t) where
  exprType = E.baseType

  asConstantPred e = AV.getAbsVal e

  asBV e =
    case E.baseType e of
      BT.BaseBVRepr w -> BV.mkBV w <$> AV.bvAsSingleton (AV.getAbsVal e)

  integerBounds = unsupported "Who2.Expr.SymExpr.integerBounds"

  asFloat = unsupported "Who2.Expr.SymExpr.asFloat"

  rationalBounds = unsupported "Who2.Expr.SymExpr.rationalBounds"

  unsignedBVBounds e =
    case E.baseType e of
      BT.BaseBVRepr _ -> Just $ AV.bvUbounds (AV.getAbsVal e)

  signedBVBounds e =
    case E.baseType e of
      BT.BaseBVRepr w -> Just $ AV.bvSbounds w (AV.getAbsVal e)

  asAffineVar = unsupported "Who2.Expr.SymExpr.asAffineVar"

  printSymExpr = PP.pretty

  unsafeSetAbstractValue _av (SymExpr e) =
    -- The What4 interface threads its own 'AbstractValue', which we don't use
    -- internally. We ignore the value rather than translating, which is
    -- sound: the field is a hint, not a constraint.
    SymExpr e

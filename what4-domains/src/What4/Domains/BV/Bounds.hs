{-|
Module      : What4.Domains.BV.Bounds
Copyright   : (c) Galois Inc, 2026
License     : BSD3

Numeric value-range bounds for bitvector abstract-domain elements.

These types let one domain pass an operand's value range into another domain's
transfer functions — used by the reduced product
"What4.Domains.BV.StridesBitwise", where the strides component supplies bounds
strictly tighter than the bitwise component's bit-pattern bounds can express.

A distinct type — rather than a bare @(Integer, Integer)@ — keeps these from
being confused with the several other @(Integer, Integer)@ pairs in this package
(bit-pattern bounds, signed bounds, known zeros\/ones).
-}

{-# LANGUAGE BangPatterns #-}

module What4.Domains.BV.Bounds
  ( UnsignedBounds(..)
  ) where

-- | An unsigned value range @[ubLow, ubHigh]@ (inclusive).
data UnsignedBounds = UnsignedBounds
  { ubLow  :: !Integer
    -- ^ Inclusive lower bound.
  , ubHigh :: !Integer
    -- ^ Inclusive upper bound.
  }
  deriving (Eq, Show)

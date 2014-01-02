{-# LANGUAGE
  DeriveDataTypeable #-}

{- |
Module      :  Data.Nimber
Description :  Finite nimber arithmetic
Copyright   :  © Anders Kaseorg, 2013
License     :  BSD-style

Maintainer  :  Anders Kaseorg <andersk@mit.edu>
Stability   :  experimental
Portability :  Non-portable (GHC extensions)

The finite nimbers, 'Nimber', are a quadratically closed field of
characteristic 2 introduced in combinatorial game theory.

>>> 257 + 258 :: Nimber
*3
>>> sqrt 123456789 :: Nimber
*98433322
>>> 123456789/sqrt 123456789 :: Nimber
*98433322

This implementation was inspired by Patrick Hurst’s slow Haskell
implementation that this replaced (with his permission), and by Michel
Van den Bergh’s Python implementation at
<https://web.archive.org/web/20101124110959/http://alpha.uhasselt.be/Research/Algebra/Members/nimbers/nimbers.py>.
-}

module Data.Nimber (
  Nimber,
  fromNimber,
  NimberException (..),
  ) where

import Control.Exception (Exception, ArithException (..), throw)
import Data.Bits
import Data.Ratio
import Data.Typeable
import Math.NumberTheory.Logarithms

-- |The type of exceptions thrown by impossible 'Nimber' operations.
data NimberException =
  -- |A negative integer was converted to a nimber.
  NegativeNimber |
  -- |A transcendental function was called on nimbers.
  Innimerable String
  deriving (Eq, Ord, Typeable)

instance Show NimberException where
  showsPrec _ (NegativeNimber) =
    showString "nimbers cannot be negative"
  showsPrec _ (Innimerable s) =
    showString "nimbers do not support " . showString s

instance Exception NimberException

-- |The type of finite nimbers.
newtype Nimber = Nimber Integer deriving (Eq, Ord)

nimSize :: Nimber -> Int
nimSize (Nimber a) = bit (intLog2 (integerLog2 a))

nimSplit :: Int -> Nimber -> (Nimber, Nimber)
nimSplit k = \(Nimber a) -> (Nimber (a `shiftR` k), Nimber (a .&. mask)) where
  mask = complement (-1 `shiftL` k)

nimJoin :: Int -> (Nimber, Nimber) -> Nimber
nimJoin k (Nimber a1, Nimber a0) = Nimber ((a1 `shiftL` k) .|. a0)

nimBit :: Int -> Nimber
nimBit i = Nimber (bit i)

nimSqr :: Nimber -> Nimber
nimSqr 0 = 0
nimSqr 1 = 1
nimSqr a = nimJoin k (p1, p0 + p1 * nimBit (k - 1)) where
  k = nimSize a
  (a1, a0) = nimSplit k a
  p0 = nimSqr a0
  p1 = nimSqr a1

instance Show Nimber where
  showsPrec d (Nimber a) = showParen (d > 7) $ showChar '*' . showsPrec 8 a

instance Read Nimber where
  readsPrec d = readParen (d > 7) $ \s -> case s of
    '*' : s1 -> [(fromInteger a, s2) | (a, s2) <- readsPrec 8 s1]
    _ -> []

instance Enum Nimber where
  pred (Nimber a) = fromInteger (pred a)
  succ (Nimber a) = fromInteger (succ a)
  toEnum a = fromInteger (toEnum a)
  fromEnum (Nimber a) = fromEnum a

instance Num Nimber where
  Nimber a + Nimber b = Nimber (a `xor` b)

  0 * _ = 0
  _ * 0 = 0
  1 * a = a
  a * 1 = a
  a * b | a == b = nimSqr a
  a * b = nimJoin k (p0 + (a0 + a1) * (b0 + b1), p0 + p1 * nimBit (k - 1)) where
    k = max (nimSize a) (nimSize b)
    split = nimSplit k
    (a1, a0) = split a
    (b1, b0) = split b
    p0 = a0 * b0
    p1 = a1 * b1

  (-) = (+)
  negate = id
  abs = id
  signum 0 = 0
  signum _ = 1
  fromInteger a
    | a >= 0 = Nimber a
    | otherwise = throw NegativeNimber

{- |
Note: Although nimbers support division, the 'fromRational' operation
makes little sense because 'Rational's are reduced according to
ordinary multiplication instead of nimber multiplication.
-}
instance Fractional Nimber where
  recip 0 = throw DivideByZero
  recip 1 = 1
  recip a = (a + a1) * recip b where
    k = nimSize a
    (a1, a0) = nimSplit k a
    b = a0 * (a0 + a1) + a1 * a1 * nimBit (k - 1)

  fromRational r = fromInteger (numerator r) / fromInteger (denominator r)

{- |
This partial 'Floating' instance only supports 'sqrt'.  All other
operations will throw the 'Innimerable' exception.
-}
instance Floating Nimber where
  sqrt 0 = 0
  sqrt 1 = 1
  sqrt a = nimJoin k (sqrt a1, sqrt (a1 * nimBit (k - 1) + a0)) where
    k = nimSize a
    (a1, a0) = nimSplit k a

  pi = throw (Innimerable "pi")
  exp = throw (Innimerable "exp")
  log = throw (Innimerable "log")
  (**) = throw (Innimerable "**")
  logBase = throw (Innimerable "logBase")
  sin = throw (Innimerable "sin")
  tan = throw (Innimerable "tan")
  cos = throw (Innimerable "cos")
  asin = throw (Innimerable "asin")
  atan = throw (Innimerable "atan")
  acos = throw (Innimerable "acos")
  sinh = throw (Innimerable "sinh")
  tanh = throw (Innimerable "tanh")
  cosh = throw (Innimerable "cosh")
  asinh = throw (Innimerable "asinh")
  atanh = throw (Innimerable "atanh")
  acosh = throw (Innimerable "acosh")

-- |Convert a 'Nimber' to the corresponding natural number.
fromNimber :: Nimber -> Integer
fromNimber (Nimber a) = a

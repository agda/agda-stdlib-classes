{-# OPTIONS --cubical-compatible #-}
module Class.HasAdd.Instances where

open import Class.Prelude
open import Class.HasAdd.Core

instance
  addNat : HasAdd ℕ
  addNat ._+_ = Nat._+_

  addInt : HasAdd ℤ
  addInt ._+_ = Int._+_

  addRat : HasAdd ℚ
  addRat ._+_ = Q._+_

  addString : HasAdd String
  addString ._+_ = Str._++_

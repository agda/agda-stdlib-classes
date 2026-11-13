{-# OPTIONS --without-K #-}
module Class.Show.Core where

open import Class.Prelude
open import Class.Core

record Show (A : Type ℓ) : Type ℓ where
  constructor mkShow
  field show : A → String
open Show ⦃...⦄ public

Show¹ = Show ¹
Show² = Show ²
Show³ = Show ³

{-# OPTIONS --cubical-compatible #-}
module Class.Default.Core where

open import Class.Prelude

record Default (A : Type ℓ) : Type ℓ where
  field def : A
open Default ⦃...⦄ public

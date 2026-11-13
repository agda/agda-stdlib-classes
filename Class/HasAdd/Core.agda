{-# OPTIONS --without-K #-}
module Class.HasAdd.Core where

open import Class.Prelude

record HasAdd (A : Type ℓ) : Type ℓ where
  infixl 6 _+_
  field _+_ : A → A → A

open HasAdd ⦃...⦄ public

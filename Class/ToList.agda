{-# OPTIONS --cubical-compatible #-}
module Class.ToList where

open import Class.Prelude

record ToList (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field toList : A → List B
  _∙toList = toList
open ToList ⦃...⦄ public

instance
  ToList-List : ToList (List A) A
  ToList-List .toList = id

  ToList-List⁺ : ToList (List⁺ A) A
  ToList-List⁺ .toList = L⁺.toList

  ToList-Str : ToList String Char
  ToList-Str .toList = Str.toList

  ToList-Vec : ∀ {n} → ToList (Vec A n) A
  ToList-Vec .toList = V.toList

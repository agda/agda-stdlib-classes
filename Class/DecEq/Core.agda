{-# OPTIONS --cubical-compatible #-}
module Class.DecEq.Core where

open import Class.Prelude
open import Class.Core

record DecEq (A : Type ℓ) : Type ℓ where
  field _≟_ : DecidableEquality A

  -- lazy (c.f. James Wood's SPLS'19 talk "A Bool in the Hand is Worth Two in the Bush")
  _==_ _≠_ : A → A → Bool
  _==_ = does ∘₂ _≟_
  _≠_  = not  ∘₂ _==_

  -- strict
  _≡ᵇ_ _≢ᵇ_ : A → A → Bool
  _≡ᵇ_ = isYes ∘₂ _≟_
  _≢ᵇ_ = not   ∘₂ _≡ᵇ_

  infix 4 _≟_ _==_ _≠_ _≡ᵇ_ _≢ᵇ_
open DecEq ⦃...⦄ public

DecEq¹ = DecEq ¹
DecEq² = DecEq ²
DecEq³ = DecEq ³

Irrelevant⇒DecEq : Irrelevant A → DecEq A
Irrelevant⇒DecEq ∀≡ ._≟_ = yes ∘₂ ∀≡

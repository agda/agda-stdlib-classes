{-# OPTIONS --cubical-compatible #-}
module Class.HasMembership.Core where

open import Relation.Nullary.Decidable using (¬?)

open import Class.Prelude
open import Class.Decidable.Core
open import Class.Decidable.Instances

record HasMembership (F : Type ℓ → Type ℓ) : Type (lsuc $ lsuc ℓ) where
  infix 4 _∈_ _∉_
  field _∈_ : A → F A → Type ℓ

  _∉_ : A → F A → Type ℓ
  _∉_ = ¬_ ∘₂ _∈_

  module _ ⦃ _ : _∈_ {A = A} ⁇² ⦄ where
    infix 4  _∈?_ _∉?_ _∈ᵇ_ _∉ᵇ_

    _∈?_ : Decidable² {A = A} _∈_
    _∈?_ = dec²

    _∉?_ : Decidable² {A = A} _∉_
    _∉?_ = dec²

    _∈ᵇ_ _∉ᵇ_ : A → F A → Bool
    _∈ᵇ_ = isYes ∘₂ _∈?_
    _∉ᵇ_ = isYes ∘₂ _∉?_

open HasMembership ⦃...⦄ public

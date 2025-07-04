{-# OPTIONS --without-K #-}
module Class.Setoid.Dec where

open import Class.Prelude
open import Class.Decidable
open import Class.Setoid.Core

DecSetoid : ∀ (A : Type ℓ) ⦃ _ : ISetoid A ⦄ → Type (ℓ ⊔ relℓ)
DecSetoid A = _≈_ {A = A} ⁇²

module _ {A : Type ℓ} ⦃ _ : ISetoid A ⦄ ⦃ _ : DecSetoid A ⦄ where
  infix 4 _≈?_ _≉?_
  _≈?_ : Decidable² _≈_
  _≈?_ = dec²
  _≉?_ : Decidable² _≉_
  _≉?_ = dec²

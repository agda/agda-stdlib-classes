{-# OPTIONS --cubical-compatible #-}
module Class.Core where

open import Class.Prelude

Type[_↝_] : ∀ ℓ ℓ′ → Type (lsuc ℓ ⊔ lsuc ℓ′)
Type[ ℓ ↝ ℓ′ ] = Type ℓ → Type ℓ′

Level↑ = Level → Level

variable ℓ↑ ℓ↑′ ℓ↑″ : Level↑

Type↑ : Level↑ → Typeω
Type↑ ℓ↑ = ∀ {ℓ} → Type[ ℓ ↝ ℓ↑ ℓ ]

variable M F : Type↑ ℓ↑

module _ (M : Type↑ ℓ↑) where
  _¹ : (A → Type ℓ) → Type _
  _¹ P = ∀ {x} → M (P x)

  _² : (A → B → Type ℓ) → Type _
  _² _~_ = ∀ {x y} → M (x ~ y)

  _³ : (A → B → C → Type ℓ) → Type _
  _³ _~_~_ = ∀ {x y z} → M (x ~ y ~ z)

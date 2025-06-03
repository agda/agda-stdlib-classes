{-# OPTIONS --cubical-compatible #-}
module Class.Core where

open import Class.Prelude

-- ** unary type formers

Type[_↝_] : ∀ ℓ ℓ′ → Type _
Type[ ℓ ↝ ℓ′ ] = Type ℓ → Type ℓ′

Level↑ = Level → Level

variable ℓ↑ ℓ↑′ : Level↑

Type↑ : Level↑ → Level↑ → Typeω
Type↑ ℓ↑ ℓ↑′ = ∀ {ℓ} → Type[ ℓ↑ ℓ ↝ ℓ↑′ ℓ ]

variable M F : Type↑ ℓ↑ ℓ↑′

-- ** binary type formers

Type[_∣_↝_] : ∀ ℓ ℓ′ ℓ″ → Type _
Type[ ℓ ∣ ℓ′ ↝ ℓ″ ] = Type ℓ → Type ℓ′ → Type ℓ″

Level↑² = Level → Level → Level

Type↑² : Level↑ → Level↑ → Level↑² → Typeω
Type↑² ℓ↑ ℓ↑′ ℓ↑² = ∀ {ℓ ℓ′} → Type[ ℓ↑ ℓ ∣ ℓ↑′ ℓ′ ↝ ℓ↑² ℓ ℓ′ ]

variable ℓ↑² ℓ↑²′ : Level → Level → Level

module _ (M : Type↑ id ℓ↑′) where
  _¹ : (A → Type ℓ) → Type _
  _¹ P = ∀ {x} → M (P x)

  _² : (A → B → Type ℓ) → Type _
  _² _~_ = ∀ {x y} → M (x ~ y)

  _³ : (A → B → C → Type ℓ) → Type _
  _³ _~_~_ = ∀ {x y z} → M (x ~ y ~ z)

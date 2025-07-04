{-# OPTIONS --cubical-compatible #-}
module Class.ToZ where

open import Class.Prelude
open import Class.ToN

record Toℤ (A : Type ℓ) : Type ℓ where
  field toℤ : A → ℤ
open Toℤ ⦃...⦄ public

instance
  Toℤ-ℤ = Toℤ ℤ ∋ λ where .toℤ → id

  Toℕ⇒Toℤ : ∀ {A : Type ℓ} → ⦃ Toℕ A ⦄ → Toℤ A
  Toℕ⇒Toℤ .toℤ = Int.+_ ∘ toℕ

{-# OPTIONS --cubical-compatible #-}
module Class.Anyable.Core where

open import Class.Prelude

record Anyable (F : Type ℓ → Type ℓ) : Typeω where
  field Any : ∀ {A} → (A → Type ℓ′) → F A → Type (ℓ ⊔ ℓ′)

  ∃∈-syntax  = Any
  ∃∈-syntax′ = Any
  ∄∈-syntax  = λ {A} {ℓ′} (P : A → Type ℓ′) → ¬_ ∘ Any P
  ∄∈-syntax′ = ∄∈-syntax
  infix 2 ∃∈-syntax ∃∈-syntax′ ∄∈-syntax ∄∈-syntax′
  syntax ∃∈-syntax  P         xs = ∃[∈    xs ] P
  syntax ∃∈-syntax′ (λ x → P) xs = ∃[ x ∈ xs ] P
  syntax ∄∈-syntax  P         xs = ∄[∈    xs ] P
  syntax ∄∈-syntax′ (λ x → P) xs = ∄[ x ∈ xs ] P

open Anyable ⦃...⦄ public

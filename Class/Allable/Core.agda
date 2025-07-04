{-# OPTIONS --cubical-compatible #-}
module Class.Allable.Core where

open import Class.Prelude

record Allable (F : Type ℓ → Type ℓ) : Typeω where
  field All : ∀ {A} → (A → Type ℓ′) → F A → Type (ℓ ⊔ ℓ′)

  ∀∈-syntax   = All
  ∀∈-syntax′  = All
  ¬∀∈-syntax  = λ {A} {ℓ′} (P : A → Type ℓ′) → ¬_ ∘ All P
  ¬∀∈-syntax′ = ¬∀∈-syntax
  infix 2 ∀∈-syntax ∀∈-syntax′ ¬∀∈-syntax ¬∀∈-syntax′
  syntax ∀∈-syntax   P         xs = ∀[∈     xs ] P
  syntax ∀∈-syntax′  (λ x → P) xs = ∀[  x ∈ xs ] P
  syntax ¬∀∈-syntax  P         xs = ¬∀[∈    xs ] P
  syntax ¬∀∈-syntax′ (λ x → P) xs = ¬∀[ x ∈ xs ] P

open Allable ⦃...⦄ public

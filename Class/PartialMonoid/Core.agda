{-# OPTIONS --cubical-compatible #-}
module Class.PartialMonoid.Core where

open import Class.Prelude
open import Class.Core
open import Class.Setoid.Core
open import Class.Setoid.Instances
open import Class.PartialSemigroup

record PartialMonoid (A : Type ℓ) ⦃ _ : PartialSemigroup A ⦄ : Type ℓ where
  field ε◆ : A
open PartialMonoid ⦃...⦄ public

record PartialMonoidLaws
  (A : Type ℓ)
  ⦃ _ : PartialSemigroup A ⦄
  ⦃ _ : PartialMonoid A ⦄
  ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
  : Type (ℓ ⊔ relℓ {A = A})
  where
  field ε◆-identity : ∀ (x : A) → (ε◆ ◆ x ≈ just x) × (x ◆ ε◆ ≈ just x)

  ε◆-identityˡ : ∀ (x : A) → ε◆ ◆ x ≈ just x
  ε◆-identityˡ = proj₁ ∘ ε◆-identity

  ε◆-identityʳ : ∀ (x : A) → x ◆ ε◆ ≈ just x
  ε◆-identityʳ = proj₂ ∘ ε◆-identity
open PartialMonoidLaws ⦃...⦄ public

PartialMonoidLaws≡ : (A : Type ℓ) ⦃ _ : PartialSemigroup A ⦄
                   → ⦃ PartialMonoid A ⦄ → Type ℓ
PartialMonoidLaws≡ A = PartialMonoidLaws A
  where instance _ = mkISetoid≡; _ = mkSetoidLaws≡

open import Class.Semigroup
open import Class.Monoid

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ where
    instance _ = Semigroup⇒Partial
    Monoid⇒Partial : PartialMonoid A
    Monoid⇒Partial .ε◆ = ε
    instance _ = Monoid⇒Partial

    MonoidLaws⇒Partial
      : ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
      → ⦃ _ : PartialSemigroupLaws A ⦄
      → ⦃ _ : MonoidLaws A ⦄
      → PartialMonoidLaws A
    MonoidLaws⇒Partial .ε◆-identity _ = ε-identityˡ _ , ε-identityʳ _

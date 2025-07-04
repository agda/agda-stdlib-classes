{-# OPTIONS --cubical-compatible #-}
module Class.Monoid.Core where

open import Class.Prelude
open import Class.Semigroup
open import Class.Setoid.Core

record Monoid (A : Type ℓ) ⦃ _ : Semigroup A ⦄ : Type ℓ where
  field ε : A
open Monoid ⦃...⦄ public

module _ (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ where

  record MonoidLaws ⦃ _ : ISetoid A ⦄ : Type (ℓ ⊔ relℓ) where
    open Alg _≈_
    field ε-identity : Identity ε _◇_
    ε-identityˡ = LeftIdentity  ε _◇_ ∋ ε-identity .proj₁
    ε-identityʳ = RightIdentity ε _◇_ ∋ ε-identity .proj₂

  MonoidLaws≡ : Type _
  MonoidLaws≡ = MonoidLaws
    where instance _ = mkISetoid≡; _ = mkSetoidLaws≡

open MonoidLaws ⦃...⦄ public

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : MonoidLaws≡ A ⦄ where
  instance _ = mkISetoid≡; _ = mkSetoidLaws≡
  open MonoidLaws it public
    renaming ( ε-identity to ε-identity≡
             ; ε-identityˡ to ε-identityˡ≡; ε-identityʳ to ε-identityʳ≡ )

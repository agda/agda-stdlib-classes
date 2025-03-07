{-# OPTIONS --cubical-compatible #-}
module Class.Monoid.Core where

open import Class.Prelude
open import Class.Semigroup

record Monoid (A : Type ℓ) ⦃ _ : Semigroup A ⦄ : Type ℓ where
  field ε : A
open Monoid ⦃...⦄ public

module _ (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ where
  record MonoidLaws (_≈_ : Rel A ℓ′) : Type (ℓ ⊔ ℓ′) where
    open Alg _≈_
    field ε-identity : Identity ε _◇_
    ε-identityˡ = LeftIdentity  ε _◇_ ∋ ε-identity .proj₁
    ε-identityʳ = RightIdentity ε _◇_ ∋ ε-identity .proj₂
  open MonoidLaws ⦃...⦄ public

  MonoidLaws≡ : Type ℓ
  MonoidLaws≡ = MonoidLaws _≡_

open MonoidLaws ⦃...⦄ public
  renaming ( ε-identity to ε-identity≡
           ; ε-identityˡ to ε-identityˡ≡; ε-identityʳ to ε-identityʳ≡ )

mconcat : {M : Type ℓ} → ⦃ _ : Semigroup M ⦄ → ⦃ Monoid M ⦄ -> List M -> M
mconcat [] = ε
mconcat (x ∷ l) = x ◇ mconcat l

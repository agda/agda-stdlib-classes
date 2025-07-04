{-# OPTIONS --cubical-compatible #-}
module Class.Semigroup.Core where

open import Class.Prelude
open import Class.Setoid.Core

record Semigroup (A : Type ℓ) : Type ℓ where
  infixr 5 _◇_ _<>_
  field _◇_ : A → A → A
  _<>_ = _◇_
open Semigroup ⦃...⦄ public

module _ (A : Type ℓ) ⦃ _ : Semigroup A ⦄ where
  record SemigroupLaws ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ : Type (ℓ ⊔ relℓ) where
    open Alg _≈_
    field ◇-comm   : Commutative _◇_
          ◇-assocʳ : Associative _◇_

    ◇-assocˡ : ∀ (x y z : A) → (x ◇ (y ◇ z)) ≈ ((x ◇ y) ◇ z)
    ◇-assocˡ x y z = ≈-sym (◇-assocʳ x y z)

  instance _ = mkISetoid≡; _ = mkSetoidLaws≡

  SemigroupLaws≡ : Type ℓ
  SemigroupLaws≡ = SemigroupLaws

open SemigroupLaws ⦃...⦄ public

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : SemigroupLaws≡ A ⦄ where

  instance _ = mkISetoid≡; _ = mkSetoidLaws≡

  open SemigroupLaws it public
    renaming (◇-comm to ◇-comm≡; ◇-assocʳ to ◇-assocʳ≡; ◇-assocˡ to ◇-assocˡ≡)

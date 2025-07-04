{-# OPTIONS --cubical-compatible #-}
module Class.Group where

open import Class.Prelude
open import Class.Semigroup
open import Class.Monoid
open import Class.Setoid.Core

record Group (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ : Type ℓ where
  field _⁻¹ : A → A
open Group ⦃...⦄ public

module _ (A : Type ℓ) ⦃ _ : Semigroup A ⦄ ⦃ _ : Monoid A ⦄ ⦃ _ : Group A ⦄ where

  record GroupLaws ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ : Type (ℓ ⊔ relℓ) where
    open Alg≈
    field
      inverse : Inverse ε _⁻¹ _◇_
      ⁻¹-cong : Congruent₁ _⁻¹

  GroupLaws≡ : Type ℓ
  GroupLaws≡ = GroupLaws
    where instance _ = mkISetoid≡; _ = mkSetoidLaws≡

open GroupLaws ⦃...⦄ public

-- ** integers
module _ where
  open ℤ
  import Data.Integer as ℤ
  import Data.Integer.Properties as ℤ

  instance _ = mkISetoid≡; _ = mkSetoidLaws≡
           _ = Semigroup-ℤ-+
           _ = Monoid-ℤ-+
  Group-ℤ-+ = Group ℤ ∋ λ where ._⁻¹ → ℤ.-_
  instance _ = Group-ℤ-+
  GroupLaws-ℤ-+ = GroupLaws≡ ℤ ∋ record {inverse = ℤ.+-inverse ; ⁻¹-cong = cong (ℤ.-_)}

-- G-sets
module _ (G : Type ℓ) ⦃ _ : Semigroup G ⦄ ⦃ _ : Monoid G ⦄ ⦃ _ : Group G ⦄ where

  module _ (X : Type ℓ′) ⦃ _ : ISetoid X ⦄ where
    record Actionˡ : Type (ℓ ⊔ ℓ′ ⊔ relℓ) where
      infixr 5 _·_
      field _·_ : G → X → X
            identity : ∀ {x : X} → ε · x ≈ x
            compatibility : ∀ {g h : G} {x : X} → g · h · x ≈ (g ◇ h) · x
    record Actionʳ : Type (ℓ ⊔ ℓ′ ⊔ relℓ) where
      infixl 5 _·_
      field _·_ : X → G → X
            identity : ∀ {x : X} → x · ε ≈ x
            compatibility : ∀ {x : X} {g h : G} → x · g · h ≈ x · (g ◇ h)
    open Actionˡ ⦃...⦄ public renaming
      (identity to ·-identity; compatibility to ·-compatibility)

    record GSet : Typeω where
      field ⦃ action ⦄ : Actionˡ
    open GSet ⦃...⦄ public

  record GSet′ : Typeω where
    field
      {ℓₓ} : Level
      X : Type ℓₓ
      ⦃ setoidX ⦄ : ISetoid X
      action′ : Actionˡ X
  open GSet′ public

  module GSet-Morphisms (X Y : Type ℓ′)
    ⦃ ix : ISetoid X ⦄ ⦃ iy : ISetoid Y ⦄
    ⦃ _ : GSet X ⦄ ⦃ _ : GSet Y ⦄ where
    record _—𝔾→_ : Type (ℓ ⊔ ℓ′ ⊔ relℓ ⦃ iy ⦄) where
      field
        F : X → Y
        equivariant : ∀ {g : G} {x : X} → F (g · x) ≈ g · F x
    open _—𝔾→_ public renaming (F to _𝔾⟨$⟩_)

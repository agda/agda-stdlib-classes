{-# OPTIONS --cubical-compatible #-}
module Class.Decidable.Core where

open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Class.Prelude
open import Class.Core

record _⁇ (P : Type ℓ) : Type ℓ where
  constructor ⁇_
  field dec : Dec P

  auto : ⦃ True dec ⦄ → P
  auto ⦃ pr ⦄ = toWitness pr

  contradict : ∀ {X : Type} {pr : False dec} → P → X
  contradict {pr = pr} = ⊥-elim ∘ toWitnessFalse pr

open _⁇ ⦃...⦄ public

¿_¿ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

¿_¿ᵇ : (P : Type ℓ) → ⦃ P ⁇ ⦄ → Bool
¿ P ¿ᵇ = ⌊ ¿ P ¿ ⌋

_⁇¹ = _⁇ ¹
_⁇² = _⁇ ²
_⁇³ = _⁇ ³

module _ {A : Type ℓ} where

  module _ {P : Pred A ℓ′} where

    dec¹ : ⦃ P ⁇¹ ⦄ → Decidable¹ P
    dec¹ _ = dec

    ⁇¹_ : Decidable¹ P → P ⁇¹
    ⁇¹ p? = ⁇ (p? _)

  ¿_¿¹ : (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
  ¿ _ ¿¹ = dec¹

module _ {A B : Type ℓ} where

  module _ {R : REL A B ℓ′} where

    dec² : ⦃ R ⁇² ⦄ → Decidable² R
    dec² _ _ = dec

    ⁇²_ : Decidable² R → R ⁇²
    ⁇² p? = ⁇ (p? _ _)

  ¿_¿² : (R : REL A B ℓ′) → ⦃ R ⁇² ⦄ → Decidable² R
  ¿ _ ¿² = dec²

module _ {A B C : Type ℓ} where

  module _ {R : 3REL A B C ℓ′} where

    dec³ : ⦃ R ⁇³ ⦄ → Decidable³ R
    dec³ _ _ _ = dec

    ⁇³_ : Decidable³ R → R ⁇³
    ⁇³_ p? = ⁇ (p? _ _ _)

  ¿_¿³ : (R : 3REL A B C ℓ′) → ⦃ R ⁇³ ⦄ → Decidable³ R
  ¿ _ ¿³ = dec³

infix -100 auto∶_
auto∶_ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Type
auto∶_ A = True ¿ A ¿

dec-✓ : ∀ {P : Type ℓ} ⦃ _ : P ⁇ ⦄ (p : P) → ∃[ p′ ] ¿ P ¿ ≡ yes p′
dec-✓ = dec-yes ¿ _ ¿

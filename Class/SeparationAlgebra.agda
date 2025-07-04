{-# OPTIONS --cubical-compatible #-}
module Class.SeparationAlgebra where

open import Function.Definitions using (Injective)
open import Data.Maybe using (Is-just)
open import Relation.Unary renaming (Irrelevant to Irrelevant¹)

open import Class.Prelude
open import Class.Core

open import Class.Setoid.Core
open import Class.Setoid.Instances
open import Class.PartialSemigroup
open import Class.PartialMonoid

-- A separation algebra is a cancellative, partial commutative monoid (Σ, •, ε).
record SeparationAlgebra
  (Σ : Type ℓ) ⦃ _ : ISetoid Σ ⦄ ⦃ _ : SetoidLaws Σ ⦄ : Type (ℓ ⊔ relℓ {A = Σ}) where
  field
    ⦃ ps ⦄ : PartialSemigroup Σ
    ⦃ ps-laws ⦄ : PartialSemigroupLaws Σ
    ⦃ pm ⦄ : PartialMonoid Σ
    ⦃ pm-laws ⦄ : PartialMonoidLaws Σ
    cancellative : ∀ (x : Σ) → Injective _≈_ _≈_ (x ◆_)

  -- ** induced relations

  -- "separateness"
  _#_ : Rel Σ _
  x # y = Is-just (x ◆ y )

  -- "substate"
  _≼_ : Rel Σ _
  x ≼ z = ∃ λ y → (x ◆ y) ≈ just z

  -- ** predicates over Σ
  ℙ : Type _
  ℙ = Pred Σ _

  emp : ℙ
  emp = _≈ ε◆

  _∗_ : ℙ → ℙ → Pred Σ _
  (p ∗ q) σ = ∃ λ (σ₀ : Σ) → ∃ λ (σ₁ : Σ)
    → (σ₀ # σ₁)
    × (σ₀ ∈ p)
    × (σ₁ ∈ q)

  -- ** precise predicates
  Prec : Pred ℙ _
  Prec p = ∀ σ → Irrelevant¹ (λ σₚ → (σₚ ∈ p) × (σₚ ≼ σ))

open SeparationAlgebra ⦃...⦄ public

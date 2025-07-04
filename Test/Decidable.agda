{-# OPTIONS --with-K #-}
module Test.Decidable where

open import Class.Prelude
open import Class.Decidable
open import Class.DecEq
open import Class.DecEq.WithK

module _ {ℓ} {A : Type ℓ} where
  open import Data.Maybe
  _ = Is-just    {A = A} ⁇¹
  _ = Is-nothing {A = A} ⁇¹

import Data.Nat as ℕ
_ = ℕ._≤_ ⁇² ∋ it
_ = ℕ._<_ ⁇² ∋ it

import Data.Integer as ℤ
_ = ℤ._≤_ ⁇² ∋ it
_ = ℤ._<_ ⁇² ∋ it

open import Data.List.Membership.Propositional using (_∈_; _∉_)

0⋯2 = List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []

open import Data.Nat using (_∸_)
open import Class.Anyable

_ = 1 ∈ 0⋯2
  ∋ auto
_ = 3 ∉ 0⋯2
  ∋ auto
f = (3 ∈ 0⋯2 → 2 ≡ 3)
  ∋ contradict

_ = (¬ ¬ ((true , true) ≡ (true , true)))
  × (8 ≡ 18 ∸ 10)
  ∋ auto

_ = ¬ ( (¬ ¬ ((true , true) ≡ (true , true)))
      × (8 ≡ 17 ∸ 10) )
  ∋ auto

_ : ∀ {A : Type ℓ}
  → ⦃ DecEq A ⦄
  → {m : Maybe (List A)} {x₁ x₂ : A}
  → Dec $ Any (λ xs → (xs ≡ (x₁ ∷ x₂ ∷ [])) ⊎ Any (const ⊤) xs) m
_ = dec

module NonDependentRecords where
  record Valid : Type where
    constructor _,_
    field p₁ : ¬ ( (¬ ¬ (true ≡ true))
                 × (8 ≡ 17 ∸ 10) )
          p₂ : (¬ ¬ (true ≡ true))
             × (8 ≡ 18 ∸ 10)
  open Valid

  t : Valid ⁇
  t .dec
    with dec
  ... | no ¬p₁ = no  (¬p₁ ∘ p₁)
  ... | yes p₁
    with dec
  ... | no ¬p₂ = no  (¬p₂ ∘ p₂)
  ... | yes p₂ = yes (p₁ , p₂)

module SimpleDependentRecords where
  record Valid : Type where
    constructor _,_
    field p₁ : ⊤
          p₂ : ¬ ( (¬ ¬ (tt ≡ p₁))
                 × (8 ≡ 17 ∸ 10) )
  open Valid

  t : Valid ⁇
  t .dec
    with dec
  ... | no ¬p₁ = no  (¬p₁ ∘ p₁)
  ... | yes p₁
    with dec
  ... | no ¬p₂ = no  λ where (p₁ , p₂) → ¬p₂ p₂
  ... | yes p₂ = yes (p₁ , p₂)

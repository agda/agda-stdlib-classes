{-# OPTIONS --without-K #-}
module Class.Measurable where

open import Class.Prelude
open Nat using (_+_)

record Measurable {ℓ} (A : Type ℓ) : Type ℓ where
  field ∣_∣ : A → ℕ
open Measurable ⦃...⦄ public

-- ** instances

instance
  Measurable-ℕ : Measurable ℕ
  Measurable-ℕ .∣_∣ x = x

  Measurable-⊎ : ⦃ _ : Measurable A ⦄ ⦃ _ : Measurable B ⦄ → Measurable (A ⊎ B)
  Measurable-⊎ .∣_∣ = λ where
    (inj₁ x) → ∣ x ∣
    (inj₂ x) → ∣ x ∣

-- alternatives for products
Measurable-×ˡ : ⦃ Measurable A ⦄ → Measurable (A × B)
Measurable-×ˡ .∣_∣ (x , _) = ∣ x ∣

Measurable-×ʳ : ⦃ Measurable B ⦄ → Measurable (A × B)
Measurable-×ʳ .∣_∣ (_ , x) = ∣ x ∣

Measurable-×ˡʳ : ⦃ Measurable A ⦄ → ⦃ Measurable B ⦄ → Measurable (A × B)
Measurable-×ˡʳ .∣_∣ (x , y) = ∣ x ∣ + ∣ y ∣

-- alternatives for lists
Measurable-List₀ : Measurable (List A)
Measurable-List₀ .∣_∣ = length

Measurable-List₁ : ⦃ _ : Measurable A ⦄ → Measurable (List A)
Measurable-List₁ {A = A} .∣_∣ = go where go = λ where
  []       → 1
  (x ∷ xs) → ∣ x ∣ + go xs

-- ** well-founded recursion

module _ ⦃ _ : Measurable A ⦄ where

  import Relation.Binary.Construct.On as On
  open import Induction using (Recursor)
  open import Induction.WellFounded using (WellFounded; WfRec; module All)
  open import Data.Nat.Induction using (<-wellFounded)
  open Nat using (_<_)
  open Fun using (_on_)

  _≺_ : Rel A 0ℓ
  _≺_ = _<_ on ∣_∣

  ≺-wf : WellFounded _≺_
  ≺-wf = On.wellFounded ∣_∣ <-wellFounded

  ≺-rec : Recursor (WfRec _≺_)
  ≺-rec = All.wfRec ≺-wf 0ℓ

-- ** working with *heterogeneous* well-founded relations

∃Measurable : Type₁
∃Measurable = ∃ λ (A : Type) → Measurable A × A

toMeasure : ∀ {A : Type} ⦃ _ : Measurable A ⦄ → A → ∃Measurable
toMeasure ⦃ mx ⦄ x = _ , mx , x

instance
  Measurable∃ : Measurable ∃Measurable
  Measurable∃ .∣_∣ (_ , record {∣_∣ = f} , x) = f x

_≺ᵐ_ : ∀ {A B : Type} ⦃ _ : Measurable A ⦄ ⦃ _ : Measurable B ⦄ → A → B → Type
x ≺ᵐ y = toMeasure x ≺ toMeasure y

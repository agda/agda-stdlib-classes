{-# OPTIONS --without-K #-}
module Class.Decidable.WithoutK where

open import Class.Prelude
open import Class.Decidable.Core

infix 0 ifᵈ_then_else_
ifᵈ_then_else_ : ∀ {X : Type ℓ} (P : Type ℓ′)
  → ⦃ P ⁇ ⦄ → ({_ : P} → X) → ({_ : ¬ P} → X) → X
ifᵈ P then t else f with ¿ P ¿
... | yes p = t {p}
... | no ¬p = f {¬p}

instance
  import Data.Sum.Relation.Unary.All as ⊎; open ⊎ using (inj₁; inj₂)

  Dec-⊎All : ⦃ P ⁇¹ ⦄ → ⦃ Q ⁇¹ ⦄ → ⊎.All P Q ⁇¹
  Dec-⊎All {P = P} {Q = Q} {x = inj₁ x} .dec = mapDec inj₁ inj₁˘ ¿ P x ¿
    where inj₁˘ : ∀ {x} → ⊎.All P Q (inj₁ x) → P x
          inj₁˘ (inj₁ x) = x
  Dec-⊎All {P = P} {Q = Q} {x = inj₂ y} .dec = mapDec inj₂ inj₂˘ ¿ Q y ¿
    where inj₂˘ : ∀ {x} → ⊎.All P Q (inj₂ x) → Q x
          inj₂˘ (inj₂ x) = x

{-# OPTIONS --without-K #-}
module Class.ToBool where

open import Class.Prelude hiding (if_then_else_; ⊤; tt)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Class.Decidable.Core

record ToBool′ (A : Type ℓ) (P 𝕋 𝔽 : A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field decide : (a : A) → ⦃ P a ⦄ → 𝕋 a ⊎ 𝔽 a

  infix -10 if_then_else_
  if_then_else_ : (a : A) ⦃ _ : P a ⦄ → ({𝕋 a} → B) → ({𝔽 a} → B) → B
  if a then t else f =
    case decide a of λ where
      (inj₁ 𝕥) → t {𝕥}
      (inj₂ 𝕗) → f {𝕗}

  toBool : (a : A) ⦃ _ : P a ⦄ → Bool
  toBool a = if a then true else false
open ToBool′ ⦃...⦄ public

ToBool : (A : Type ℓ) (𝕋 𝔽 : A → Type ℓ′) → Type (ℓ ⊔ ℓ′)
ToBool {ℓ} A = ToBool′ A (λ _ → ⊤)

instance
  ToBool-Bool : ToBool Bool (_≡ true) (_≡ false)
  ToBool-Bool .decide = λ where
    true  → inj₁ refl
    false → inj₂ refl

  ToBool-Dec : ToBool (Dec B) (const B) (const $ ¬ B)
  ToBool-Dec .decide = λ where
    (yes x) → inj₁ x
    (no ¬x) → inj₂ ¬x

  ToBool-Maybe : ToBool (Maybe B) (const B) (const ⊤)
  ToBool-Maybe .decide = λ where
    (just x) → inj₁ x
    nothing  → inj₂ tt

  ToBool-⁇ : ToBool′ (Type ℓ) _⁇ id ¬_
  ToBool-⁇ .decide _ = decide dec ⦃ _ ⦄

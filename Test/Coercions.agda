{-# OPTIONS --without-K #-}
module Test.Coercions where

open import Class.Prelude
open import Class.Coercions

𝟚 = ⊤ ⊎ ⊤
pattern 𝕃 = inj₁ tt; pattern ℝ = inj₂ tt

instance
  ↝Bool : 𝟚 ↝ Bool
  ↝Bool .to = λ where
    𝕃 → true
    ℝ → false

  Bool↝ : Bool ↝ 𝟚
  Bool↝ .to = λ where
    true  → 𝕃
    false → ℝ

_ : Bool
_ = to 𝕃

_ : 𝟚
_ = to true

_ : Bool → Bool
_ = not ∘ to[ Bool ] ∘ to[ 𝟚 ]

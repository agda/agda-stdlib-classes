{-# OPTIONS --cubical-compatible #-}
module Class.Setoid.Instances where

open import Class.Prelude
open import Class.Setoid.Core

instance
  Setoid-Maybe : ⦃ ISetoid A ⦄ → ISetoid (Maybe A)
  Setoid-Maybe .relℓ = _
  Setoid-Maybe ._≈_ = λ where
    nothing nothing → Lift _ ⊤
    nothing (just _) → Lift _ ⊥
    (just _) nothing → Lift _ ⊥
    (just x) (just y) → x ≈ y

  SetoidLaws-Maybe : ⦃ _ : ISetoid A ⦄ → ⦃ SetoidLaws A ⦄ → SetoidLaws (Maybe A)
  SetoidLaws-Maybe .isEquivalence = record
    { refl  = λ where
      {just x}  → ≈-refl {x = x}
      {nothing} → lift tt
    ; sym   = λ where
      {just x}  {just y}  → ≈-sym {x = x}{y}
      {just _}  {nothing} → id
      {nothing} {just _}  → id
      {nothing} {nothing} → id
    ; trans = λ where
      {just x}  {just y}  {just z}  p q → ≈-trans {i = x}{y}{z} p q
      {nothing} {nothing} {nothing} p _ → p
    }

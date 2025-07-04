{-# OPTIONS --without-K #-}
module Test.HasMembership where

open import Class.Prelude
open import Class.HasMembership
open import Class.ToN

_ = mapWith∈ (List ℕ ∋ 10 ∷ 20 ∷ 30 ∷ []) toℕ
  ≡ (0 ∷ 1 ∷ 2 ∷ [])
  ∋ refl
_ = mapWith∈ (List⁺ ℕ ∋ 10 ∷ 20 ∷ 30 ∷ []) toℕ
  ≡ (0 ∷ 1 ∷ 2 ∷ [])
  ∋ refl
_ = mapWith∈ (Vec ℕ 3 ∋ 10 ∷ 20 ∷ 30 ∷ []) toℕ
  ≡ (0 ∷ 1 ∷ 2 ∷ [])
  ∋ refl
_ = mapWith∈ (Maybe ℕ ∋ just 10) (const 1)
  ≡ just 1
  ∋ refl

open import Class.DecEq
open import Class.Decidable

_ = 20 ∈ (List ℕ ∋ 10 ∷ 20 ∷ 30 ∷ [])
  ∋ auto
_ = 20 ∈ (List⁺ ℕ ∋ 10 ∷ 20 ∷ 30 ∷ [])
  ∋ auto
_ = 20 ∈ (Vec ℕ 3 ∋ 10 ∷ 20 ∷ 30 ∷ [])
  ∋ auto
_ = 10 ∈ just 10
  ∋ auto

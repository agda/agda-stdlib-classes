{-# OPTIONS --cubical-compatible #-}
module Test.HasMembership where

open import Class.Prelude
open import Class.HasMembership
open import Class.ToN

_ = mapWith∈ (List ℕ ∋ 10 ∷ 20 ∷ 30 ∷ []) toℕ
  ≡ (0 ∷ 1 ∷ 2 ∷ [])
  ∋ refl
_ = mapWith∈ (Vec ℕ 3 ∋ 10 ∷ 20 ∷ 30 ∷ []) toℕ
  ≡ (0 ∷ 1 ∷ 2 ∷ [])
  ∋ refl

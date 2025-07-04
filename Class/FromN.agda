{-# OPTIONS --cubical-compatible #-}
module Class.FromN where

open import Class.Prelude

record Fromℕ (A : Type ℓ) : Type ℓ where
  field fromℕ : ℕ → A
open Fromℕ ⦃...⦄ public

instance
  Fromℕ-ℕ    = Fromℕ ℕ ∋ λ where .fromℕ → id
  Fromℕ-Int  = Fromℕ ℤ ∋ λ where .fromℕ → Int.+_
  Fromℕ-ℕᵇ   = Fromℕ ℕᵇ ∋ λ where .fromℕ → Bin.fromℕ
  Fromℕ-Char = Fromℕ Char ∋ λ where .fromℕ → Ch.fromℕ
  Fromℕ-Word = Fromℕ Word64 ∋ λ where .fromℕ → Word.fromℕ
  Fromℕ-Fin  = Fromℕ (∃ Fin) ∋ λ where .fromℕ → -,_ ∘ Fi.fromℕ

{-# OPTIONS --without-K #-}
module Test.Measurable where

open import Class.Prelude
open Nat
open import Class.Measurable

instance _ = Measurable-List₁

-- ** make sure we can differentiate between ∣ [] ∣ and ∣ [ [] ] ∣

∣xs∣>0 : ∀ ⦃ _ : Measurable A ⦄ (xs : List A) →
  ∣ xs ∣ > 0
∣xs∣>0 [] = s≤s z≤n
∣xs∣>0 (x ∷ xs) with ∣ x ∣
... | 0     = ∣xs∣>0 xs
... | suc _ = s≤s z≤n

≺ᵐ-∷ : ⦃ _ : Measurable A ⦄ (x : A) (xs : List A) →
  x ≺ᵐ (x ∷ xs)
≺ᵐ-∷ x xs = Nat.m<m+n ∣ x ∣ (∣xs∣>0 xs)

-- ** example well-founded recursion on naturals
--
-- NB: termination fails if the recursive argument is not structurally smaller, e.g.
--
-- binSearch : ℕ → ℕ
-- binSearch 0 = 0
-- binSearch n = f ⌊ n /2⌋

binSearch : ℕ → ℕ
binSearch = ≺-rec _ λ where
  zero    _ → 0
  (suc n) r → r (s≤s $ /2-less n)
 where
  /2-less : ∀ n → ⌊ n /2⌋ ≤ n
  /2-less = λ where
    zero          → z≤n
    (suc zero)    → z≤n
    (suc (suc n)) → s≤s $ ≤-trans (/2-less n) (n≤1+n _)

{-# OPTIONS --without-K #-}
module Test.Monoid where

open import Class.Prelude
open import Class.Semigroup
open import Class.Monoid

_ = ε ◇ 1 ◇ 2 ≡ 3
  ∋ refl
  where instance _ = Semigroup-ℕ-+; _ = Monoid-ℕ-+
_ = ε ◇ 1 ◇ 2 ≡ 2
  ∋ refl
  where instance _ = Semigroup-ℕ-*; instance _ = Monoid-ℕ-*
_ = ε ◇ 1ℤ ◇ 1ℤ ≡ + 2
  ∋ refl
  where instance _ = Semigroup-ℤ-+; instance _ = Monoid-ℤ-+
        open import Data.Integer using (+_)
_ = ε ◇ 1ℤ ◇ 1ℤ ≡ 1ℤ
  ∋ refl
  where instance _ = Semigroup-ℤ-*; instance _ = Monoid-ℤ-*

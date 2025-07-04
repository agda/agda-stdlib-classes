{-# OPTIONS --cubical-compatible #-}
module Test.Monad where

open import Class.Prelude
open import Class.Core
open import Class.Monad
-- open import Class.Monad.Id -- breaks instance resolution

_ = (return 5 >>= just) ≡ just 5
  ∋ refl
_ = (return 5 >>= just) ≡ just 5
  ∋ >>=-identityʳ _

_ : Monad Maybe
_ = itω

_ : MonadLaws Maybe
_ = itω

_ : ⦃ _ : Monad M ⦄ → (ℕ → M ℕ)
_ = return

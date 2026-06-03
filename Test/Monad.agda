{-# OPTIONS --cubical-compatible #-}
module Test.Monad where

open import Class.Prelude
open import Class.Core
open import Class.Monad

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

-- ** maybe monad

pred? : ℕ → Maybe ℕ
pred? = λ where
  0 → nothing
  (suc n) → just n

getPred : ℕ → Maybe ℕ
getPred = λ n → do
  x ← pred? n
  return x

_ = getPred 3 ≡ just 2
  ∋ refl

-- ** cross-level bind

_ : TC Set
_ = getType (quote Nat.zero) >>= unquoteTC
  where open import Reflection using (getType; unquoteTC)

-- ** reader monad

ReaderT : ∀ (M : Type↑ ℓ↑) → Type ℓ → Type ℓ′ → _
ReaderT M A B = A → M B

module _ ⦃ _ : Monad M ⦄ {A : Type ℓ} where
  module Monad-ReaderT = MkMonad {M = ReaderT M A}
    (λ x _ → return x)
    (λ m k a → m a >>= λ b → k b a)

Reader : Type ℓ → Type ℓ′ → Type _
Reader = ReaderT id

ask : Reader A A
ask a = a

local : (A → B) → Reader B C → Reader A C
local f r = r ∘ f

runReader : A → Reader A B → B
runReader = flip _$_

getLength : List (Maybe ℕ) → ℕ
getLength ys = runReader ys $ local (just 0 ∷_) $ do
  xs ← ask
  return (length xs)
  where open import Class.Monad.Id

_ = getLength (just 1 ∷ nothing ∷ just 2 ∷ []) ≡ 4
  ∋ refl

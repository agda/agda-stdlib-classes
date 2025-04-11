{-# OPTIONS --cubical-compatible #-}
module Test.Monad where

open import Data.List using (length)

open import Class.Core
open import Class.Prelude
open import Class.Functor
open import Class.Monad

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

-- ** reader monad

ReaderT : ∀ (M : Type↑ ℓ↑) → Type ℓ → Type ℓ′ → _
ReaderT M A B = A → M B

instance
  Monad-ReaderT : ⦃ _ : Monad M ⦄ → Monad (ReaderT M A)
  Monad-ReaderT = λ where
    .return → λ x _ → return x
    ._>>=_ m k → λ a → m a >>= λ b → k b a

Reader : Type ℓ → Type ℓ′ → Type _
Reader = ReaderT id

instance
  Monad-Id : Monad id
  Monad-Id = λ where
    .return → id
    ._>>=_ m k → k m
  {-# INCOHERENT Monad-Id #-}

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

_ = getLength (just 1 ∷ nothing ∷ just 2 ∷ []) ≡ 4
  ∋ refl

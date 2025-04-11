{-# OPTIONS --cubical-compatible #-}
module Class.Traversable.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor.Core
open import Class.Monad

record Traversable (F : Type↑ ℓ↑) ⦃ _ : Functor F ⦄ : Typeω where
  field sequence : ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverse : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverse f = sequence ∘ fmap f
open Traversable ⦃...⦄ public

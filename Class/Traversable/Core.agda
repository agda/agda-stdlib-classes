{-# OPTIONS --cubical-compatible #-}
module Class.Traversable.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor.Core
open import Class.Monad

record Traversable {a} (F : Type a → Type a) ⦃ _ : Functor F ⦄ : Type (lsuc a) where
  field sequence : {M : Type a → Type a} → ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverse : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverse f = sequence ∘ fmap f
open Traversable ⦃...⦄ public

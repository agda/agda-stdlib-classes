{-# OPTIONS --cubical-compatible #-}
module Class.Traversable.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor.Core
open import Class.Applicative.Core
open import Class.Monad.Core

record TraversableA (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field sequenceA : ⦃ Applicative M ⦄ → F (M A) → M (F A)

  traverseA : ⦃ Applicative M ⦄ → (A → M B) → F A → M (F B)
  traverseA f = sequenceA ∘ fmap f
open TraversableA ⦃...⦄ public

record Traversable (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field sequence : ⦃ Monad M ⦄ → F (M A) → M (F A)

  traverse : ⦃ Monad M ⦄ → (A → M B) → F A → M (F B)
  traverse f = sequence ∘ fmap f
open Traversable ⦃...⦄ public

{-# OPTIONS --cubical-compatible #-}
module Class.Foldable.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor
open import Class.Semigroup
open import Class.Monoid

record Foldable (F : Type↑ ℓ↑) ⦃ _ : Functor F ⦄ : Typeω where
  field fold : ⦃ _ : Semigroup A ⦄ → ⦃ Monoid A ⦄ → F A → A
open Foldable ⦃...⦄ public

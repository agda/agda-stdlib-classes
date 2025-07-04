{-# OPTIONS --cubical-compatible #-}
module Class.Foldable.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor
open import Class.Semigroup
open import Class.Monoid

record Foldable (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field fold : ⦃ _ : Semigroup A ⦄ → ⦃ Monoid A ⦄ → F A → A

  foldMap : ⦃ _ : Semigroup B ⦄ → ⦃ Monoid B ⦄ → (A → B) → F A → B
  foldMap f = fold ∘ fmap f

open Foldable ⦃...⦄ public

record Foldable′ (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field foldMap′ : ⦃ _ : Semigroup B ⦄ → ⦃ Monoid B ⦄ → (A → B) → F A → B

  fold′ : ⦃ _ : Semigroup A ⦄ → ⦃ Monoid A ⦄ → F A → A
  fold′ = foldMap′ id

open Foldable′ ⦃...⦄ public

Foldable′⇒Foldable : ⦃ _ : Functor F ⦄ → Foldable′ F → Foldable F
Foldable′⇒Foldable f = let instance _ = f in
  λ where .fold → fold′

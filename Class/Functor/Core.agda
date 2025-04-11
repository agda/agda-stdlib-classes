{-# OPTIONS --cubical-compatible #-}
module Class.Functor.Core where

open import Class.Prelude
open import Class.Core

private variable a b c : Level

record Functor (F : Type↑ ℓ↑) : Typeω where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field _<$>_ : (A → B) → F A → F B
  fmap = _<$>_

  _<$_ : A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : F A → (A → B) → F B
  _<&>_ = flip _<$>_
open Functor ⦃...⦄ public

record FunctorLaws (F : Type↑ ℓ↑) ⦃ _ : Functor F ⦄ : Typeω where
  field
    -- preserves identity morphisms
    fmap-id : ∀ {A : Type a} (x : F A) →
      fmap id x ≡ x
    -- preserves composition of morphisms
    fmap-∘  : ∀ {A : Type a} {B : Type b} {C : Type c}
                {f : B → C} {g : A → B} (x : F A) →
      fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
open FunctorLaws ⦃...⦄ public

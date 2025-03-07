{-# OPTIONS --cubical-compatible #-}
module Class.Functor.Core where

open import Class.Prelude
open import Class.Core

private variable a b c : Level

record Functor (F : Type a → Type b) : Type (lsuc (a ⊔ b)) where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field _<$>_ : (A → B) → F A → F B
  fmap = _<$>_

  _<$_ : A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : F A → (A → B) → F B
  _<&>_ = flip _<$>_
open Functor ⦃...⦄ public

record FunctorLaws (F : Type a → Type b) ⦃ _ : Functor F ⦄ : Type (lsuc (a ⊔ b)) where
  field
    -- preserves identity morphisms
    fmap-id : ∀ {A : Type a} (x : F A) →
      fmap id x ≡ x
    -- preserves composition of morphisms
    fmap-∘  : ∀ {A B C : Type a}
                {f : B → C} {g : A → B} (x : F A) →
      fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
open FunctorLaws ⦃...⦄ public

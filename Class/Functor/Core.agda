{-# OPTIONS --cubical-compatible #-}
module Class.Functor.Core where

open import Class.Prelude
open import Class.Core

private variable a b c : Level

record Functor (F : Type↑ ℓ↑ ℓ↑′) : Typeω where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field _<$>_ : (A → B) → F A → F B
  fmap = _<$>_

  _<$_ : A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : F A → (A → B) → F B
  _<&>_ = flip _<$>_
open Functor ⦃...⦄ public

record FunctorLaws (F : Type↑ ℓ↑ ℓ↑′) ⦃ _ : Functor (λ {ℓ} → F {ℓ}) ⦄ : Typeω where
  field
    -- preserves identity morphisms
    fmap-id : ∀ {A : Type (ℓ↑ a)} (x : F {a} A) →
      fmap id x ≡ x
    -- preserves composition of morphisms
    fmap-∘  : ∀ {A : Type (ℓ↑ a)} {B : Type (ℓ↑ b)} {C : Type (ℓ↑ c)}
                {f : B → C} {g : A → B} (x : F {a} A) →
      fmap (f ∘ g) x ≡ (fmap {F = F} {b}{A = B} {c}{B = C} f ∘ fmap  g) x
open FunctorLaws ⦃...⦄ public

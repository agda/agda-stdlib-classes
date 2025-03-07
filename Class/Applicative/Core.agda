{-# OPTIONS --cubical-compatible #-}
module Class.Applicative.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor.Core

record Applicative {a b} (F : Type a → Type b) : Type (lsuc (a ⊔ b)) where
  infixl 4 _<*>_ _⊛_ _<*_ _<⊛_ _*>_ _⊛>_
  infix  4 _⊗_

  field
    overlap ⦃ super ⦄ : Functor F
    pure : A → F A
    _<*>_  : F (A → B) → F A → F B
  _⊛_ = _<*>_

  _<*_ : F A → F B → F A
  x <* y = const <$> x ⊛ y

  _*>_ : F A → F B → F B
  x *> y = constᵣ <$> x ⊛ y

  _<⊛_ = _<*_; _⊛>_ = _*>_

  _⊗_ : F A → F B → F (A × B)
  x ⊗ y = (_,_) <$> x ⊛ y

  zipWithA : (A → B → C) → F A → F B → F C
  zipWithA f x y = f <$> x ⊛ y

  zipA : F A → F B → F (A × B)
  zipA = zipWithA _,_

open Applicative ⦃...⦄ public

record Applicative₀ {a b} (F : Type a → Type b) : Type (lsuc (a ⊔ b)) where
  field
    overlap ⦃ super ⦄ : Applicative F
    ε₀ : F A
open Applicative₀ ⦃...⦄ public

record Alternative {a b} (F : Type a → Type b) : Type (lsuc (a ⊔ b)) where
  infixr 3 _<|>_
  field _<|>_ : F A → F A → F A
open Alternative ⦃...⦄ public

infix -1 ⋃⁺_ ⋃_

⋃⁺_ : ⦃ Alternative F ⦄ → List⁺ (F A) → F A
⋃⁺_ = foldr₁ _<|>_

⋃_ : ⦃ Applicative₀ F ⦄ → ⦃ Alternative F ⦄ → List (F A) → F A
⋃_ = foldr _<|>_ ε₀

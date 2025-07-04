{-# OPTIONS --with-K #-}
module Test.View where

open import Class.Prelude
open import Class.View

data SnocList (A : Type ℓ) : Type ℓ where
  [] : SnocList A
  _∷_ : SnocList A → A → SnocList A

_∷ˡ_ : A → SnocList A → SnocList A
x ∷ˡ [] = [] ∷ x
x ∷ˡ (xs ∷ y) = (x ∷ˡ xs) ∷ y

snocView : List A → SnocList A
snocView = λ where
  [] → []
  (x ∷ xs) → x ∷ˡ snocView xs

snocUnview : SnocList A → List A
snocUnview = λ where
  [] → []
  (xs ∷ x) → snocUnview xs L.∷ʳ x

snocUnview-∷ˡ : ∀ (x : A) xs → snocUnview (x ∷ˡ xs) ≡ x ∷ snocUnview xs
snocUnview-∷ˡ _ [] = refl
snocUnview-∷ˡ x (xs ∷ _) rewrite snocUnview-∷ˡ x xs = refl

snocView-∷ʳ : ∀ (x : A) xs → snocView (xs L.∷ʳ x) ≡ snocView xs ∷ x
snocView-∷ʳ _ [] = refl
snocView-∷ʳ x (_ ∷ xs) rewrite snocView-∷ʳ x xs = refl

instance
  SnocView : List A ▷ SnocList A
  SnocView .view = snocView
  SnocView .unview = snocUnview
  SnocView .unview∘view [] = refl
  SnocView .unview∘view (x ∷ xs)
    rewrite snocUnview-∷ˡ x (view xs)
          | unview∘view xs
          = refl
  SnocView .view∘unview [] = refl
  SnocView .view∘unview (xs ∷ x)
    rewrite snocView-∷ʳ x (unview xs)
          | view∘unview xs
          = refl

last : List A → Maybe A
last xs with view xs as SnocList _
... | []    = nothing
... | _ ∷ x = just x

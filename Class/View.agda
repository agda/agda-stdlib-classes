{-# OPTIONS --cubical-compatible #-}
module Class.View where

open import Class.Prelude

record _▷_ (A : Type ℓ) (B : Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field
    view   : A → B
    unview : B → A
    unview∘view : ∀ x → unview (view x) ≡ x
    view∘unview : ∀ y → view (unview y) ≡ y

open _▷_ ⦃...⦄ public

view_as_ : A → (B : Type ℓ′) ⦃ _ : A ▷ B ⦄ → B
view x as B = view {B = B} x

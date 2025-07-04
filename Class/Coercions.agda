{-# OPTIONS --cubical-compatible #-}
module Class.Coercions where

open import Class.Prelude

infix -1 _↝_
record _↝_ (A : Type ℓ) (B : Type ℓ′) : Typeω where
  field to : A → B
  syntax to {B = B} = to[ B ]
open _↝_ ⦃...⦄ public

tos : ⦃ A ↝ B ⦄ → List A ↝ List B
tos .to = map to

infix -1 _⁇_↝_
record _⁇_↝_ (A : Type ℓ) (P : Pred A ℓ′) (B : Type ℓ′) : Typeω where
  field toBecause : (x : A) .{_ : P x} → B
  syntax toBecause x {p} = ⌞ x ⊣ p ⌟
open _⁇_↝_ ⦃...⦄ public

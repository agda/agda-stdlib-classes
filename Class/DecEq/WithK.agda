{-# OPTIONS --with-K #-}
open import Class.Prelude
open import Class.DecEq.Core

module Class.DecEq.WithK ⦃ _ : DecEq A ⦄ where

≟-refl : ∀ (x : A) → (x ≟ x) ≡ yes refl
≟-refl x with refl , p ← dec-yes (x ≟ x) refl = p

==-refl : ∀ (x : A) → T (x == x)
==-refl _ = subst (T ∘ does) (sym $ ≟-refl _) tt

≡ᵇ-refl = ==-refl

instance
  DecEq-Σ : ∀ {B : A → Type ℓ′} ⦃ _ : ∀ {x} → DecEq (B x) ⦄ → DecEq (Σ A B)
  DecEq-Σ ._≟_ (x , y) (x′ , y′)
    with x ≟ x′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl
    with y ≟ y′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl = yes refl

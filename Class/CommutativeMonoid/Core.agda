{-# OPTIONS --without-K #-}
module Class.CommutativeMonoid.Core where

open import Class.Prelude
open import Class.Semigroup
open import Class.Monoid

import Algebra as Alg

record CommutativeMonoid c ℓ Carrier : Type (lsuc (c ⊔ ℓ)) where
  infix  4 _≈_
  field
    _≈_                 : Carrier → Carrier → Type ℓ
    ⦃ semigroup ⦄       : Semigroup Carrier
    ⦃ monoid ⦄          : Monoid Carrier
    isCommutativeMonoid : Alg.IsCommutativeMonoid {c} _≈_ _◇_ ε

module Conversion {c ℓ} where
  toBundle : ∀ {Carrier} → CommutativeMonoid c ℓ Carrier → Alg.CommutativeMonoid c ℓ
  toBundle c = record { CommutativeMonoid c }

  fromBundle : (m : Alg.CommutativeMonoid c ℓ)
             → CommutativeMonoid c ℓ (Alg.CommutativeMonoid.Carrier m)
  fromBundle c = record
    { Alg.CommutativeMonoid c using (_≈_; isCommutativeMonoid)
    ; semigroup = λ where ._◇_ → Alg.CommutativeMonoid._∙_ c
    ; monoid    = λ where .ε   → Alg.CommutativeMonoid.ε c }

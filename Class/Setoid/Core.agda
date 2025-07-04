{-# OPTIONS --cubical-compatible #-}
module Class.Setoid.Core where

open import Class.Core
open import Class.Prelude

record ISetoid (A : Type ℓ) : Typeω where
  infix 4 _≈_ _≉_
  field
    {relℓ} : Level
    _≈_ : Rel A relℓ

  _≉_ : Rel A relℓ
  x ≉ y = ¬ (x ≈ y)

  module Alg≈ = Alg _≈_
open ISetoid ⦃...⦄ public

record SetoidLaws (A : Type ℓ) ⦃ _ : ISetoid A ⦄ : Typeω where
  field isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public
    renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans; reflexive to ≈-reflexive)

  mkSetoid : Setoid ℓ relℓ
  mkSetoid = record {Carrier = A; _≈_ = _≈_; isEquivalence = isEquivalence}

  import Relation.Binary.Reasoning.Setoid as BinSetoid
  module ≈-Reasoning = BinSetoid mkSetoid
open SetoidLaws ⦃...⦄ public

_⟶_ : (A : Type ℓ) (B : Type ℓ′)
    → ⦃ _ : ISetoid A ⦄ → ⦃ SetoidLaws A ⦄
    → ⦃ _ : ISetoid B ⦄ → ⦃ SetoidLaws B ⦄
    → Type _
A ⟶ B = Func (mkSetoid {A = A}) (mkSetoid {A = B})
  where open import Function.Bundles

mkISetoid≡ : ISetoid A
mkISetoid≡ = λ where
  .relℓ → _
  ._≈_ → _≡_

mkSetoidLaws≡ : SetoidLaws A ⦃ mkISetoid≡ ⦄
mkSetoidLaws≡ .isEquivalence = PropEq.isEquivalence
  where import Relation.Binary.PropositionalEquality as PropEq

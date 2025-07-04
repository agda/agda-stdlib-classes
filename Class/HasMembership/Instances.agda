{-# OPTIONS --cubical-compatible #-}
module Class.HasMembership.Instances where

open import Class.Prelude
open import Class.HasMembership.Core

open import Class.DecEq.Core

open import Class.Decidable.Core
-- open import Class.Decidable.Instances

instance

  M-List : HasMembership {ℓ} List
  M-List = record {LMem}
    where import Data.List.Membership.Propositional as LMem

  Dec∈-List : ⦃ _ : DecEq A ⦄ → _∈_ {F = List}{A} ⁇²
  Dec∈-List = ⁇² DL._∈?_
    where import Data.List.Membership.DecPropositional _≟_ as DL

  M-Vec : HasMembership {ℓ} (flip Vec n)
  M-Vec ._∈_ = λ x → VMem._∈_ x
    where import Data.Vec.Membership.Propositional as VMem

  Dec∈-Vec : ⦃ _ : DecEq A ⦄ → _∈_ {F = flip Vec n}{A} ⁇²
  Dec∈-Vec = ⁇² λ x → DV._∈?_ x
    where import Data.Vec.Membership.DecPropositional _≟_ as DV

  M-List⁺ : HasMembership {ℓ} List⁺
  M-List⁺ ._∈_ x xs = x ∈  L⁺.toList xs

  Dec∈-List⁺ : ⦃ _ : DecEq A ⦄ → _∈_ {F = List⁺}{A} ⁇²
  Dec∈-List⁺ .dec = _ ∈? L⁺.toList _

  import Data.Maybe.Relation.Unary.Any as Mb

  M-Maybe : HasMembership {ℓ} Maybe
  M-Maybe ._∈_ x mx = Mb.Any (_≡ x) mx

  Dec∈-Maybe : ⦃ _ : DecEq A ⦄ → _∈_ {F = Maybe}{A} ⁇²
  Dec∈-Maybe .dec = Mb.dec (_≟ _) _

module _ {A B : Type} (f : A → B) where

  import Data.List.Membership.Propositional.Properties as LMem

  ∈⁺-map⁺ : ∀ {x xs} → x ∈ xs → f x ∈ L⁺.map f xs
  ∈⁺-map⁺ = LMem.∈-map⁺ f

  ∈⁺-map⁻ : ∀ {y xs} → y ∈ L⁺.map f xs → ∃ λ x → x ∈ xs × y ≡ f x
  ∈⁺-map⁻ = LMem.∈-map⁻ f

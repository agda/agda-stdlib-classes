{-# OPTIONS --cubical-compatible #-}
module Class.HasMembership.Instances where

open import Class.Prelude
open import Class.HasMembership.Core

instance
  M-List : HasMembership {ℓ} List
  M-List = record {LMem}
    where import Data.List.Membership.Propositional as LMem

  M-List⁺ : HasMembership {ℓ} List⁺
  M-List⁺ ._∈_ x xs = x ∈  L⁺.toList xs

  M-Vec : HasMembership {ℓ} (flip Vec n)
  M-Vec ._∈_ = λ x → VMem._∈_ x
    where import Data.Vec.Membership.Propositional as VMem

  M-Maybe : HasMembership {ℓ} Maybe
  M-Maybe ._∈_ x mx = Mb.Any (_≡ x) mx
    where import Data.Maybe.Relation.Unary.Any as Mb

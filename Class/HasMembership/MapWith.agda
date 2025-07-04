{-# OPTIONS --cubical-compatible #-}
module Class.HasMembership.MapWith where

open import Class.Prelude
open import Class.HasMembership.Core
open import Class.HasMembership.Instances

record Functor∈ (F : Type ℓ → Type ℓ) ⦃ _ : HasMembership F ⦄ : Type (lsuc ℓ) where
  field mapWith∈ : ∀ {A B : Type ℓ} → (xs : F A) → (∀ {x : A} → x ∈ xs → B) → F B
open Functor∈ ⦃...⦄ public

instance
  F∈-List : Functor∈ {ℓ} List
  F∈-List = record {LMem}
    where import Data.List.Membership.Propositional as LMem

  F∈-List⁺ : Functor∈ {ℓ} List⁺
  F∈-List⁺ .mapWith∈ (_ ∷ xs) f = f (here refl) ∷ mapWith∈ xs (f ∘ there)
    where open import Data.List.Relation.Unary.Any using (here; there)

  F∈-Vec : Functor∈ {ℓ} (flip Vec n)
  F∈-Vec = record {VMem}
    where import Data.Vec.Membership.Propositional as VMem

  F∈-Maybe : Functor∈ {ℓ} Maybe
  F∈-Maybe .mapWith∈ = λ where
    (just _) f → just $ f (Mb.just refl)
    nothing  f → nothing
   where import Data.Maybe.Relation.Unary.Any as Mb

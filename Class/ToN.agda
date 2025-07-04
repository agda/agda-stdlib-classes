{-# OPTIONS --cubical-compatible #-}
module Class.ToN where

open import Class.Prelude

record Toℕ (A : Type ℓ) : Type ℓ where
  field toℕ : A → ℕ
open Toℕ ⦃...⦄ public

open import Reflection.AST.Meta as Meta using (Meta)

instance
  Toℕ-ℕ    = Toℕ ℕ      ∋ λ where .toℕ → id
  Toℕ-Char = Toℕ Char   ∋ λ where .toℕ → Ch.toℕ
  Toℕ-Word = Toℕ Word64 ∋ λ where .toℕ → Word.toℕ
  Toℕ-Meta = Toℕ Meta   ∋ λ where .toℕ → Meta.toℕ

  Toℕ-Fin : ∀ {n} → Toℕ (Fin n)
  Toℕ-Fin .toℕ = Fi.toℕ

  import Data.List.Membership.Propositional as LMem
  import Data.List.Relation.Unary.Any as LAny

  Toℕ-List∈ : ∀ {x}{xs : List A} → Toℕ (x LMem.∈ xs)
  Toℕ-List∈ .toℕ = toℕ ∘ LAny.index

  import Data.Vec.Membership.Propositional as VMem
  import Data.Vec.Relation.Unary.Any as VAny

  Toℕ-Vec∈ : ∀ {x}{xs : Vec A n} → Toℕ (x VMem.∈ xs)
  Toℕ-Vec∈ .toℕ = toℕ ∘ VAny.index

{-# OPTIONS --cubical-compatible #-}
module Class.Traversable.Instances where

open import Class.Prelude
open import Class.Functor
open import Class.Applicative
open import Class.Monad
open import Class.Traversable.Core

instance
  TraversableA-Maybe : TraversableA Maybe
  TraversableA-Maybe .sequenceA = λ where
    nothing  → ⦇ nothing ⦈
    (just x) → ⦇ just x  ⦈

  TraversableM-Maybe : Traversable Maybe
  TraversableM-Maybe .sequence = sequenceA

  TraversableA-List : TraversableA List
  TraversableA-List .sequenceA = go where go = λ where
    []       → ⦇ [] ⦈
    (m ∷ ms) → ⦇ m ∷ go ms ⦈

  TraversableM-List : Traversable List
  TraversableM-List .sequence = sequenceA

  TraversableA-List⁺ : TraversableA List⁺
  TraversableA-List⁺ .sequenceA (m ∷ ms) = ⦇ m ∷ sequenceA ms ⦈

  TraversableM-List⁺ : Traversable List⁺
  TraversableM-List⁺ .sequence = sequenceA

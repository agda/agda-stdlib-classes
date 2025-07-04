{-# OPTIONS --cubical-compatible #-}
module Class.Foldable.Instances where

open import Class.Prelude
open import Class.Functor
open import Class.Semigroup
open import Class.Monoid
open import Class.Foldable.Core

instance
  Foldable-List : Foldable List
  Foldable-List .fold = foldr _◇_ ε

  Foldable-Maybe : Foldable Maybe
  Foldable-Maybe .fold = fromMaybe ε

  Foldable-List⁺ : Foldable List⁺
  Foldable-List⁺ .fold (x ∷ xs) = x ◇ fold xs

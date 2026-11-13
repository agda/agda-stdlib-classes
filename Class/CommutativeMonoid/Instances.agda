{-# OPTIONS --without-K #-}

module Class.CommutativeMonoid.Instances where

open import Class.CommutativeMonoid.Core

open import Data.Nat.Properties

module NonUniqueInstances where
  CommMonoid-ℕ-+ = Conversion.fromBundle +-0-commutativeMonoid
  CommMonoid-ℕ-* = Conversion.fromBundle *-1-commutativeMonoid

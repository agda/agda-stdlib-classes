{-# OPTIONS --with-K #-}
module Classes where

-- ** Algebraic structures
open import Class.Semigroup public
open import Class.Monoid public
open import Class.Functor public
open import Class.Bifunctor public
open import Class.Applicative public
open import Class.Monad public
open import Class.Foldable public
open import Class.Traversable public

-- ** Decidability
open import Class.DecEq public
open import Class.DecEq.WithK public
open import Class.Decidable public

-- ** Others
open import Class.Show public
open import Class.Default public
open import Class.ToBool public

-- ** Tests
open import Test.Monoid
open import Test.Functor
open import Test.DecEq
open import Test.Decidable
open import Test.Show

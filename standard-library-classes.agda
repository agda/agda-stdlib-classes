{-# OPTIONS --with-K #-}
module standard-library-classes where

-- ** Algebraic structures
open import Class.Semigroup public
open import Class.Monoid public
open import Class.CommutativeMonoid public
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
open import Class.Allable public
open import Class.Anyable public
open import Class.Default public
open import Class.HasAdd public
open import Class.HasOrder public
open import Class.Show public
open import Class.ToBool public
open import Class.MonotonePredicate public

-- ** Tests
open import Test.Monoid
open import Test.Functor
open import Test.Monad
open import Test.DecEq
open import Test.Decidable
open import Test.Show
open import Test.Reflection

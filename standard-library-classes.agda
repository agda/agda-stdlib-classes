{-# OPTIONS --with-K #-}
module standard-library-classes where

open import Class.Prelude
open import Class.Newtype; import Test.Newtype

-- ** Algebraic structures
open import Class.Setoid public
open import Class.Semigroup public
open import Class.Monoid public; import Test.Monoid
open import Class.CommutativeMonoid public
open import Class.Functor public; import Test.Functor
open import Class.Bifunctor public
open import Class.Applicative public
open import Class.Monad public; import Class.Monad.Id; import Test.Monad
open import Class.Foldable public
open import Class.Traversable public
open import Class.Pointed public
open import Class.Group public
open import Class.PartialSemigroup public
open import Class.PartialMonoid public
open import Class.SeparationAlgebra public

-- ** Decidability
open import Class.DecEq public; import Test.DecEq
open import Class.DecEq.WithK public
open import Class.Decidable public; import Test.Decidable

-- ** Conversions
open import Class.ToBool public
open import Class.ToList public
open import Class.FromList public
open import Class.ToN public
open import Class.FromN public
open import Class.ToZ public
open import Class.Coercions public; import Test.Coercions

-- ** Overloading notation
open import Class.Allable public; import Test.Allable
open import Class.Anyable public; import Test.Anyable
open import Class.HasAdd public
open import Class.HasOrder public
open import Class.HasMembership public; import Test.HasMembership

-- ** Others
open import Class.Default public
open import Class.Show public; import Test.Show
open import Class.MonotonePredicate public
open import Class.Default public
open import Class.Measurable public; import Test.Measurable
open import Class.Null public
open import Class.View public; import Test.View

-- ** Id monad.
-- Provides us with forward composition as _>=>_,
-- but might break instance-resolution/typeclass-inference

{-# OPTIONS --cubical-compatible #-}
module Class.Monad.Id where

open import Class.Prelude
open import Class.Functor.Core
open import Class.Applicative.Core
open import Class.Monad.Core

Id : Type ℓ → Type ℓ
Id = id

instance
  Functor-Id : Functor Id
  Functor-Id ._<$>_ = _$_
  {-# OVERLAPPABLE Functor-Id #-}

  Applicative-Id : Applicative Id
  Applicative-Id .pure  = id
  Applicative-Id ._<*>_ = _$_
  {-# OVERLAPPABLE Applicative-Id #-}

  Monad-Id : Monad Id
  Monad-Id .return = id
  Monad-Id ._>>=_  = _|>_
  {-# OVERLAPPABLE Monad-Id #-}

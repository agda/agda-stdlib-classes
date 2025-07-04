{-# OPTIONS --cubical-compatible #-}
module Class.Pointed.Core where

open import Class.Prelude
open import Class.Core
open import Class.Applicative.Core
open import Class.Monad.Core

record Pointed (F : Type↑) : Typeω where
  field point : ∀ {A : Type ℓ} → A → F A
open Pointed ⦃...⦄ public

Applicative⇒Pointed : ⦃ Applicative F ⦄ → Pointed F
Applicative⇒Pointed .point = pure

Monad⇒Pointed : ⦃ Monad F ⦄ → Pointed F
Monad⇒Pointed .point = return

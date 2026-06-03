{-# OPTIONS --cubical-compatible #-}
module Class.Monad.Instances where

open import Class.Prelude
open import Class.Applicative
open import Class.Monad.Core

instance
  Monad-TC : Monad TC
  Monad-TC = record {R}
    where import Reflection as R renaming (pure to return)

  Monad-List : Monad List
  Monad-List = λ where
    .return → _∷ []
    ._>>=_  → flip concatMap

  Monad-Maybe : Monad Maybe
  Monad-Maybe = λ where
    .return → just
    ._>>=_  → Maybe._>>=_
   where import Data.Maybe as Maybe

  MonadLaws-Maybe : MonadLaws Maybe
  MonadLaws-Maybe = λ where
    .>>=-identityˡ → refl
    .>>=-identityʳ → λ where
      (just _) → refl
      nothing  → refl
    .>>=-assoc → λ where
      (just _) → refl
      nothing  → refl

module _ {X : Type ℓ} where
  module Monad-Sumˡ = MkMonad {M = X ⊎_}
    inj₂ (λ where (inj₁ a) f → inj₁ a; (inj₂ b) f → f b)
  module Monad-Sumʳ = MkMonad {M = _⊎ X}
    inj₁ (λ where (inj₁ a) f → f a; (inj₂ b) f → inj₂ b)

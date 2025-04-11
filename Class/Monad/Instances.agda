{-# OPTIONS --cubical-compatible #-}
module Class.Monad.Instances where

open import Class.Prelude
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

  Monad-Sumˡ : Monad (_⊎ A)
  Monad-Sumˡ = λ where
    .return → inj₁
    ._>>=_ (inj₁ a) f → f a
    ._>>=_ (inj₂ b) f → inj₂ b

  Monad-Sumʳ : Monad (A ⊎_)
  Monad-Sumʳ = λ where
    .return → inj₂
    ._>>=_ (inj₁ a) f → inj₁ a
    ._>>=_ (inj₂ b) f → f b

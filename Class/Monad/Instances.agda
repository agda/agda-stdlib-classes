{-# OPTIONS --cubical-compatible #-}
module Class.Monad.Instances where

open import Class.Prelude
open import Class.Monad.Core

private variable a : Level

instance
  Monad-TC : Monad {a} TC
  Monad-TC = record {R}
    where import Reflection as R renaming (pure to return)

  Monad-List : Monad {a} List
  Monad-List = λ where
    .return → _∷ []
    ._>>=_  → flip concatMap

  Monad-Maybe : Monad {a} Maybe
  Monad-Maybe = λ where
    .return → just
    ._>>=_  → Maybe._>>=_
   where import Data.Maybe as Maybe

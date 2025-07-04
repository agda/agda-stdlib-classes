{-# OPTIONS --cubical-compatible #-}
module Class.Anyable.Instances where

open import Class.Prelude
open import Class.Anyable.Core

import Data.List.Relation.Unary.Any as L
import Data.Vec.Relation.Unary.Any as V
import Data.Maybe.Relation.Unary.Any as M

instance
  Anyable-List : Anyable {ℓ} List
  Anyable-List .Any = L.Any

  Anyable-Vec : ∀ {n} → Anyable {ℓ} (flip Vec n)
  Anyable-Vec .Any P = V.Any P

  Anyable-Maybe : Anyable {ℓ} Maybe
  Anyable-Maybe .Any = M.Any

  Anyable-List⁺ : Anyable {ℓ} List⁺
  Anyable-List⁺ .Any P = Any P ∘ L⁺.toList

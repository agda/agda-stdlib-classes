{-# OPTIONS --cubical-compatible #-}
module Class.Allable.Instances where

open import Class.Prelude
open import Class.Allable.Core

import Data.List.Relation.Unary.All as L
import Data.Vec.Relation.Unary.All as V
import Data.Maybe.Relation.Unary.All as M

instance
  Allable-List : Allable {ℓ} List
  Allable-List .All = L.All

  Allable-Vec : ∀ {n} → Allable {ℓ} (flip Vec n)
  Allable-Vec .All P = V.All P

  Allable-Maybe : Allable {ℓ} Maybe
  Allable-Maybe .All = M.All

  Allable-List⁺ : Allable {ℓ} List⁺
  Allable-List⁺ .All P = All P ∘ L⁺.toList

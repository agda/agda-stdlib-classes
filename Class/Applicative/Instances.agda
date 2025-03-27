{-# OPTIONS --cubical-compatible #-}
module Class.Applicative.Instances where

open import Class.Prelude
open import Class.Functor.Core
open import Class.Functor.Instances
open import Class.Applicative.Core

private variable a : Level

instance
  Applicative-Maybe : Applicative {a} Maybe
  Applicative-Maybe = λ where
    .pure → just
    ._<*>_ → maybe fmap (const nothing)

  Applicative₀-Maybe : Applicative₀ {a} Maybe
  Applicative₀-Maybe .ε₀ = nothing

  Alternative-Maybe : Alternative {a} Maybe
  Alternative-Maybe ._<|>_ = May._<∣>_
    where import Data.Maybe as May

  Applicative-List : Applicative {a} List
  Applicative-List = λ where
    .pure → [_]
    ._<*>_ → flip $ concatMap ∘ _<&>_

  Applicative₀-List : Applicative₀ {a} List
  Applicative₀-List .ε₀ = []

  Alternative-List : Alternative {a} List
  Alternative-List ._<|>_ = _++_

  Applicative-List⁺ : Applicative {a} List⁺
  Applicative-List⁺ = λ where
    .pure → L⁺.[_]
    ._<*>_ → flip $ L⁺.concatMap ∘ _<&>_
   where import Data.List.NonEmpty as L⁺

  Applicative-Vec : ∀ {n} → Applicative {a} (flip Vec n)
  Applicative-Vec = λ where
    .pure → V.replicate _
    ._<*>_ → V._⊛_
   where import Data.Vec as V

  Applicative₀-Vec : Applicative₀ {a} (flip Vec 0)
  Applicative₀-Vec .ε₀ = []

  -- Applicative-∃Vec : Applicative (∃ ∘ Vec)
  -- Applicative-∃Vec = λ where
  --   .pure x → 1 , pure x
  --   ._<*>_ (n , xs) (m , ys) → {! (n ⊔ m) , zipWith _$_ xs ys  -- (+ zipWith-⊔ lemma) !}

  private module M where
    open import Reflection.TCM.Syntax public
    open import Reflection.TCM public

  Alternative-TC : Alternative {a} TC
  Alternative-TC = record {M}

  Applicative-TC : Applicative {a} TC
  Applicative-TC = record {M}

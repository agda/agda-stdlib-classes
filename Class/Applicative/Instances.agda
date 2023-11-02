module Class.Applicative.Instances where

open import Class.Prelude
open import Class.Functor.Core
open import Class.Functor.Instances
open import Class.Applicative.Core

instance
  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe = λ where
    .pure → just
    ._<*>_ → maybe fmap (const nothing)

  Applicative₀-Maybe : Applicative₀ Maybe
  Applicative₀-Maybe .ε₀ = nothing

  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe ._<|>_ = May._<∣>_
    where import Data.Maybe as May

  Applicative-List : Applicative List
  Applicative-List = λ where
    .pure → [_]
    ._<*>_ → flip $ concatMap ∘ _<&>_

  Applicative₀-List : Applicative₀ List
  Applicative₀-List .ε₀ = []

  Alternative-List : Alternative List
  Alternative-List ._<|>_ = _++_

  Applicative-List⁺ : Applicative List⁺
  Applicative-List⁺ = λ where
    .pure → L⁺.[_]
    ._<*>_ → flip $ L⁺.concatMap ∘ _<&>_
   where import Data.List.NonEmpty as L⁺

  Applicative-Vec : ∀ {n} → Applicative (flip Vec n)
  Applicative-Vec = λ where
    .pure → V.replicate
    ._<*>_ → V._⊛_
   where import Data.Vec as V


  Applicative₀-Vec : Applicative₀ (flip Vec 0)
  Applicative₀-Vec .ε₀ = []

  -- Applicative-∃Vec : Applicative (∃ ∘ Vec)
  -- Applicative-∃Vec = λ where
  --   .pure x → 1 , pure x
  --   ._<*>_ (n , xs) (m , ys) → {! (n ⊔ m) , zipWith _$_ xs ys  -- (+ zipWith-⊔ lemma) !}

  Alternative-TC : Alternative TC
  Alternative-TC = record {M}
    where import Reflection.TypeChecking.Monad.Syntax as M

  Applicative-TC : Applicative TC
  Applicative-TC = record {M}
    where import Reflection.TypeChecking.Monad.Syntax as M

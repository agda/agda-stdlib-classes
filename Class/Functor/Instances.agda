{-# OPTIONS --cubical-compatible #-}
module Class.Functor.Instances where

open import Class.Prelude
open import Class.Functor.Core

private variable a : Level

instance
  Functor-Maybe : Functor {a} Maybe
  Functor-Maybe = record {M}
    where import Data.Maybe as M renaming (map to _<$>_)

  FunctorLaws-Maybe : FunctorLaws {a} Maybe
  FunctorLaws-Maybe = λ where
    .fmap-id → λ where (just _) → refl; nothing → refl
    .fmap-∘  → λ where (just _) → refl; nothing → refl

  Functor-List : Functor {a} List
  Functor-List ._<$>_ = map

  FunctorLaws-List : FunctorLaws {a} List
  FunctorLaws-List = record {fmap-id = p; fmap-∘ = q}
    where
      p : ∀ {A : Type ℓ} (x : List A) → fmap id x ≡ x
      p = λ where
        [] → refl
        (x ∷ xs) → cong (x ∷_) (p xs)

      q : ∀ {A B C : Type ℓ} {f : B → C} {g : A → B} (x : List A) →
        fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
      q {f = f}{g} = λ where
        [] → refl
        (x ∷ xs) → cong (f (g x) ∷_) (q xs)

  Functor-List⁺ : Functor {a} List⁺
  Functor-List⁺ = record {L}
    where import Data.List.NonEmpty as L renaming (map to _<$>_)

  Functor-Vec : ∀ {n} → Functor {a} (flip Vec n)
  Functor-Vec = record {V}
    where import Data.Vec as V renaming (map to _<$>_)

  Functor-TC : Functor {a} TC
  Functor-TC = record {R}
    where import Reflection.TCM.Syntax as R

  Functor-Abs : Functor {a} Abs
  Functor-Abs = record {R}
    where import Reflection.AST.Abstraction as R renaming (map to _<$>_)

  Functor-Arg : Functor {a} Arg
  Functor-Arg = record {R}
    where import Reflection.AST.Argument as R renaming (map to _<$>_)

  Functor-∃Vec : Functor {a} (∃ ∘ Vec)
  Functor-∃Vec ._<$>_ f (_ , xs) = -, (f <$> xs)

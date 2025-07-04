{-# OPTIONS --cubical-compatible #-}
module Class.Pointed.Instances where

open import Class.Prelude
open import Class.Pointed.Core
open import Class.Applicative.Instances

instance
  P-Maybe = Applicative⇒Pointed {F = Maybe}
  P-List  = Applicative⇒Pointed {F = List}
  P-List⁺ = Applicative⇒Pointed {F = List⁺}
  P-TC    = Applicative⇒Pointed {F = TC}
  P-Vec   = λ {n} → Applicative⇒Pointed {F = flip Vec n}

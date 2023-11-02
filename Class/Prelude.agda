module Class.Prelude where

open import Agda.Primitive public
  using () renaming (Set to Type; Setω to Typeω)
open import Level public
  using (Level; _⊔_) renaming (suc to lsuc)
open import Function public
  using (id; _∘_; _∋_; _$_; const; constᵣ; flip)

open import Data.Unit public
  using (⊤; tt)
open import Data.Product public
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; -,_)
open import Data.Sum public
  using (_⊎_; inj₁; inj₂)
open import Data.Bool public
  using (Bool; true; false; not; if_then_else_)
open import Data.Nat public
  using (ℕ; zero; suc)
open import Data.Fin as Fin public
  using (Fin; zero; suc)
open import Data.Integer public
  using (ℤ; 0ℤ; 1ℤ)
open import Data.Float public
  using (Float)
open import Data.Char public
  using (Char)
open import Data.String public
  using (String)
open import Data.Maybe public
  using (Maybe; just; nothing; maybe; fromMaybe)
open import Data.List public
  using (List; []; _∷_; [_]; map; _++_; foldr; concat; concatMap)
open import Data.List.NonEmpty public
  using (List⁺; _∷_; _⁺++⁺_; foldr₁)
open import Data.Vec public
  using (Vec; []; _∷_)
open import Data.These public
  using (These; this; that; these)

open import Relation.Nullary public
  using (yes; no)
open import Relation.Nullary.Decidable public
  using (⌊_⌋; dec-yes)
open import Relation.Binary public
  using (Rel; DecidableEquality)
  renaming (Decidable to Decidable²)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; cong)

open import Reflection public
  using (TC; Arg; Abs)

variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

module Alg (_~_ : Rel A ℓ) where
  open import Algebra.Definitions _~_ public
module Alg≡ {ℓ} {A : Type ℓ} = Alg (_≡_ {A = A})
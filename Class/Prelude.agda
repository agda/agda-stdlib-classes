{-# OPTIONS --cubical-compatible #-}
module Class.Prelude where

open import Agda.Primitive public
  using () renaming (Set to Type; Setω to Typeω)
open import Level public
  using (Level; _⊔_; Lift; lift; 0ℓ) renaming (suc to lsuc)
module Fun where open import Function.Base public
open Fun public
  using (id; _∘_; _∘₂_; _∋_; _$_; const; constᵣ; flip; it; case_of_; _|>_)

open import Data.Empty public
  using (⊥; ⊥-elim)
open import Data.Unit public
  using (⊤; tt)
open import Data.These public
  using (These; this; that; these)
open import Data.Refinement public
  using (Refinement; _,_; value)
module Prod where open import Data.Product public
open Prod public
  using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃-syntax; -,_)
module Sum where open import Data.Sum public
open Sum public
  using (_⊎_; inj₁; inj₂)
module 𝔹 where open import Data.Bool public
open 𝔹 public
  using (Bool; true; false; not; if_then_else_; T)
module Nat where open import Data.Nat public; open import Data.Nat.Properties public
open Nat public
  using (ℕ; zero; suc)
module Bin where open import Data.Nat.Binary public
open Bin public
  using (ℕᵇ)
module Fi where open import Data.Fin public
open Fi public
  using (Fin; zero; suc)
module Int where open import Data.Integer public
open Int public
  using (ℤ; 0ℤ; 1ℤ; -_)
module Q where open import Data.Rational public
open Q public
  using (ℚ)
module Fl where open import Data.Float public
open Fl public
  using (Float)
module Ch where open import Data.Char public
open Ch public
  using (Char)
module Str where open import Data.String public
open Str public
  using (String)
module Word where open import Data.Word64 public
open Word public
  using (Word64)
module Mb where open import Data.Maybe public
open Mb public
  using (Maybe; just; nothing; maybe; fromMaybe)
module L where open import Data.List public
open L public
  using (List; []; _∷_; [_]; map; _++_; foldr; concat; concatMap; length)
module L⁺ where open import Data.List.NonEmpty public
open L⁺ public
  using (List⁺; _∷_; _⁺++⁺_; foldr₁)
module V where open import Data.Vec public
open V public
  using (Vec; []; _∷_)

module Meta where
  open import Reflection public
  open import Reflection.AST public
  open import Reflection.TCM public
open Meta public
  using (TC; Arg; Abs)

open import Relation.Nullary public
  using (¬_; Dec; does; yes; no; contradiction; Irrelevant)
open import Relation.Nullary.Decidable public
  using (⌊_⌋; dec-yes; isYes; _×-dec_)
  renaming (map′ to mapDec)
open import Relation.Unary public
  using (Pred)
  renaming (Decidable to Decidable¹)
open import Relation.Binary public
  using ( REL; Rel; DecidableEquality
        ; IsEquivalence; Setoid
        )
  renaming (Decidable to Decidable²)
module _ {a b c} where
  3REL : (A : Type a) (B : Type b) (C : Type c) (ℓ : Level) → Type _
  3REL A B C ℓ = A → B → C → Type ℓ

  Decidable³ : ∀ {A B C ℓ} → 3REL A B C ℓ → Type _
  Decidable³ _~_~_ = ∀ x y z → Dec (x ~ y ~ z)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; refl; sym; cong; subst; trans)

variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level
  A B C : Type ℓ
  x y : A
  P Q : Pred A ℓ
  R R′ : Rel A ℓ
  n m : ℕ

module Alg (_~_ : Rel A ℓ) where
  open import Algebra.Definitions _~_ public
module Alg≡ {ℓ} {A : Type ℓ} = Alg (_≡_ {A = A})

itω : ∀ {A : Typeω} → ⦃ A ⦄ → A
itω ⦃ x ⦄ = x

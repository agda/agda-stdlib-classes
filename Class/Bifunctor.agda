{-# OPTIONS --cubical-compatible #-}
module Class.Bifunctor where

open import Class.Prelude hiding (A; B; C)
open import Class.Core
import Data.Product as ×
import Data.Sum     as ⊎

private variable
  a b : Level
  A : Type a; A′ : Type a; A″ : Type a
  B : A → Type b; B′ : A → Type b; C : A′ → Type b

-- ** indexed/dependent version
record BifunctorI
  (F : (A : Type a) (B : A → Type b) → Type (a ⊔ b)) : Type (lsuc (a ⊔ b)) where
  field
    bimap′ : (f : A → A′) → (∀ {x} → B x → C (f x)) → F A B → F A′ C

  map₁′ : (A → A′) → F A (const A″) → F A′ (const A″)
  map₁′ f = bimap′ f id
  _<$>₁′_ = map₁′

  map₂′ : (∀ {x} → B x → B′ x) → F A B → F A B′
  map₂′ g = bimap′ id g
  _<$>₂′_ = map₂′

  infixl 4 _<$>₁′_ _<$>₂′_

open BifunctorI ⦃...⦄ public

instance
  Bifunctor-Σ : BifunctorI {a}{b} Σ
  Bifunctor-Σ .bimap′ = ×.map

-- ** non-dependent version
Type[_∣_↝_] : ∀ ℓ ℓ′ ℓ″ → Type _
Type[ ℓ ∣ ℓ′ ↝ ℓ″ ] = Type ℓ → Type ℓ′ → Type ℓ″

Level↑² = Level → Level → Level

Type↑² : Level↑² → Typeω
Type↑² ℓ↑² = ∀ {ℓ ℓ′} → Type[ ℓ ∣ ℓ′ ↝ ℓ↑² ℓ ℓ′ ]

variable
  ℓ↑² : Level → Level → Level

record Bifunctor (F : Type↑² ℓ↑²) : Typeω where
  field
    bimap : ∀ {A A′ : Type a} {B B′ : Type b} → (A → A′) → (B → B′) → F A B → F A′ B′

-- record Bifunctor {a}{b} (F : Type a → Type b → Type (a ⊔ b)) : Type (lsuc (a ⊔ b)) where
--   field
--     bimap : ∀ {A A′ : Type a} {B B′ : Type b} → (A → A′) → (B → B′) → F A B → F A′ B′

  map₁ : ∀ {A A′ : Type a} {B : Type b} → (A → A′) → F A B → F A′ B
  map₁ f = bimap f id
  _<$>₁_ = map₁

  map₂ : ∀ {A : Type a} {B B′ : Type b} → (B → B′) → F A B → F A B′
  map₂ g = bimap id g
  _<$>₂_ = map₂

  infixl 4 _<$>₁_ _<$>₂_

open Bifunctor ⦃...⦄ public

map₁₂ : ∀ {F : Type↑² ℓ↑²} ⦃ _ : Bifunctor F ⦄ →
  (∀ {a} {A B : Type a} → (A → B) → F A A → F B B)
map₁₂ f = bimap f f
_<$>₁₂_ = map₁₂
infixl 4 _<$>₁₂_

instance
  Bifunctor-× : Bifunctor _×_
  Bifunctor-× .bimap f g = ×.map f g

  Bifunctor-⊎ : Bifunctor _⊎_
  Bifunctor-⊎ .bimap = ⊎.map

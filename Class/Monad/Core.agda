{-# OPTIONS --cubical-compatible #-}
module Class.Monad.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor
open import Class.Applicative

record Monad (M : Type↑) : Typeω where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    overlap ⦃ super ⦄ : Applicative M
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  _>>_ : M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _≫=_ = _>>=_; _≫_ = _>>_; _=≪_ = _=<<_

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  join : M (M A) → M A
  join m = m >>= id

  Functor-M : Functor M
  Functor-M = λ where ._<$>_ f x → return ∘ f =<< x

open Monad ⦃...⦄ public

module _ ⦃ _ : Monad M ⦄ where
  mapM : (A → M B) → List A → M (List B)
  mapM f []       = return []
  mapM f (x ∷ xs) = ⦇ f x ∷ mapM f xs ⦈

  concatMapM : (A → M (List B)) → List A → M (List B)
  concatMapM f xs = concat <$> mapM f xs

  forM : List A → (A → M B) → M (List B)
  forM []       _ = return []
  forM (x ∷ xs) f = ⦇ f x ∷ forM xs f ⦈

  concatForM : List A → (A → M (List B)) → M (List B)
  concatForM xs f = concat <$> forM xs f

  return⊤ void : M A → M ⊤
  return⊤ k = k ≫ return tt
  void = return⊤

  filterM : (A → M Bool) → List A → M (List A)
  filterM _ [] = return []
  filterM p (x ∷ xs) = do
    b ← p x
    ((if b then [ x ] else []) ++_) <$> filterM p xs

  traverseM : (A → M B) → List A → M (List B)
  traverseM f = λ where
    [] → return []
    (x ∷ xs) → ⦇ f x ∷ traverseM f xs ⦈

record MonadLaws (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  field
    >>=-identityˡ : ∀ {A : Type ℓ} {B : Type ℓ′} →
      ∀ {a : A} {h : A → M B} →
        (return a >>= h) ≡ h a
    >>=-identityʳ : ∀ {A : Type ℓ} →
      ∀ (m : M A) →
        (m >>= return) ≡ m
    >>=-assoc : ∀ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} →
      ∀ (m : M A) {g : A → M B} {h : B → M C} →
        ((m >>= g) >>= h) ≡ (m >>= (λ x → g x >>= h))
open MonadLaws ⦃...⦄ public

record Monad₀ (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ isApplicative₀ ⦄ : Applicative₀ M
open Monad₀ ⦃...⦄ using () public
instance
  mkMonad₀ : ⦃ Monad M ⦄ → ⦃ Applicative₀ M ⦄ → Monad₀ M
  mkMonad₀ = record {}

record Monad⁺ (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ isAlternative ⦄ : Alternative M
open Monad⁺ ⦃...⦄ using () public
instance
  mkMonad⁺ : ⦃ Monad M ⦄ → ⦃ Alternative M ⦄ → Monad⁺ M
  mkMonad⁺ = record {}

{-# OPTIONS --cubical-compatible #-}
module Test.Functor where

open import Class.Prelude
open import Class.Functor
-- open import Class.Bifunctor

_ = fmap suc (just 0) ≡ just 1
  ∋ refl
_ = fmap suc (List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
_ = fmap suc (List⁺ ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
_ = fmap suc (Vec ℕ 3 ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl
_ = fmap suc (∃ (Vec ℕ) ∋ -, 0 ∷ 1 ∷ 2 ∷ []) ≡ (-, 1 ∷ 2 ∷ 3 ∷ [])
  ∋ refl

-- _ = map₁ suc (0 , (List ℕ ∋ [])) ≡ (1 , [])
--   ∋ refl
-- _ = map₂ (2 ∷_) (0 , []) ≡ (0 , [ 2 ])
--   ∋ refl
-- _ = bimap suc (2 ∷_) (0 , []) ≡ (1 , [ 2 ])
--   ∋ refl
-- _ = map₁₂ suc (0 , 1) ≡ (1 , 2)
--   ∋ refl
-- _ = map₁′ suc (0 , (List ℕ ∋ [])) ≡ (1 , [])
--   ∋ refl
-- _ = map₂′ id (1 , 2 ∷ []) ≡ ((∃ λ n → Vec ℕ n) ∋ (1 , 2 ∷ []))
--   ∋ refl
-- _ = bimap′ suc (2 ∷_) (0 , []) ≡ ((∃ λ n → Vec ℕ n) ∋ (1 , 2 ∷ []))
--   ∋ refl

-- ** cross-level mapping
module _ (X : Type) (Y : Type₁) (Z : Type₂) (g : X → Y) (f : Y → Z) (xs : List X) where
  _ : fmap (f ∘ g)      xs
    ≡ (fmap f ∘ fmap g) xs
  _ = fmap-∘ xs

-- ** base level

data newtype (A : Type ℓ) : Type ℓ where
  mk : A → newtype A

data newtype₀ (A : Type) : Type where
  mk : A → newtype₀ A

instance
  _ : Functor {id} newtype
  _ = λ where ._<$>_ f (mk x) → mk (f x)

  -- ** WORKS even for non-polymorphic newtype₀
  _ : Functor newtype₀
  _ = λ where ._<$>_ f (mk x) → mk (f x)

{-# OPTIONS --cubical-compatible #-}
module Class.Monad.Core where

open import Class.Prelude
open import Class.Core
open import Class.Functor
open import Class.Applicative

record Monad {a b} (M : Type a → Type b) : Type (lsuc (a ⊔ b)) where
  infixl 1 _>>=_ _>>_ _>=>_
  infixr 1 _=<<_ _<=<_

  field
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  _>>_ : M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  Functor-M : Functor M
  Functor-M = λ where ._<$>_ f x → return ∘ f =<< x

  instance _ = Functor-M

  mapM : (A → M B) → List A → M (List B)
  mapM f []       = return []
  mapM f (x ∷ xs) = do y ← f x; y ∷_ <$> mapM f xs

  concatMapM : (A → M (List B)) → List A → M (List B)
  concatMapM f xs = concat <$> mapM f xs

  forM : List A → (A → M B) → M (List B)
  forM []       _ = return []
  forM (x ∷ xs) f = do y ← f x; y ∷_ <$> forM xs f

  concatForM : List A → (A → M (List B)) → M (List B)
  concatForM xs f = concat <$> forM xs f

  traverseM : ⦃ Applicative M ⦄ → ⦃ Monad M ⦄ → (A → M B) → List A → M (List B)
  traverseM f = λ where
    [] → return []
    (x ∷ xs) → ⦇ f x ∷ traverseM f xs ⦈

  _<$₂>_,_ : (A → B → C) → M A → M B → M C
  f <$₂> x , y = do x ← x; y ← y; return (f x y)
open Monad ⦃...⦄ public

join : ∀ {a} {M : Type a → Type a} ⦃ _ : Monad M ⦄ {A : Type a} → M (M A) → M A
join m = m >>= id

module _ {a} {M : Type → Type a} ⦃ _ : Monad M ⦄ {A : Type} where
  return⊤ void : M A → M ⊤
  return⊤ k = k >> return tt
  void = return⊤

  filterM : (A → M Bool) → List A → M (List A)
  filterM _ [] = return []
  filterM p (x ∷ xs) = do
    b ← p x
    ((if b then [ x ] else []) ++_) <$> filterM p xs
    where instance _ = Functor-M

  infix 0 mif_then_
  mif_then_ : Bool → M ⊤ → M ⊤
  mif b then x = if b then x else return _

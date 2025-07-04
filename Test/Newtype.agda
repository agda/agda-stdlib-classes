{-# OPTIONS --without-K #-}
module Test.Newtype where

open import Class.Prelude
open import Class.Newtype
open import Class.Functor

ℕ˘ = newtype ℕ

_+˘_ : ℕ˘ → ℕ˘ → ℕ˘
n +˘ m = case unmk m of λ where
  0        → n
  (suc m′) → suc <$> (n +˘ mk m′)

+˘-identityˡ : ∀ x → mk 0 +˘ x ≡ x
+˘-identityˡ (mk 0)       = refl
+˘-identityˡ (mk (suc n)) rewrite +˘-identityˡ (mk n) = refl

H˘ : ∀ {n : ℕ˘} → n +˘ mk 0 ≡ n
H˘ = refl

H˘′ : ∀ {n : ℕ} → mk n +˘ mk 0 ≡ mk n
H˘′ = H˘

open Nat using (_+_)

+↔+˘ : ∀ (x y : ℕ) → x + y ≡ (mk x +˘ mk y) .unmk
+↔+˘ zero y rewrite +˘-identityˡ (mk y) = refl
+↔+˘ (suc x) zero    = cong suc $ Nat.+-identityʳ x
+↔+˘ (suc x) (suc y) = cong suc $ trans (Nat.+-suc x y) (+↔+˘ (suc x) y)

_ : ∀ {n : ℕ} → n + 0 ≡ n
_ = trans (+↔+˘ _ 0) (cong unmk H˘′)

-- T0D0: tactic to automate "newtype" transports

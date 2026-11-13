{-# OPTIONS --without-K #-}
module Class.Default.Instances where

open import Class.Prelude
open import Class.Default.Core

instance
  Default-⊤ = Default ⊤    ∋ λ where .def → tt
  Default-𝔹 = Default Bool ∋ λ where .def → true
  Default-ℕ = Default ℕ    ∋ λ where .def → zero
  Default-ℤ = Default ℤ    ∋ λ where .def → ℤ.pos def

  Default-Maybe : Default (Maybe A)
  Default-Maybe .def = nothing

  Default-List : Default (List A)
  Default-List .def = []

  Default-Fin : Default (Fin (suc n))
  Default-Fin .def = Fin.zero

  Default-→ : ⦃ Default B ⦄ → Default (A → B)
  Default-→ .def = const def

  module _ ⦃ _ : Default A ⦄ ⦃ _ : Default B ⦄ where
    Default-× = Default (A × B) ∋ λ where .def → def , def
    Default-⊎ = Default (A ⊎ B) ∋ λ where .def → inj₁ def

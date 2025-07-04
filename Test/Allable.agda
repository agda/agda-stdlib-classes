module Test.Allable where

open import Class.Prelude
open import Class.Allable
open import Class.Decidable
open import Class.HasOrder

_ : ∀[ x ∈ List ℕ ∋ 1 ∷ 2 ∷ 3 ∷ [] ] x > 0
_ = auto

_ : ∀[ x ∈ just 42 ] x > 0
_ = auto

_ : ∀[ x ∈ nothing ] x > 0
_ = auto

_ : ¬∀[ x ∈ just 0 ] x > 0
_ = auto

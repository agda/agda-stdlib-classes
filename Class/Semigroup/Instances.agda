{-# OPTIONS --cubical-compatible #-}
module Class.Semigroup.Instances where

open import Class.Prelude
open import Class.Semigroup.Core
open import Class.Setoid.Core
open import Class.Setoid.Instances

instance
  Semigroup-List : Semigroup (List A)
  Semigroup-List ._◇_ = _++_

  Semigroup-List⁺ : Semigroup (List⁺ A)
  Semigroup-List⁺ ._◇_ = _⁺++⁺_

  Semigroup-∃Vec : Semigroup (∃ (Vec A))
  Semigroup-∃Vec ._◇_ (_ , v) (_ , v′) = _ , (v V.++ v′)
    where import Data.Vec as V

  Semigroup-String : Semigroup String
  Semigroup-String ._◇_ = Str._++_
    where import Data.String as Str

module _ ⦃ _ : Semigroup A ⦄ where instance
  Semigroup-Maybe : Semigroup (Maybe A)
  Semigroup-Maybe ._◇_ = λ where
    (just x) (just y) → just (x ◇ y)
    (just x) nothing  → just x
    nothing  m        → m

  module _ ⦃ _ : SemigroupLaws≡ A ⦄ where instance
    SemigroupLaws≡-Maybe : SemigroupLaws≡ (Maybe A)
    SemigroupLaws≡-Maybe = record
      { ◇-assocʳ = λ where
          (just x) (just y) (just z) → cong just $ ◇-assocʳ≡ x y z
          (just x) (just y) nothing  → refl
          (just x) nothing  z        → refl
          nothing  (just y) z        → refl
          nothing  nothing  z        → refl
      ; ◇-comm = λ where
          (just x) (just y) → cong just $ ◇-comm≡ x y
          (just x) nothing  → refl
          nothing  (just y) → refl
          nothing  nothing  → it
      }

  module _ ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄ ⦃ _ : SemigroupLaws A ⦄ where instance
    SemigroupLaws-Maybe : SemigroupLaws (Maybe A)
    SemigroupLaws-Maybe = record
      { ◇-assocʳ = λ where
          (just x) (just y) (just z) → ◇-assocʳ x y z
          (just x) (just y) nothing  → ≈-refl {x = x ◇ y}
          (just x) nothing  z        → ≈-refl {x = just x ◇ z}
          nothing  (just y) z        → ≈-refl {x = just y ◇ z}
          nothing  nothing  z        → ≈-refl {x = z}
      ; ◇-comm = λ where
          (just x) (just y) → ◇-comm x y
          (just x) nothing  → ≈-refl {x = x}
          nothing  (just y) → ≈-refl {x = y}
          nothing  nothing  → lift tt
      }

module _ ⦃ _ : Semigroup A ⦄ ⦃ _ : Semigroup B ⦄ where instance
  Semigroup-× : Semigroup (A × B)
  Semigroup-× ._◇_ (a , b) (a′ , b′) = (a ◇ a′ , b ◇ b′)

  SemigroupLaws-× : ⦃ SemigroupLaws≡ A ⦄ → ⦃ SemigroupLaws≡ B ⦄
                  → SemigroupLaws≡ (A × B)
  SemigroupLaws-× = record {◇-assocʳ = p; ◇-comm = q}
    where
      open Alg≡

      p : Associative (_◇_ {A = A × B})
      p (a , b) (c , d) (e , f) rewrite ◇-assocʳ≡ a c e | ◇-assocʳ≡ b d f = refl

      q : Commutative (_◇_ {A = A × B})
      q (a , b) (c , d) rewrite ◇-comm≡ a c | ◇-comm≡ b d = refl

-- ** natural numbers
module _ where
  open import Data.Nat
  open import Data.Nat.Properties

  Semigroup-ℕ-+ = Semigroup ℕ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℕ-+ = SemigroupLaws≡ ℕ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℕ-+

  Semigroup-ℕ-* = Semigroup ℕ ∋ λ where ._◇_ → _*_
  SemigroupLaws-ℕ-* = SemigroupLaws≡ ℕ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℕ-*

-- ** binary natural numbers
module _ where
  open import Data.Nat.Binary
  open import Data.Nat.Binary.Properties

  Semigroup-ℕᵇ-+ = Semigroup ℕᵇ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℕᵇ-+ = SemigroupLaws≡ ℕᵇ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℕᵇ-+

-- ** integers
module _ where
  open import Data.Integer
  open import Data.Integer.Properties

  Semigroup-ℤ-+ = Semigroup ℤ ∋ λ where ._◇_ → _+_
  SemigroupLaws-ℤ-+ = SemigroupLaws≡ ℤ ∋
    record {◇-assocʳ = +-assoc; ◇-comm = +-comm}
    where instance _ = Semigroup-ℤ-+

  Semigroup-ℤ-* = Semigroup ℤ ∋ λ where ._◇_ → _*_
  SemigroupLaws-ℤ-* = SemigroupLaws≡ ℤ ∋
    record {◇-assocʳ = *-assoc; ◇-comm = *-comm}
    where instance _ = Semigroup-ℤ-*

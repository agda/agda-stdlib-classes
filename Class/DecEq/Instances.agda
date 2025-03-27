{-# OPTIONS --without-K #-}
module Class.DecEq.Instances where

open import Class.Prelude
open import Class.DecEq.Core

-- ** basic types
instance
  DecEq-⊥      = DecEq ⊥ ∋ λ where ._≟_ ()
  DecEq-⊤      = DecEq _ ∋ record {M} where import Data.Unit as M
  DecEq-Bool   = DecEq _ ∋ record {M} where import Data.Bool as M
  DecEq-ℕ      = DecEq _ ∋ record {M} where import Data.Nat as M
  DecEq-ℤ      = DecEq _ ∋ record {M} where import Data.Integer as M
  DecEq-ℚ      = DecEq _ ∋ record {M} where import Data.Rational.Properties as M
  DecEq-Char   = DecEq _ ∋ record {M} where import Data.Char as M
  DecEq-String = DecEq _ ∋ record {M} where import Data.String as M

  DecEq-Fin : DecEq¹ Fin
  DecEq-Fin = record {M} where import Data.Fin as M

  DecEq-List : ⦃ DecEq A ⦄ → DecEq (List A)
  DecEq-List ._≟_ = M.≡-dec _≟_ where import Data.List.Properties as M

-- ** containers of decidably equal elements
private
  ∷-injective : ∀ {x y xs ys} →
    (List⁺ A ∋ x ∷ xs) ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-injective refl = (refl , refl)

module _ ⦃ _ : DecEq A ⦄ where instance
  DecEq-List⁺ : DecEq (List⁺ A)
  DecEq-List⁺ ._≟_ (x ∷ xs) (y ∷ ys)
    with x ≟ y
  ... | no x≢y = no $ x≢y ∘ proj₁ ∘ ∷-injective
  ... | yes refl
    with xs ≟ ys
  ... | no xs≢ys = no $ xs≢ys ∘ proj₂ ∘ ∷-injective
  ... | yes refl = yes refl

  DecEq-Vec : DecEq¹ (Vec A)
  DecEq-Vec ._≟_ = M.≡-dec _≟_
    where import Data.Vec.Properties as M

  DecEq-Maybe : DecEq (Maybe A)
  DecEq-Maybe ._≟_ = M.≡-dec _≟_
    where import Data.Maybe.Properties as M

  DecEq-Refinement : ∀ {P : A → Set ℓ} → DecEq (Refinement A P)
  DecEq-Refinement ._≟_ x y
    with x .value ≟ y .value
  ... | yes refl = yes refl
  ... | no ¬eq   = no (¬eq ∘ cong value)

module _ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where

  -- Not exported as instance so that users can also choose `Class.DecEq.WithK.DecEq-Σ`
  DecEq-× : DecEq (A × B)
  DecEq-× ._≟_ = ×.≡-dec _≟_ _≟_
    where import Data.Product.Properties as ×

  instance
    DecEq-⊎ : DecEq (A ⊎ B)
    DecEq-⊎ ._≟_ = ⊎.≡-dec _≟_ _≟_
      where import Data.Sum.Properties as ⊎

    DecEq-These : DecEq (These A B)
    DecEq-These ._≟_ = M.≡-dec _≟_ _≟_
      where import Data.These.Properties as M

-- ** reflection
instance
  DecEq-Name = DecEq _ ∋ record {M} where import Reflection.AST.Name as M
  DecEq-Lit  = DecEq _ ∋ record {M} where import Reflection.AST.Literal as M
  DecEq-Meta = DecEq _ ∋ record {M} where import Reflection.AST.Meta as M
  DecEq-Term = DecEq _ ∋ record {M} where import Reflection.AST.Term as M
  DecEq-Mod  = DecEq _ ∋ record {M}
    where import Reflection.AST.Argument.Modality as M
  DecEq-Vis  = DecEq _ ∋ record {M}
    where import Reflection.AST.Argument.Visibility as M
  DecEq-ArgI = DecEq _ ∋ record {M}
    where import Reflection.AST.Argument.Information as M

  -- put this last to work around Agda issue #6976
  DecEq-Arg : ⦃ DecEq A ⦄ → DecEq (Arg A)
  DecEq-Arg ._≟_ = M.≡-dec _≟_ where import Reflection.AST.Argument as M

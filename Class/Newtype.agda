----------------------------------------
-- Emulating Haskell's newtype feature.
----------------------------------------

{-# OPTIONS --without-K #-}
module Class.Newtype where

open import Function.Bundles using (_↔_; mk↔)

open import Class.Prelude
open import Class.Functor

record newtype (A : Type ℓ) : Type ℓ where
  constructor mk
  field unmk : A
open newtype public

instance
  Functor-newtype : Functor newtype
  Functor-newtype ._<$>_ f = mk ∘ f ∘ unmk

  mkNewtype : ⦃ A ⦄ → newtype A
  mkNewtype = mk it

mk-injective : ∀ (x y : A) → mk x ≡ mk y → x ≡ y
mk-injective _ _ refl = refl

newtype¹ : Pred A ℓ → Pred A ℓ
newtype¹ P x = newtype (P x)

newtype² : Rel A ℓ → Rel A ℓ
newtype² _~_ x y = newtype (x ~ y)

newtype↔ : newtype A ↔ A
newtype↔ = mk↔ {to = unmk} $ (λ where refl → refl) , (λ where refl → refl)

mk? : Dec A → Dec (newtype A)
mk? = mapDec mk unmk

unmk? : Dec (newtype A) → Dec A
unmk? = mapDec unmk mk

mk?¹ : Decidable¹ P → Decidable¹ (newtype¹ P)
mk?¹ P? x = mk? (P? x)

unmk?¹ : Decidable¹ (newtype¹ P) → Decidable¹ P
unmk?¹ P? x = unmk? (P? x)

mk?² : Decidable² R → Decidable² (newtype² R)
mk?² R? x y = mk? (R? x y)

unmk?² : Decidable² (newtype² R) → Decidable² R
unmk?² R? x y = unmk? (R? x y)

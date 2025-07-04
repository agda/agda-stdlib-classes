{-# OPTIONS --without-K #-}
module Class.MonotonePredicate.Core where

open import Class.Prelude hiding (trans)
open import Class.HasOrder

open import Relation.Unary
open import Relation.Binary using (IsPreorder ; IsEquivalence)

open import Level

-- We make the "simplifying" assumption here that everything (carrier,
-- relation, etc...) lives at the same level. Otherwise we couldn't
-- express the (co)monadic structure of the possiblity and necessity
-- modalities.
module _ {A : Type ℓ}
         ⦃ _ : HasPreorder {A = A} {_≈_ = _≡_} {ℓ} {ℓ} ⦄ where

  open IsPreorder {ℓ} ≤-isPreorder

  record Monotone {ℓ′} (P : Pred A ℓ′) : Type (ℓ ⊔ ℓ′ ⊔ ℓ) where
    field
      weaken : ∀ {a a′} → a ≤ a′ → P a → P a′

  record Antitone {ℓ′} (P : Pred A ℓ′) : Type (ℓ ⊔ ℓ′ ⊔ ℓ″) where
    field
      strengthen : ∀ {a a′} → a′ ≤ a → P a → P a′

  open Monotone ⦃...⦄
  open Antitone ⦃...⦄

  -- The posibility modality. One way to think about posibility is as a unary
  -- version of separating conjunction.
  record ◇ (P : Pred A ℓ) (a : A) : Set ℓ where
    constructor ◇⟨_,_⟩
    field
      {a′}    : A
      ι       : a′ ≤ a
      px      : P a′

  open ◇ public

  -- The necessity modality. In a similar spirit, we can view necessity as a unary
  -- version of separating implication.
  record □ (P : Pred A ℓ) (a : A) : Set ℓ where
    constructor necessary
    field
      □⟨_⟩_ : ∀ {a′} → (ι : a ≤ a′) → P a′

  open □ public

  module Operations where

    -- □ is a comonad over the category of monotone predicates over `A`
    extract : ∀ {P} → ∀[ □ P ⇒ P ]
    extract px = □⟨ px ⟩ reflexive _≡_.refl

    duplicate : ∀ {P} → ∀[ □ P ⇒ □ (□ P) ]
    duplicate px = necessary λ ι → necessary λ ι′ → □⟨ px ⟩ trans ι ι′


    -- ◇ is a monad over the category of monotone predicates over `A`.
    return : ∀ {P} → ∀[ P ⇒ ◇ P ]
    return px = ◇⟨ reflexive _≡_.refl , px ⟩

    join : ∀ {P} → ∀[ ◇ (◇ P) ⇒ ◇ P ]
    join ◇⟨ ι₁ , ◇⟨ ι₂ , px ⟩ ⟩ = ◇⟨ (trans ι₂ ι₁) , px ⟩

    -- □ is right-adjoint to ◇
    curry : ∀ {P Q} → ∀[ ◇ P ⇒ Q ] → ∀[ P ⇒ □ Q ]
    curry f px = necessary (λ ι → f ◇⟨ ι , px ⟩)

    uncurry : ∀ {P Q} → ∀[ P ⇒ □ Q ] → ∀[ ◇ P ⇒ Q ]
    uncurry f ◇⟨ ι , px ⟩ = □⟨ f px ⟩ ι


    -- The "Kripke exponent" (or, Kripke function space) between two predicates is
    -- defined as the necessity of their implication.
    _⇛_ : ∀ (P Q : Pred A ℓ) → Pred A ℓ
    P ⇛ Q = □ (P ⇒ Q)

    kripke-curry : {P Q R : Pred A ℓ} → ⦃ Monotone P ⦄ → ∀[ (P ∩ Q) ⇒ R ] → ∀[ P ⇒ (Q ⇛ R) ]
    kripke-curry f px₁ = necessary (λ i px₂ → f (weaken i px₁ , px₂))

    kripke-uncurry : {P Q R : Pred A ℓ} → ∀[ P ⇒ (Q ⇛ R) ] → ∀[ (P ∩ Q) ⇒ R ]
    kripke-uncurry f (px₁ , px₂) = □⟨ f px₁ ⟩ reflexive _≡_.refl $ px₂

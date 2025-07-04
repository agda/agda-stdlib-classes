{-# OPTIONS --cubical-compatible #-}
module Class.FromList where

open import Class.Prelude

record FromList (A : Type ℓ) (B : List A → Type ℓ′) : Type (ℓ ⊔ ℓ′) where
  field fromList : (xs : List A) → B xs
  _∙fromList = fromList
open FromList ⦃...⦄ public

instance
  FromList-List : FromList A (const $ List A)
  FromList-List .fromList = id

  FromList-Str : FromList Char (const $ String)
  FromList-Str .fromList = Str.fromList

  FromList-∃Vec : FromList A (const $ ∃ $ Vec A)
  FromList-∃Vec .fromList xs = length xs , V.fromList xs

  FromList-Vec : FromList A (Vec A ∘ length)
  FromList-Vec .fromList = V.fromList

open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.Any using (there)
open import Data.List.Membership.Propositional using (_∈_; mapWith∈)

-- open import Data.List.Membership.Propositional.Properties using (length-mapWith∈)
length-mapWith∈ : ∀ {xs : List A} (f : ∀ {x} → x ∈ xs → B) →
  length (mapWith∈ xs f) ≡ length xs
length-mapWith∈ {xs = []} _ = refl
length-mapWith∈ {xs = _ ∷ xs} f = cong suc $ length-mapWith∈ {xs = xs} (f ∘ there)

module _ {A B : Type} (xs : List A) where

  fromList∘map : (f : A → B) → Vec B (length xs)
  fromList∘map f = subst (Vec B) (length-map f xs)
                 $ fromList (map f xs)

  fromList∘mapWith∈ : (f : ∀ {x} → x ∈ xs → B) → Vec B (length xs)
  fromList∘mapWith∈ f = subst (Vec B) (length-mapWith∈ f)
                      $ fromList (mapWith∈ xs f)

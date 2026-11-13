{-# OPTIONS --without-K #-}
module Test.Show where

open import Class.Prelude
open import Class.Show

private
  _ = Show String ∋ it
  _ = Show ⊤ ∋ it
  _ = Show Char ∋ it
  _ = Show Bool ∋ it
  _ = Show ℕ ∋ it
  _ = Show¹ Fin ∋ it
  _ = Show Float ∋ it

  open import Reflection
  open import Reflection.AST.Term
  open import Reflection.AST.Meta
  open import Reflection.AST.Argument.Relevance
  open import Reflection.AST.Argument.Visibility

  _ = Show Name ∋ it
  _ = Show Meta ∋ it
  _ = Show Relevance ∋ it
  _ = Show Visibility ∋ it
  _ = Show Literal ∋ it

  _ = Show (Args Term) ∋ it
  _ = Show Term ∋ it
  _ = Show Sort ∋ it
  _ = Show (Args Pattern) ∋ it
  _ = Show Pattern ∋ it
  _ = Show Clause ∋ it
  _ = Show (List Clause) ∋ it
  _ = Show Telescope ∋ it
  _ = Show Definition ∋ it

  _ = Show (Arg Name) ∋ it
  _ = Show (Arg Term) ∋ it
  _ = Show (Args Name) ∋ it

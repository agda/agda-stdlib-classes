{-# OPTIONS --cubical-compatible #-}
module Class.Show.Instances where

open import Class.Prelude hiding (Type)
open import Data.String using (parens; braces; intersperse)
open import Class.Semigroup
open import Class.Show.Core

Show-× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
Show-× .show (x , y) = parens $ show x ◇ " , " ◇ show y

Show-Maybe : ⦃ Show A ⦄ → Show (Maybe A)
Show-Maybe .show nothing  = "nothing"
Show-Maybe .show (just x) = "just " ◇ show x

Show-List : ⦃ Show A ⦄ → Show (List A)
Show-List .show = braces ∘ intersperse ", " ∘ map show

instance
  Show-String = mkShow id

  Show-⊤ = Show ⊤ ∋ λ where .show tt → "tt"

  Show-Char = Show _ ∋ record {M}
    where import Data.Char as M

  Show-Bool = Show _ ∋ record {M}
    where import Data.Bool.Show as M

  Show-ℕ = Show _ ∋ record {M}
    where import Data.Nat.Show as M

  Show-ℤ = Show _ ∋ record {M}
    where import Data.Integer.Show as M

  Show-Fin : Show¹ Fin
  Show-Fin .show = ("# " ◇_) ∘ show ∘ toℕ
    where open import Data.Fin using (toℕ)

  Show-Float = Show _ ∋ record {M}
    where import Data.Float as M

open import Reflection
open import Reflection.AST.Term
open import Reflection.AST.Meta

instance
  Show-Name = mkShow showName
  Show-Meta = mkShow showMeta
  Show-Relevance = mkShow showRel -- showRelevance
  Show-Vis = mkShow showVisibility
  Show-Literal = mkShow showLiteral

Show-Arg : ⦃ Show A ⦄ → Show (Arg A)
Show-Arg .show (arg (arg-info v _) x) = show v ◇ show x

Show-Abs : ⦃ Show A ⦄ → Show (Abs A)
Show-Abs .show (abs s x) = "abs " ◇ show s ◇ " " ◇ show x

instance
  Show-Names = Show (Args Term) ∋ mkShow showTerms
  Show-Term = mkShow showTerm
  Show-Sort = mkShow showSort
  Show-Patterns = Show (Args Pattern) ∋ mkShow showPatterns
  Show-Pattern = mkShow showPattern
  Show-Clause = mkShow showClause
  Show-Clauses = Show (List Clause) ∋ mkShow showClauses
  Show-Tel = Show Telescope ∋ mkShow showTel
  Show-Definition = mkShow showDefinition

  Show-AName = Show (Arg Name) ∋ Show-Arg
  Show-AType = Show (Arg Type) ∋ Show-Arg
  Show-ATerms = Show (Args Name) ∋ Show-List

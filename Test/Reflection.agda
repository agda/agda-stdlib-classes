module Test.Reflection where

open import Reflection hiding (_>>=_)
open import Data.Nat using (zero)
open import Class.Monad

-- ** cross-level bind
_ : TC Set
_ = getType (quote zero) >>= unquoteTC

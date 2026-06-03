{-# OPTIONS --cubical-compatible #-}
module Class.Monad where

open import Class.Monad.Core public
open import Class.Monad.Instances public

-- ** do not export: breaks instance resolution in general
-- open import Class.Monad.Id public

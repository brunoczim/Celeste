module Data.Signed where

open import Data.Bit using (Bit)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

record Signed (size : ℕ) : Set where
  field
    bits : Vec Bit size


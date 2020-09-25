module Data.Int.Literal where

open import Data.Nat using (ℕ)
open import Level using (suc)

record Negative {a} (A : Set a) : Set (suc a) where
  field
    Constraint : ℕ → Set a
    fromNeg : (n : ℕ) → ⦃ Constraint n ⦄ → A

open Negative {{...}} public using (fromNeg)
{-# BUILTIN FROMNEG fromNeg #-}

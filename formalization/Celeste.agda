module Celeste where

open import Data.Nat using (ℕ; _⊔_; zero)
open import Data.String using (String)
open import Data.Vec using (Vec)

record Signed (size : ℕ) : Set where
  field
    bits : Vec Bit size

mutual
  data Type : ℕ → Set where
    string : Type zero
    int8 : Type zero
    uint8 : Type zero
    int16 : Type zero
    uint16 : Type zero
    int32 : Type zero
    uint32 : Type zero
    int64 : Type zero
    uint64 : Type zero
    int128 : Type zero
    uint128 : Type zero
    int-word : Type zero
    uint-word : Type zero
    float32 : Type zero
    float64 : Type zero
    _×_ : {m n : ℕ} → Type m → Type n → Type (m ⊔ n)
    _⇒_ : {m n : ℕ} → Type m → Type n → Type (m ⊔ n)

  data Expr : {n : ℕ} → Type n → Set where
    str-lit : String → Expr string


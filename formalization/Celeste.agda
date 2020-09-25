module Celeste where

open import Data.Nat using (ℕ; _⊔_; zero)
open import Data.String using (String)
open import Data.Vec using (Vec)
open import Data.Unsigned using (Unsigned)
open import Data.Signed using (Signed)
open import Data.Float using (Float)

private
  variable
    word-size : ℕ

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
    _⟶_ : {m n : ℕ} → Type m → Type n → Type (m ⊔ n)

  data Expr : {n : ℕ} → Type n → Set where
    str-lit : String → Expr string
    int8-lit : Signed 8 → Expr int8
    uint8-lit : Unsigned 8 → Expr uint8
    int16-lit : Signed 16 → Expr int16
    uint16-lit : Unsigned 16 → Expr uint16
    int32-lit : Signed 32 → Expr int32
    uint32-lit : Unsigned 32 → Expr uint32
    int64-lit : Signed 64 → Expr int64
    uint64-lit : Unsigned 64 → Expr uint64
    int128-lit : Signed 128 → Expr int128
    uint128-lit : Unsigned 128 → Expr uint128
    int-word-lit : Signed word-size → Expr int-word
    uint-word-lit : Unsigned word-size → Expr uint-word
    float32-lit : Float → Expr float32
    float64-lit : Float → Expr float64

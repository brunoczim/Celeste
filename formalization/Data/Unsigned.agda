module Data.Unsigned where

open import Data.Bit using
  (Bit
  ; Bits-num
  ; Overflowing
  ; _overflow:_
  ; result
  ; carry
  ; toBool
  )
  renaming (_+_ to bit+; _-_ to bit-; ! to bit!)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; head)
open import Data.Nat.Literal using (Number)

record Unsigned (n : ℕ) : Set where
  constructor mk-uint
  field
    bits : Vec Bit n

open Unsigned public

instance
  Unsigned-num : {m : ℕ} → Number (Unsigned m)
  Unsigned-num {m} .Number.Constraint = Number.Constraint (Bits-num {m})
  Unsigned-num {m} .Number.fromNat n ⦃ p ⦄ = mk-uint (mk-bits p) where
    mk-bits : Number.Constraint (Bits-num {m}) n → Vec Bit m
    mk-bits p = Number.fromNat Bits-num n ⦃ p ⦄

_+_ : {n : ℕ} → Unsigned n → Unsigned n → Overflowing (Unsigned n)
p + q = mk-uint (result sum) overflow: toBool (head (carry sum)) where
  sum = bit+ (bits p) (bits q)

_-_ : {n : ℕ} → Unsigned n → Unsigned n → Overflowing (Unsigned n)
p - q = mk-uint (result sub) overflow: toBool (bit! (head (carry sub))) where
  sub = bit- (bits p) (bits q)

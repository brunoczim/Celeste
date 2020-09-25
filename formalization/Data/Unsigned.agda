module Data.Unsigned where

open import Data.Bit using
  (Bit
  ; b0
  ; b1
  ; Bits-num
  ; Overflowing
  ; _overflow:_
  ; result
  ; carry
  ; WithCarry
  ; _with-carry:_
  ; toBool
  ; tryToFinₙ
  ; !ₙ
  ) renaming
  ( _+_ to bit+
  ; _-_ to bit-
  ; ! to bit!
  ; _&_ to bit&
  ; _~|_ to bit|
  ; _^_ to bit^
  ; _>>_ to bit>>
  ; _<<_ to bit<<
  )
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; head; replicate)
open import Data.Nat.Literal using (Number)
open import Data.Maybe using (just; nothing)

infixl 8 _-_ _+_
infixl 7 _<<_ _>>_
infixl 6 _&_
infixl 5 _^_
infixl 4 _~|_

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

rotr : {n : ℕ} → Unsigned n → Unsigned n → WithCarry (Unsigned n) (Unsigned n)
rotr {n} (mk-uint ps) (mk-uint qs) = new-result with-carry: new-carry where
  shifted : WithCarry (Vec Bit n) (Vec Bit n)
  shifted with tryToFinₙ qs
  ...        | just i  = bit>> ps i
  ...        | nothing = replicate b0 with-carry: ps 
  new-result : Unsigned n
  new-result = mk-uint (result shifted)
  new-carry : Unsigned n
  new-carry = mk-uint (carry shifted)

rotl : {n : ℕ} → Unsigned n → Unsigned n → WithCarry (Unsigned n) (Unsigned n)
rotl {n} (mk-uint ps) (mk-uint qs) = new-result with-carry: new-carry where
  shifted : WithCarry (Vec Bit n) (Vec Bit n)
  shifted with tryToFinₙ qs
  ...        | just i  = bit<< ps i
  ...        | nothing = replicate b0 with-carry: ps
  new-result : Unsigned n
  new-result = mk-uint (result shifted)
  new-carry : Unsigned n
  new-carry = mk-uint (carry shifted)

_>>_ : {n : ℕ} → Unsigned n → Unsigned n → Unsigned n
ps >> qs = result (rotr ps qs)

_<<_ : {n : ℕ} → Unsigned n → Unsigned n → Unsigned n
ps << qs = result (rotl ps qs)

! : {n : ℕ} → Unsigned n → Unsigned n
! (mk-uint ps) = mk-uint (!ₙ ps)

_&_ : {n : ℕ} → Unsigned n → Unsigned n → Unsigned n
(mk-uint ps) & (mk-uint qs) = mk-uint (bit& ps qs)

_~|_ : {n : ℕ} → Unsigned n → Unsigned n → Unsigned n
(mk-uint ps) ~| (mk-uint qs) = mk-uint (bit| ps qs)

_^_ : {n : ℕ} → Unsigned n → Unsigned n → Unsigned n
(mk-uint ps) ^ (mk-uint qs) = mk-uint (bit^ ps qs)

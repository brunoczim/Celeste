module Data.Signed where

open import Data.Bit using
  (Bit
  ; b0
  ; b1
  ; Bits-num
  ; Bits-neg
  ; Overflowing
  ; _overflow:_
  ; result
  ; carry
  ; WithCarry
  ; _with-carry:_
  ; toBool
  ; tryToFinₙ
  ; !ₙ
  ; _⊕_
  ; _↔_
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
open import Data.Nat using (ℕ; suc; zero) renaming (_≤_ to ℕ≤)
open import Data.Vec using (Vec; _∷_; []; head; tail; replicate)
open import Data.Nat.Literal using (Number)
open import Data.Int.Literal using (Negative)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥)

infixl 8 _-_ _+_
infixl 7 _<<_ _>>_
infixl 6 _&_
infixl 5 _^_
infixl 4 _~|_

record Signed (n : ℕ) : Set where
  constructor mk-int
  field
    bits : Vec Bit n

open Signed public

instance
  Signed-num : {m : ℕ} → Number (Signed m)
  Signed-num {zero} .Number.Constraint = Number.Constraint (Bits-num {zero})
  Signed-num {suc m} .Number.Constraint = Number.Constraint (Bits-num {m})
  Signed-num {zero} .Number.fromNat zero ⦃ p ⦄ = mk-int [] where
  Signed-num {zero} .Number.fromNat (suc _) ⦃ ℕ≤.s≤s () ⦄
  Signed-num {suc m} .Number.fromNat n ⦃ p ⦄ = mk-int (mk-bits p) where
    mk-bits : Number.Constraint (Bits-num {m}) n → Vec Bit (suc m)
    mk-bits p = b0 ∷ Number.fromNat Bits-num n ⦃ p ⦄

instance
  Signed-neg : {m : ℕ} → Negative (Signed (suc m))
  Signed-neg {m} .Negative.Constraint = Negative.Constraint (Bits-neg {m})
  Signed-neg {m} .Negative.fromNeg n ⦃ p ⦄ = mk-int bitVec where
    bitVec : Vec Bit (suc m)
    bitVec = Negative.fromNeg (Bits-neg {m}) n ⦃ p ⦄

_+_ : {n : ℕ} → Signed n → Signed n → Overflowing (Signed n)
p + q = mk-int (result sum) overflow: toBool overflow where
  sum = bit+ (bits p) (bits q)
  last-carry : {n : ℕ} → Vec Bit n → Bit
  last-carry [] = b0
  last-carry (b ∷ _) = b
  overflow = head (carry sum) ⊕ last-carry (tail (carry sum))

_-_ : {n : ℕ} → Signed n → Signed n → Overflowing (Signed n)
p - q = mk-int (result sub) overflow: toBool overflow where
  sub = bit- (bits p) (bits q)
  last-carry : {n : ℕ} → Vec Bit n → Bit
  last-carry [] = b0
  last-carry (b ∷ _) = b
  overflow = head (carry sub) ↔ last-carry (tail (carry sub))

rotr : {n : ℕ} → Signed n → Signed n → WithCarry (Signed n) (Signed n)
rotr {n} (mk-int ps) (mk-int qs) = new-result with-carry: new-carry where
  shifted : WithCarry (Vec Bit n) (Vec Bit n)
  shifted with tryToFinₙ qs
  ...        | just i  = bit>> ps i
  ...        | nothing = replicate b0 with-carry: ps 
  new-result : Signed n
  new-result = mk-int (result shifted)
  new-carry : Signed n
  new-carry = mk-int (carry shifted)

rotl : {n : ℕ} → Signed n → Signed n → WithCarry (Signed n) (Signed n)
rotl {n} (mk-int ps) (mk-int qs) = new-result with-carry: new-carry where
  shifted : WithCarry (Vec Bit n) (Vec Bit n)
  shifted with tryToFinₙ qs
  ...        | just i  = bit<< ps i
  ...        | nothing = replicate b0 with-carry: ps
  new-result : Signed n
  new-result = mk-int (result shifted)
  new-carry : Signed n
  new-carry = mk-int (carry shifted)

_>>_ : {n : ℕ} → Signed n → Signed n → Signed n
ps >> qs = result (rotr ps qs)

_<<_ : {n : ℕ} → Signed n → Signed n → Signed n
ps << qs = result (rotl ps qs)

arotr : {n : ℕ} → Signed n → Signed n → WithCarry (Signed n) (Signed n)
arotr {n} (mk-int []) _ = mk-int [] with-carry: mk-int []
arotr {suc n} (mk-int (p ∷ ps)) (mk-int qs) = new-result with-carry: new-carry
  where
    shifted : WithCarry (Vec Bit n) (Vec Bit n)
    shifted with tryToFinₙ qs
    ...        | just i  = bit>> ps i
    ...        | nothing = replicate b0 with-carry: ps
    new-result : Signed (suc n)
    new-result = mk-int (p ∷ result shifted)
    new-carry : Signed (suc n)
    new-carry = mk-int (b0 ∷ carry shifted)

arotl : {n : ℕ} → Signed n → Signed n → WithCarry (Signed n) (Signed n)
arotl {n} (mk-int []) _ = mk-int [] with-carry: mk-int []
arotl {suc n} (mk-int (p ∷ ps)) (mk-int qs) = new-result with-carry: new-carry
  where
    shifted : WithCarry (Vec Bit n) (Vec Bit n)
    shifted with tryToFinₙ qs
    ...        | just i  = bit<< ps i
    ...        | nothing = replicate b0 with-carry: ps
    new-result : Signed (suc n)
    new-result = mk-int (p ∷ result shifted)
    new-carry : Signed (suc n)
    new-carry = mk-int (b0 ∷ carry shifted)

_a>>_ : {n : ℕ} → Signed n → Signed n → Signed n
ps a>> qs = result (rotr ps qs)

_a<<_ : {n : ℕ} → Signed n → Signed n → Signed n
ps a<< qs = result (rotl ps qs)

! : {n : ℕ} → Signed n → Signed n
! (mk-int ps) = mk-int (!ₙ ps)

_&_ : {n : ℕ} → Signed n → Signed n → Signed n
(mk-int ps) & (mk-int qs) = mk-int (bit& ps qs)

_~|_ : {n : ℕ} → Signed n → Signed n → Signed n
(mk-int ps) ~| (mk-int qs) = mk-int (bit| ps qs)

_^_ : {n : ℕ} → Signed n → Signed n → Signed n
(mk-int ps) ^ (mk-int qs) = mk-int (bit^ ps qs)

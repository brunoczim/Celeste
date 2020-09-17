module Data.Bit where

open import Data.Nat.Literal using (Number; ℕ-num; Fin-num)
open import Data.Nat using (ℕ ; suc; zero; ⌊_/2⌋)
                     renaming (_*_ to ℕ*; _+_ to ℕ+; _≤_ to ℕ≤; _^_ to ℕ^)
open import Data.Fin using (Fin; suc; zero; raise)
                     renaming (toℕ to finToℕ; fromℕ to finFromℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _++_; map; replicate; insert)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Level using (_⊔_)
open import Data.Bool using (Bool; false; true)

record WithCarry {a} {c} (A : Set a) (C : Set c) : Set (a ⊔ c) where
  constructor _with-carry:_
  field
    result : A
    carry : C

open WithCarry public

record Overflowing {a} (A : Set a) : Set a where
  constructor _overflow:_
  field
    result : A
    overflow : Bool

open Overflowing public

data Bit : Set where
  b0 : Bit
  b1 : Bit

infixl 8 _-_ _+_
infixl 7 _<<_ _>>_
infixl 6 _∧_ _&_
infixl 5 _⊕_ _^_
infixl 4 _∨_ _~|_
infixl 1 _with-carry:_

fromBool : Bool → Bit
fromBool false = b0
fromBool true = b1

toBool : Bit → Bool
toBool b0 = false
toBool b1 = true

! : Bit → Bit
! b0 = b1
! b1 = b0

_∧_ : Bit → Bit → Bit
b0 ∧ _ = b0
b1 ∧ q = q

_∨_ : Bit → Bit → Bit
b0 ∨ q = q
b1 ∨ _ = b1


_⊕_ : Bit → Bit → Bit
b0 ⊕ q = q
b1 ⊕ q = ! q

maj3 : Bit → Bit → Bit → Bit
maj3 p q r = p ∧ q ∨ p ∧ r ∨ q ∧ r

half-add : Bit → Bit → WithCarry Bit Bit
half-add p q = p ⊕ q with-carry: p ∧ q

full-add : Bit → Bit → Bit → WithCarry Bit Bit
full-add p q r = p ⊕ q ⊕ r with-carry: maj3 p q r

full-addₙ : {n : ℕ} →
            Vec Bit n →
            Vec Bit n →
            Bit →
            WithCarry (Vec Bit n) (Vec Bit 2)
full-addₙ [] [] r = [] with-carry: b0 ∷ r ∷ []
full-addₙ (p ∷ []) (q ∷ []) r = result s ∷ [] with-carry: r ∷ carry s ∷ [] where
  s = full-add p q r
full-addₙ (p ∷ ps) (q ∷ qs) r = result s ∷ result ss with-carry: carry ss  where
  s = full-add p q r
  ss = full-addₙ ps qs (carry s)

!ₙ : {n : ℕ} → Vec Bit n → Vec Bit n
!ₙ = map !

_+_ : {n : ℕ} → Vec Bit n → Vec Bit n → WithCarry (Vec Bit n) (Vec Bit 2)
ps + qs = full-addₙ ps qs b0

_-_ : {n : ℕ} → Vec Bit n → Vec Bit n → WithCarry (Vec Bit n) (Vec Bit 2)
ps - qs = full-addₙ ps (!ₙ qs) b1

inc : {n : ℕ} → Vec Bit n → WithCarry (Vec Bit n) (Vec Bit 2)
inc ps = full-addₙ ps (replicate b0) b1

dec : {n : ℕ} → Vec Bit n → WithCarry (Vec Bit n) (Vec Bit 2)
dec ps = full-addₙ ps (replicate b1) b0

_>>_ : {m : ℕ} → Vec Bit m → Fin m → WithCarry (Vec Bit m) (Vec Bit m)
ps >> zero = ps with-carry: replicate b0
_>>_ {suc m} (p ∷ ps) (suc i) = new-result with-carry: new-carry
  where
    qs : WithCarry (Vec Bit m) (Vec Bit m)
    qs = ps >> i
    new-result : Vec Bit (suc m)
    new-result = insert (result qs) (finFromℕ m) b0
    new-carry : Vec Bit (suc m)
    new-carry = insert (result qs) (finFromℕ m) p

_<<_ : {m : ℕ} → Vec Bit m → Fin m → WithCarry (Vec Bit m) (Vec Bit m)
_<<_ {m} ps i = proj₂ (do-shift ps) where
  do-shift : {n : ℕ} → Vec Bit n → Fin m × WithCarry (Vec Bit n) (Vec Bit n)
  do-shift [] = i , ([] with-carry: [])
  do-shift {suc n} (p ∷ ps) = ret (proj₁ pair) where
    pair : Fin m × WithCarry (Vec Bit n) (Vec Bit n)
    pair = do-shift ps
    qs : WithCarry (Vec Bit n) (Vec Bit n)
    qs = proj₂ pair
    ret : Fin m → Fin m × WithCarry (Vec Bit (suc n)) (Vec Bit (suc n))
    ret zero = zero , (b0 ∷ result qs with-carry: p ∷ carry qs)
    ret (suc j) = raise 1 j , (p ∷ result qs with-carry: b0 ∷ carry qs)

_&_ : {n : ℕ} → Vec Bit n → Vec Bit n → Vec Bit n
[] & [] = []
(p ∷ ps) & (q ∷ qs) = p ∧ q ∷ ps & qs

_~|_ : {n : ℕ} → Vec Bit n → Vec Bit n → Vec Bit n
[] ~| [] = []
(p ∷ ps) ~| (q ∷ qs) = (p ∨ q) ∷ (ps ~| qs)

_^_ : {n : ℕ} → Vec Bit n → Vec Bit n → Vec Bit n
[] ^ [] = []
(p ∷ ps) ^ (q ∷ qs) = (p ⊕ q) ∷ (ps ^ qs)

toℕ : Bit → ℕ
toℕ b0 = 0
toℕ b1 = 1

toFin : {n : ℕ} → Bit → Fin (suc (suc n))
toFin b0 = 0
toFin b1 = 1

toℕₙ : {n : ℕ} → Vec Bit n → ℕ
toℕₙ [] = 0
toℕₙ (p ∷ ps) = ℕ+ (toℕ p) (ℕ* 2 (toℕₙ ps))

ℕ-mod2 : ℕ → Bit
ℕ-mod2 zero = b0
ℕ-mod2 (suc zero) = b1
ℕ-mod2 (suc (suc n)) = ℕ-mod2 n

instance
  Bit-num : Number Bit
  Bit-num .Number.Constraint n = constrain n where
    constrain : ℕ → Set
    constrain zero = ⊤
    constrain (suc zero) = ⊤
    constrain  _ = ⊥
  Bit-num .Number.fromNat n ⦃ p ⦄ = fromNat n p where
    fromNat : (m : ℕ) → (Number.Constraint Bit-num) m → Bit
    fromNat zero _ = b0
    fromNat (suc zero) _ = b1
    fromNat (suc (suc _)) ()

instance
  Bits-num : {m : ℕ} → Number (Vec Bit m)
  Bits-num {m} .Number.Constraint n = ℕ≤ (suc n) (ℕ^ 2 m)
  Bits-num {m} .Number.fromNat n  = fromNat m n where
    fromNat : (m : ℕ) → ℕ → Vec Bit m
    fromNat zero _ = []
    fromNat (suc m) n = ℕ-mod2 n ∷ fromNat m ⌊ n /2⌋
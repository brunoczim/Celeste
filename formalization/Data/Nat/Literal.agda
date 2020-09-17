module Data.Nat.Literal where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Agda.Builtin.FromNat using (Number; fromNat) public

_≤_ : ℕ → ℕ → Set
zero  ≤ n     = ⊤
suc m ≤ zero  = ⊥
suc m ≤ suc n = m ≤ n

instance
  ℕ-num : Number ℕ
  ℕ-num .Number.Constraint _ = ⊤
  ℕ-num .Number.fromNat n = n

instance
  Fin-num : {n : ℕ} → Number (Fin (suc n))
  Fin-num {n} .Number.Constraint m = m ≤ n
  Fin-num {n} .Number.fromNat m ⦃ p ⦄ = from m n p where
    from : (m n : ℕ) → m ≤ n → Fin (suc n)
    from zero _ _ = zero
    from (suc _) zero ()
    from (suc m) (suc n) p = suc (from m n p)

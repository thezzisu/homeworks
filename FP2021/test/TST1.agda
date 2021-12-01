module TST1 where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

+-cong : {n m : ℕ} → n + m ≡ m + n
+-cong {zero} {zero} = refl
+-cong {zero} {suc m} = cong suc (+-cong {zero} {m})
+-cong {suc n} {zero} = cong suc (+-cong {n} {zero})
+-cong {suc n} {suc m} = ?
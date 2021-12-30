module TST6 where

open import Data.Nat using (ℕ; _*_; _+_)

data Square : ℕ → Set where
  sqr : (n : ℕ) → Square (n * n)


root : (n : ℕ)(sq : Square n) → ℕ
root n (sqr m) = m

add : (a b c : ℕ) → ℕ
add a c b = a + b

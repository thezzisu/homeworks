module HW13 where

module problem-1 where

  open import Data.Nat using (ℕ; suc; zero)
  open import Data.Bool using (Bool; true; false)

  _<_ : ℕ → ℕ → Bool
  zero < zero = false
  zero < suc n = true
  suc n < zero = false
  suc n < suc m = n < m

module problem-2 where

  open import Data.List using (List; []; _∷_)
  open import Data.Bool using (Bool; true; false)

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else y = x
  if false then x else y = y

  filter : {A : Set} → ((x : A) → Bool) → List A → List A
  filter f [] = []
  filter f (x ∷ xs) = if f x then x ∷ filter f xs else filter f xs

module problem-3 where

  open import Data.Nat using (ℕ; suc; zero)
  open import Data.Vec using (Vec; []; _∷_)

  Matrix : Set → ℕ → ℕ → Set
  Matrix A n m = Vec (Vec A n) m

  vmap : {A B : Set}{n : ℕ} → ((x : A) → B) → Vec A n → Vec B n
  vmap f [] = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

  lappend : {A : Set}{n m : ℕ} → Vec A m -> Matrix A n m -> Matrix A (suc n) m
  lappend [] [] = []
  lappend (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ lappend xs ys

  cvt : {A : Set}{n : ℕ} → Vec A n → Matrix A 1 n
  cvt [] = []
  cvt (x ∷ xs) = (x ∷ []) ∷ cvt xs

  transpose
    : {A : Set}
      {n m : ℕ}
    → Matrix A n m
      ------------
    → Matrix A m n
  -- transpose [] = []
  transpose (v ∷ []) = cvt v
  transpose (v ∷ mat) = lappend v (transpose mat)

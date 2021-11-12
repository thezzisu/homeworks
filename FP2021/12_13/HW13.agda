module HW13 where

data Bool : Set where
  true  : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixr 40 _::_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

module problem-1 where
  _<_ : ℕ → ℕ → Bool
  zero < zero = false
  zero < suc n = true
  suc n < zero = false
  suc n < suc m = n < m

module problem-2 where
  filter : {A : Set} → ((x : A) → Bool) → List A → List A
  filter f [] = []
  filter f (x ∷ xs) = if f x then x ∷ filter f xs else filter f xs

module problem-3 where
  Matrix : Set → ℕ → ℕ → Set
  Matrix A n m = Vec (Vec A n) m

  vmap : {A B : Set}{n : ℕ} → ((x : A) → B) → Vec A n → Vec B n
  vmap f [] = []
  vmap f (x ∷ xs) = f x ∷ vmap f xs

  lappend : {A : Set}{n m : ℕ} → Vec A m → Matrix A n m → Matrix A (suc n) m
  lappend [] [] = []
  lappend (x ∷ xs) (y ∷ ys) = (x ∷ y) ∷ lappend xs ys

  cvt : {A : Set}{n : ℕ} → Vec A n → Matrix A (suc zero) n
  cvt [] = []
  cvt (x ∷ xs) = (x ∷ []) ∷ cvt xs

  fill : {A : Set} → (n : ℕ) → A → Vec A n
  fill zero x = []
  fill (suc n) x = x ∷ fill n x

  transpose
    : {A : Set}
      {n m : ℕ}
    → Matrix A n m
      ------------
    → Matrix A m n
  transpose [] = fill _ []
  transpose (v ∷ []) = cvt v
  transpose (v ∷ mat) = lappend v (transpose mat)

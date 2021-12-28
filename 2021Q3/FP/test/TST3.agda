module TST3 where

open import Data.Nat using (ℕ; _*_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Relation.Nullary using (¬_)

open import Data.List using (List; []; _∷_)

infixr 5 _++_

_++_ : ∀{A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

foldr : ∀{A B : Set} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀{A B : Set} → (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

concat : ∀{A : Set} → List (List A) → List A
concat = foldr _++_ []

map : ∀{A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

scanr : ∀{A B : Set} → (A → B → B) → B → List A → List B
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : ∀{A B : Set} → (A → B → A) → A → List B → List A
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

inits : ∀{A : Set} → List A → List (List A)
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (x ∷_) (inits xs)

tails : ∀{A : Set} → List A → List (List A)
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs
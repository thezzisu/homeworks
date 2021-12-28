module HW15 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.List using (List; []; _∷_; _++_; foldr)

module problem-1 where

  ++-assoc : ∀ {A : Set}
      (xs ys zs : List A)
      -----------------------------------
    → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

  -- tips: to input the superscript l (ˡ), type \^l and use your
  --       arrow keys to select it (should be the fourth candidate).
  ++-identityˡ : ∀ {A : Set}
      (xs : List A)
      -------------
    → [] ++ xs ≡ xs
  ++-identityˡ xs = refl

  -- you might have already guessed it: type \^r for superscript r (ʳ)
  -- again, use your arrow keys to select it (the fourth candidate). 
  ++-identityʳ : ∀ {A : Set}
      (xs : List A)
    → xs ++ [] ≡ xs
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

module problem-2 where

  -- tips: to input ⊗, type \otimes
  foldr-++ : ∀ {A : Set}
      (_⊗_ : A → A → A)
      (e : A)
      (xs ys : List A)
      -----------------------------
    → foldr _⊗_ e (xs ++ ys)
    ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
  foldr-++ _⊗_ e [] ys =
    begin
      foldr _⊗_ e ([] ++ ys)
    ≡⟨⟩
      foldr _⊗_ e ys
    ≡⟨⟩
      foldr _⊗_ (foldr _⊗_ e ys) []
    ∎
  foldr-++ _⊗_ e (x ∷ xs) ys =
    begin
      foldr _⊗_ e ((x ∷ xs) ++ ys)
    ≡⟨⟩
      x ⊗ (foldr _⊗_ e (xs ++ ys))
    ≡⟨ cong (x ⊗_) (foldr-++ _⊗_ e xs ys) ⟩
      x ⊗ (foldr _⊗_ (foldr _⊗_ e ys) xs)
    ≡⟨⟩
      foldr _⊗_ (foldr _⊗_ e ys) (x ∷ xs)
    ∎

module problem-3 (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Function using (id; _∘_)

  reverse : ∀ {A : Set} → List A → List A
  reverse []       = []
  reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

  -- hint: you might want to introduce an extra lemma to prove this.
reverse-involutive : ∀ {A : Set} → reverse {A} ∘ reverse {A} ≡ id
reverse-involutive {A} = extensionality lemma
  where
    reverse-tail : (x : A) → (xs : List A) → reverse (xs ++ (x ∷ [])) ≡ x ∷ reverse xs
    reverse-tail x [] = refl
    reverse-tail x (x₁ ∷ xs) = cong (_++ (x₁ ∷ [])) (reverse-tail x xs)
    lemma : (xs : List A) → (reverse ∘ reverse) xs ≡ id xs
    lemma [] = refl
    lemma (x ∷ xs) =
      begin
        reverse ((reverse xs) ++ (x ∷ []))
      ≡⟨ reverse-tail x (reverse xs) ⟩
        x ∷ ((reverse ∘ reverse) xs)
      ≡⟨ cong (x ∷_) (lemma xs) ⟩
        x ∷ xs
      ∎

  -- bonus: fast-reverse-involutive
  -- this is only for practice, not part of the homework this week

  fast-reverse : ∀ {A : Set} → List A → List A
  fast-reverse = helper []
    module FastReverse where
    helper : ∀ {A : Set} → List A → List A → List A
    helper res []       = res
    helper res (x ∷ xs) = helper (x ∷ res) xs

  open FastReverse using (helper)
  open problem-1 using (++-assoc; ++-identityʳ)

  fast-reverse≡reverse : ∀ {A : Set} → fast-reverse {A} ≡ reverse {A}
  fast-reverse≡reverse {A} = extensionality lemma
    where
      actual-helper : (xs ys : List A) → helper {A} xs ys ≡ (reverse ys) ++ xs
      actual-helper xs [] = refl
      actual-helper xs (y ∷ ys) = begin
          helper {A} xs (y ∷ ys)
        ≡⟨⟩
          helper {A} (y ∷ xs) ys
        ≡⟨ actual-helper (y ∷ xs) ys ⟩
          (reverse ys) ++ (y ∷ xs)
        ≡⟨ cong ((reverse ys) ++_) refl ⟩
          (reverse ys) ++ ((y ∷ []) ++ xs)
        ≡⟨ sym (++-assoc (reverse ys) (y ∷ []) xs) ⟩
          ((reverse ys) ++ (y ∷ [])) ++ xs
        ≡⟨ cong (_++ xs) refl ⟩
          (reverse (y ∷ ys)) ++ xs
        ∎

      lemma : (xs : List A) → fast-reverse xs ≡ reverse xs
      lemma xs = begin
          fast-reverse xs
        ≡⟨⟩
          helper {A} [] xs
        ≡⟨ actual-helper [] xs ⟩
          (reverse xs) ++ []
        ≡⟨ ++-identityʳ (reverse xs) ⟩
          reverse xs
        ∎

  fast-reverse-involutive : ∀ {A : Set}
    → fast-reverse {A} ∘ fast-reverse {A} ≡ id
  fast-reverse-involutive {A} = extensionality lemma
    where
      lemma : (xs : List A) → (fast-reverse ∘ fast-reverse) xs ≡ id xs
      lemma xs = begin
          (fast-reverse ∘ fast-reverse) xs
        ≡⟨⟩
         fast-reverse (fast-reverse xs)
        ≡⟨ cong fast-reverse (cong-app fast-reverse≡reverse xs) ⟩
          fast-reverse (reverse xs)
        ≡⟨ cong-app fast-reverse≡reverse (reverse xs) ⟩
          reverse (reverse xs)
        ≡⟨ cong-app reverse-involutive xs ⟩
          id xs
        ∎

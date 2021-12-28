module TST4 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function using (_∘_)

module semigroup where
  record IsSemigroup {A : Set} (_⊕_ : A → A → A) : Set where
    field assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)

  open IsSemigroup public

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-assoc)
  ℕ-add-is-semigroup : IsSemigroup _+_
  ℕ-add-is-semigroup .assoc = +-assoc

  open import Data.Nat using (_⊔_)
  open import Data.Nat.Properties using (⊔-assoc)
  ℕ-⊔-is-semigroup : IsSemigroup _⊔_
  ℕ-⊔-is-semigroup .assoc = ⊔-assoc

  open import Data.List using (List; _++_; [])
  open import Data.List.Properties using (++-assoc)
  List-++-is-semigroup : ∀ {A : Set} → IsSemigroup {List A} _++_
  List-++-is-semigroup .assoc = ++-assoc

open semigroup

module monoid where
  record IsMonoid {A : Set} (e : A) (_⊕_ : A → A → A) : Set where
    field
      is-semigroup : IsSemigroup _⊕_
      identityˡ : ∀ x → e ⊕ x ≡ x
      identityʳ : ∀ x → x ⊕ e ≡ x

  open IsMonoid public

  open import Data.Nat using (_+_)
  open import Data.Nat.Properties using (+-identityˡ; +-identityʳ)
  ℕ-add-is-monoid : IsMonoid 0 _+_
  ℕ-add-is-monoid .is-semigroup = ℕ-add-is-semigroup
  ℕ-add-is-monoid .identityˡ = +-identityˡ
  ℕ-add-is-monoid .identityʳ = +-identityʳ

  open import Data.Nat using (_⊔_)
  open import Data.Nat.Properties using (⊔-identityˡ; ⊔-identityʳ)
  ℕ-⊔-is-monoid : IsMonoid 0 _⊔_
  ℕ-⊔-is-monoid .is-semigroup = ℕ-⊔-is-semigroup
  ℕ-⊔-is-monoid .identityˡ = ⊔-identityˡ
  ℕ-⊔-is-monoid .identityʳ = ⊔-identityʳ

  open import Data.List using (List; _++_; [])
  open import Data.List.Properties using (++-identityˡ; ++-identityʳ)
  List-++-is-monoid : ∀ {A : Set} → IsMonoid {List A} [] _++_
  List-++-is-monoid .is-semigroup = List-++-is-semigroup
  List-++-is-monoid .identityˡ = ++-identityˡ
  List-++-is-monoid .identityʳ = ++-identityʳ

open monoid

module FUCK (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Data.Nat using (ℕ; _+_; zero; suc; _⊔_)
  open import Data.List using (List; []; _∷_; [_]; _++_; foldl; foldr; map; scanl; scanr; inits; tails)
  open import Data.Nat.Properties using (+-identityʳ; ⊔-identityʳ; +-assoc; +-identityˡ; +-comm; ⊔-comm)

  reduce : ∀{A : Set} → (_⊕_ : A → A → A) → (e : A) → IsMonoid e _⊕_ → List A → A
  reduce _⊕_ e _ [] = e
  reduce _⊕_ e p (x ∷ xs) = x ⊕ reduce _⊕_ e p xs

  flatten : ∀ {A : Set} → List (List A) → List A
  flatten = reduce _++_ [] List-++-is-monoid

  map-distrib : ∀ {A B : Set} (f : A → B)(xs ys : List A)
    → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-distrib f [] ys = refl
  map-distrib f (x ∷ xs) ys = cong (f x ∷_) (map-distrib f xs ys)

  map-compose : ∀{A B C : Set} (f : B → C)(g : A → B)
    → map f ∘ map g ≡ map (f ∘ g)
  map-compose {A} f g = extensionality lemma
    where
      lemma : (xs : List A) → (map f ∘ map g) xs ≡ map (f ∘ g) xs
      lemma [] = refl
      lemma (x ∷ xs) = cong (f (g x) ∷_) (lemma xs)

  map-promotion : ∀{A B : Set} (f : A → B)
    → map f ∘ flatten ≡ flatten ∘ map (map f)
  map-promotion {A} {B} f = extensionality lemma
    where
      lemma : (xss : List (List A)) → (map f ∘ flatten) xss ≡ (flatten ∘ map (map f)) xss
      lemma [] = refl
      lemma (xs ∷ xss) = trans (map-distrib f xs (flatten xss)) (cong (map f xs ++_) (lemma xss))

  reduce-commute : ∀{A : Set} (_⊕_ : A → A → A)(e : A)(p : IsMonoid e _⊕_)(xs ys : List A)
    → reduce _⊕_ e p (xs ++ ys) ≡ reduce _⊕_ e p xs ⊕ reduce _⊕_ e p ys
  reduce-commute _⊕_ e p [] ys = sym (IsMonoid.identityˡ p (reduce _⊕_ e p ys))
  reduce-commute _⊕_ e p (x ∷ xs) ys =
    begin
      x ⊕ reduce _⊕_ e p (xs ++ ys)
    ≡⟨ cong (x ⊕_) (reduce-commute _⊕_ e p xs ys) ⟩
      x ⊕ (reduce _⊕_ e p xs ⊕ reduce _⊕_ e p ys)
    ≡⟨ sym (IsSemigroup.assoc (IsMonoid.is-semigroup p) x (reduce _⊕_ e p xs) (reduce _⊕_ e p ys))  ⟩
      reduce _⊕_ e p (x ∷ xs) ⊕ reduce _⊕_ e p ys
    ∎

  reduce-promotion : ∀{A : Set} (_⊕_ : A → A → A)(e : A)(p : IsMonoid e _⊕_)
    → reduce _⊕_ e p ∘ flatten ≡ reduce _⊕_ e p ∘ map (reduce _⊕_ e p)
  reduce-promotion {A} _⊕_ e p = extensionality lemma
    where
      lemma : (xss : List (List A))
        → (reduce _⊕_ e p ∘ flatten) xss ≡ (reduce _⊕_ e p ∘ map (reduce _⊕_ e p)) xss
      lemma [] = refl
      lemma (xs ∷ xss) =
        begin
          reduce _⊕_ e p (xs ++ flatten xss)
        ≡⟨ reduce-commute _⊕_ e p xs (flatten xss) ⟩
          reduce _⊕_ e p xs ⊕ reduce _⊕_ e p (flatten xss)
        ≡⟨ cong (reduce _⊕_ e p xs ⊕_) (lemma xss) ⟩
          reduce _⊕_ e p (map (reduce _⊕_ e p) (xs ∷ xss))
        ∎

  foldl-extendʳ : ∀{A : Set}(_⊕_ : A → A → A)(e : A)(xs : List A)(x : A)
    → foldl _⊕_ e xs ⊕ x ≡ foldl _⊕_ e (xs ++ [ x ])
  foldl-extendʳ _⊕_ e [] x = refl
  foldl-extendʳ _⊕_ e (x₁ ∷ xs) x =
    begin
      foldl _⊕_ (e ⊕ x₁) xs ⊕ x
    ≡⟨ foldl-extendʳ _⊕_ (e ⊕ x₁) xs x ⟩
      foldl _⊕_ (e ⊕ x₁) (xs ++ [ x ])
    ∎

  acc-lemma : ∀{A : Set} (_⊕_ : A → A → A) (e : A) → scanl _⊕_ e ≡ map (foldl _⊕_ e) ∘ inits
  acc-lemma {A} _⊕_ e = extensionality (lemma e [] init-proof)
    where
      init-proof : e ≡ foldl _⊕_ e []
      init-proof = refl

      next-proof : (acc : A)(head : List A)(x : A)
        → acc ≡ foldl _⊕_ e head
        → acc ⊕ x ≡ foldl _⊕_ e (head ++ [ x ])
      next-proof acc head x p = trans (cong (_⊕ x) p) (foldl-extendʳ _⊕_ e head x)

      lemma : (acc : A)(head : List A)(p : acc ≡ foldl _⊕_ e head)
        → (xs : List A)
        → scanl _⊕_ acc xs ≡ (map (foldl _⊕_ acc) ∘ inits) xs
      lemma acc head p [] = refl
      lemma acc head p (x ∷ xs) =
        begin
          acc ∷ scanl _⊕_ (acc ⊕ x) xs
        ≡⟨ cong (acc ∷_) (
          begin
            scanl _⊕_ (acc ⊕ x) xs
          ≡⟨ lemma (acc ⊕ x) (head ++ [ x ]) (next-proof acc head x p) xs ⟩
            map (foldl _⊕_ (acc ⊕ x)) (inits xs)
          ≡⟨⟩
            map ((foldl _⊕_ acc) ∘ (x ∷_)) (inits xs)
          ≡⟨ cong-app (sym (map-compose (foldl _⊕_ acc) (x ∷_))) (inits xs) ⟩
            (map (foldl _⊕_ acc) ∘ map (x ∷_)) (inits xs)
          ∎
        ) ⟩
          acc ∷ (map (foldl _⊕_ acc) ∘ map (x ∷_)) (inits xs)
        ∎

  ∘-assoc : ∀{l l′ l′′ l′′′}{A : Set l}{B : Set l′}{C : Set l′′}{D : Set l′′′}(f : C → D)(g : B → C)(h : A → B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  ∘-assoc f g h = refl

  R-Dist : ∀{A : Set} (_⊕_ : A → A → A)(_⊗_ : A → A → A) → Set
  R-Dist {A} _⊕_ _⊗_ = ∀ (a b c : A) → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊗ c)

  reduce-R-Dist : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)(_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_)
    → (rdist : R-Dist _⊕_ _⊗_)
    → (x x₁ : A)(xs : List A)
    → reduce _⊕_ e-⊕ p (map (_⊗ x) (x₁ ∷ xs)) ≡ reduce _⊕_ e-⊕ p (x₁ ∷ xs) ⊗ x
  reduce-R-Dist {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x x₁ [] =
    begin
      (x₁ ⊗ x) ⊕ e-⊕
    ≡⟨ IsMonoid.identityʳ p (x₁ ⊗ x) ⟩
      x₁ ⊗ x
    ≡⟨ cong (_⊗ x) (sym (IsMonoid.identityʳ p x₁)) ⟩
      (x₁ ⊕ e-⊕) ⊗ x
    ∎
  reduce-R-Dist {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x x₁ xa@(x₂ ∷ xs) =
    begin
      (x₁ ⊗ x) ⊕ reduce _⊕_ e-⊕ p (map (_⊗ x) xa)
    ≡⟨ cong ((x₁ ⊗ x) ⊕_) (reduce-R-Dist {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x x₂ xs) ⟩
      (x₁ ⊗ x) ⊕ (reduce _⊕_ e-⊕ p xa ⊗ x)
    ≡⟨ sym (rdist x₁ (reduce _⊕_ e-⊕ p xa) x)  ⟩
      (x₁ ⊕ reduce _⊕_ e-⊕ p xa) ⊗ x
    ∎

  open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ; foldl-++; map-++-commute; ∷-injectiveˡ)

  tails-first : ∀{A : Set}(x : A)(xs : List A)
    → (tails (x ∷ xs)) ≡ (x ∷ xs) ∷ tails xs
  tails-first x xs = refl

  tails-last : ∀{A : Set}(xs : List A)(x : A)
    → tails (xs ++ [ x ]) ≡ (map (_++ [ x ]) (tails xs)) ++ [ [] ]
  tails-last [] x = refl
  tails-last (x₁ ∷ xs) x = cong ((x₁ ∷ xs ++ [ x ]) ∷_) (tails-last xs x)

  ++-transform : ∀{A : Set}(xs : List A)(y : A)(ys : List A)
    → (xs ++ [ y ]) ++ ys ≡ xs ++ (y ∷ ys)
  ++-transform [] y ys = refl
  ++-transform (x ∷ xs) y ys = cong (x ∷_) (++-transform xs y ys)

  horner-rule : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)(_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_)
    → (rdist : R-Dist _⊕_ _⊗_)
    → reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails ≡ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗
  horner-rule {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist = extensionality (λ xs → helper [] xs xs (++-identityˡ xs) init-proof)
    where
      init-proof : (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) [] ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) []
      init-proof = IsMonoid.identityʳ p e-⊗

      next-proof : (xs : List A)(x : A)
        → (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) xs ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) xs
        → (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (xs ++ [ x ]) ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (xs ++ [ x ])
      next-proof [] x s =
        begin
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) ([] ++ [ x ])
        ≡⟨ cong (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (++-identityˡ [ x ]) ⟩
          (x ⊗ e-⊗) ⊕ ((e-⊗) ⊕ e-⊕)
        ≡⟨ cong ((x ⊗ e-⊗) ⊕_) (IsMonoid.identityʳ p e-⊗) ⟩
          (x ⊗ e-⊗) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (IsMonoid.identityʳ q x) ⟩
          x ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (sym (IsMonoid.identityˡ q x)) ⟩
          (e-⊗ ⊗ x) ⊕ e-⊗
        ≡⟨ cong (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (sym (++-identityˡ [ x ])) ⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ ([] ++ [ x ])
        ∎
      next-proof xa@(x₁ ∷ xs) x s =
        begin
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (tails (xa ++ [ x ])))
        ≡⟨ cong (reduce _⊕_ e-⊕ p) (cong (map (reduce _⊗_ e-⊗ q)) (tails-last xa x)) ⟩
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) ((map (_++ [ x ]) (tails xa)) ++ [ [] ]))
        ≡⟨ cong (reduce _⊕_ e-⊕ p) (map-++-commute (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)) ([ [] ])) ⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa))) ++ [ e-⊗ ])
        ≡⟨ reduce-commute _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa))) ([ e-⊗ ]) ⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)))) ⊕ (e-⊗ ⊕ e-⊕)
        ≡⟨ cong (reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)))) ⊕_) (IsMonoid.identityʳ p e-⊗) ⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) ∘ map (_++ [ x ])) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong-app (map-compose (reduce _⊗_ e-⊗ q) (_++ [ x ])) (tails xa))) ⟩
          reduce _⊕_ e-⊕ p (map (λ ts → reduce _⊗_ e-⊗ q (ts ++ [ x ])) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong (λ ϕ → map ϕ (tails xa)) (extensionality (λ ts → reduce-commute _⊗_ e-⊗ q ts [ x ])))) ⟩
          reduce _⊕_ e-⊕ p (map (λ ts → reduce _⊗_ e-⊗ q ts ⊗ (x ⊗ e-⊗)) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong (λ ϕ → map ϕ (tails xa)) (extensionality (λ ts → cong (reduce _⊗_ e-⊗ q ts ⊗_) (IsMonoid.identityʳ q x))))) ⟩
          reduce _⊕_ e-⊕ p (map ((_⊗ x) ∘ (reduce _⊗_ e-⊗ q)) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong-app (sym (map-compose (_⊗ x) (reduce _⊗_ e-⊗ q))) (tails xa))) ⟩
          reduce _⊕_ e-⊕ p (map (_⊗ x) (map (reduce _⊗_ e-⊗ q) (tails xa))) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong (map (_⊗ x)) (cong (map (reduce _⊗_ e-⊗ q)) (tails-first x₁ xs)))) ⟩
          reduce _⊕_ e-⊕ p (map (_⊗ x) (reduce _⊗_ e-⊗ q xa ∷ map (reduce _⊗_ e-⊗ q) (tails (xs)))) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (reduce-R-Dist {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x (reduce _⊗_ e-⊗ q xa) (map (reduce _⊗_ e-⊗ q) (tails (xs)))) ⟩
          (reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (xa ∷ tails (xs))) ⊗ x) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (_⊗ x) (cong (reduce _⊕_ e-⊕ p) (cong (map (reduce _⊗_ e-⊗ q)) (sym (tails-first x₁ xs))))) ⟩
          (reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (tails xa)) ⊗ x) ⊕ e-⊗
        ≡⟨ cong (λ t → (t ⊗ x) ⊕ e-⊗) s ⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ xa) [ x ]
        ≡⟨ sym (foldl-++ (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ xa [ x ]) ⟩
          (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (xa ++ [ x ])
        ∎

      helper : (left right all : List A)(s : left ++ right ≡ all)
        → (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) left ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) left
        → (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) all ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) all
      helper left [] all s t =
        begin
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) all
        ≡⟨ cong (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (sym s) ⟩
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (left ++ [])
        ≡⟨ cong (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (++-identityʳ left) ⟩
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) left
        ≡⟨ t ⟩
          (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) left
        ≡⟨ cong (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (sym (++-identityʳ left)) ⟩
          (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (left ++ [])
        ≡⟨ cong (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) s ⟩
          (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) all
        ∎
      helper left (x ∷ right) all s t = helper (left ++ [ x ]) right all (trans (++-transform left x right) s) (next-proof left x t)
  
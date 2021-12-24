module HW16 where

-- How to type those Unicode characters:
-- →   \->
-- ≡   \==
-- ≢   \==n
-- ⟨   \<
-- ⟩   \>
-- ∎   \qed
-- ∘   \o
-- ∷   \::
-- ℕ   \bN
-- ⊕   \oplus
-- ˡ   \^l       (4th candidate, use your right arrow key to select)
-- ʳ   \^r       (4th candidate, use your right arrow key to select)
-- ₁   \_1
-- ×   \x
-- ∀   \all
-- Σ   \Sigma
-- ∃   \ex
-- ⊆   \subseteq
-- ≤   \le
-- ⊔   \sqcup
-- ¬   \neg
-- ⊥   \bot
-- ∈   \in

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

module MSS (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Data.Nat using (ℕ; _+_; zero; suc; _⊔_)
  open import Data.List using (List; []; _∷_; [_]; _++_; foldl; foldr; map; scanl; scanr)

  inits : ∀ {A : Set} → List A → List (List A)
  inits = scanl _++_ [] ∘ map [_]

  tails : ∀ {A : Set} → List A → List (List A)
  tails = scanr _++_ [] ∘ map [_]

  concat : ∀ {A : Set} → List (List A) → List A
  concat = foldr _++_ []

  segs : ∀ {A : Set} → List A → List (List A)
  segs = concat ∘ map tails ∘ inits

  sum : List ℕ → ℕ
  sum = foldr _+_ 0

  maximum : List ℕ → ℕ
  maximum = foldr _⊔_ 0

  mss : List ℕ → ℕ
  mss = maximum ∘ map sum ∘ segs

  -- Did you know there are plenty of useful theorems in the standard library?
  open import Data.Nat.Properties using (+-distribˡ-⊔; +-distribʳ-⊔)
  -- +-distribˡ-⊔ : ∀ x y z → x + (y ⊔ z) ≡ (x + y) ⊔ (x + z)
  -- +-distribʳ-⊔ : ∀ z x y → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)

  open import Data.Nat.Properties using (+-identityʳ; ⊔-identityʳ; +-assoc; +-identityˡ; +-comm; ⊔-comm)

  _⊙_ : (a b : ℕ) → ℕ
  _⊙_ a b = (a + b) ⊔ 0

  reduce : ∀{A : Set} → (_⊕_ : A → A → A) → (e : A) → IsMonoid e _⊕_ → List A → A
  reduce _⊕_ e _ [] = e
  reduce _⊕_ e p (x ∷ xs) = x ⊕ reduce _⊕_ e p xs

  flatten : ∀ {A : Set} → List (List A) → List A
  flatten = reduce _++_ [] List-++-is-monoid

  map-flatten : ∀ {A B : Set} → (f : A → B) → (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-flatten f [] ys = refl
  map-flatten f (x ∷ xs) ys =
    begin
      map f ((x ∷ xs) ++ ys)
    ≡⟨⟩
      map f (x ∷ (xs ++ ys))
    ≡⟨⟩
      f x ∷ map f (xs ++ ys)
    ≡⟨ cong (f x ∷_) (map-flatten f xs ys) ⟩
      f x ∷ (map f xs ++ map f ys)
    ∎

  map-distrib : ∀{A B C : Set} (f : B → C) (g : A → B) → map f ∘ map g ≡ map (f ∘ g)
  map-distrib {A} f g = extensionality lemma
    where
      lemma : (xs : List A) → (map f ∘ map g) xs ≡ map (f ∘ g) xs
      lemma [] = refl
      lemma (x ∷ xs) =
        begin
          (map f ∘ map g) (x ∷ xs)
        ≡⟨⟩
          map f (map g (x ∷ xs))
        ≡⟨⟩
          map f (g x ∷ map g xs)
        ≡⟨⟩
          f (g x) ∷ map f (map g xs)
        ≡⟨ cong (f (g x) ∷_) (lemma xs) ⟩
          f (g x) ∷ map (f ∘ g) xs
        ≡⟨⟩
          map (f ∘ g) (x ∷ xs)
        ∎

  map-promotion : ∀{A B : Set} (f : A → B) → map f ∘ flatten ≡ flatten ∘ map (map f)
  map-promotion {A} {B} f = extensionality lemma
    where
      lemma : (xs : List (List A)) → (map f ∘ flatten) xs ≡ (flatten ∘ map (map f)) xs
      lemma [] = refl
      lemma (xs ∷ xs₁) =
        begin
          (map f ∘ flatten) (xs ∷ xs₁)
        ≡⟨⟩
          map f (flatten (xs ∷ xs₁))
        ≡⟨⟩
          map f (xs ++ flatten xs₁)
        ≡⟨ map-flatten f xs (flatten xs₁) ⟩
          map f xs ++ map f (flatten xs₁)
        ≡⟨ cong (map f xs ++_) (lemma xs₁) ⟩
          map f xs ++ flatten (map (map f) xs₁)
        ≡⟨⟩
          flatten (map (map f) (xs ∷ xs₁))
        ≡⟨⟩
          (flatten ∘ map (map f)) (xs ∷ xs₁)
        ∎

  reduce-commute : ∀{A : Set} (_⊕_ : A → A → A)(e : A)(p : IsMonoid e _⊕_)(xs ys : List A) → reduce _⊕_ e p (xs ++ ys) ≡ reduce _⊕_ e p xs ⊕ reduce _⊕_ e p ys
  reduce-commute _⊕_ e p [] ys =
    begin
      reduce _⊕_ e p ([] ++ ys)
    ≡⟨⟩
      reduce _⊕_ e p ys
    ≡⟨ sym (IsMonoid.identityˡ p (reduce _⊕_ e p ys)) ⟩
      e ⊕ reduce _⊕_ e p ys
    ∎
  reduce-commute _⊕_ e p (x ∷ xs) ys =
    begin
      reduce _⊕_ e p (x ∷ xs ++ ys)
    ≡⟨⟩
      x ⊕ reduce _⊕_ e p (xs ++ ys)
    ≡⟨ cong (x ⊕_) (reduce-commute _⊕_ e p xs ys) ⟩
      x ⊕ (reduce _⊕_ e p xs ⊕ reduce _⊕_ e p ys)
    ≡⟨ sym (IsSemigroup.assoc (IsMonoid.is-semigroup p) x (reduce _⊕_ e p xs) (reduce _⊕_ e p ys))  ⟩
      (x ⊕ reduce _⊕_ e p xs) ⊕ reduce _⊕_ e p ys
    ≡⟨⟩
      reduce _⊕_ e p (x ∷ xs) ⊕ reduce _⊕_ e p ys
    ∎

  reduce-promotion : ∀{A : Set} (_⊕_ : A → A → A) (e : A)(p : IsMonoid e _⊕_) → reduce _⊕_ e p ∘ flatten ≡ reduce _⊕_ e p ∘ map (reduce _⊕_ e p)
  reduce-promotion {A} _⊕_ e p = extensionality lemma
    where
      lemma : (xs : List (List A)) → (reduce _⊕_ e p ∘ flatten) xs ≡ (reduce _⊕_ e p ∘ map (reduce _⊕_ e p)) xs
      lemma [] = refl
      lemma (xs ∷ xs₁) =
        begin
          (reduce _⊕_ e p ∘ flatten) (xs ∷ xs₁)
        ≡⟨⟩
          reduce _⊕_ e p (flatten (xs ∷ xs₁))
        ≡⟨⟩
          reduce _⊕_ e p (xs ++ flatten xs₁)
        ≡⟨ reduce-commute _⊕_ e p xs (flatten xs₁) ⟩
          reduce _⊕_ e p xs ⊕ reduce _⊕_ e p (flatten xs₁)
        ≡⟨ cong (reduce _⊕_ e p xs ⊕_) (lemma xs₁) ⟩
          reduce _⊕_ e p xs ⊕ reduce _⊕_ e p (map (reduce _⊕_ e p) xs₁)
        ≡⟨⟩
          reduce _⊕_ e p (reduce _⊕_ e p xs ∷ map (reduce _⊕_ e p) xs₁)
        ≡⟨⟩
          reduce _⊕_ e p (map (reduce _⊕_ e p) (xs ∷ xs₁))
        ∎

  foldl-last : ∀{A : Set}(_⊕_ : A → A → A)(e : A)(xs : List A)(x : A)
    → foldl _⊕_ e xs ⊕ x ≡ foldl _⊕_ e (xs ++ [ x ])
  foldl-last _⊕_ e [] x = refl
  foldl-last _⊕_ e (x₁ ∷ xs) x =
    begin
      foldl _⊕_ (e ⊕ x₁) xs ⊕ x
    ≡⟨ foldl-last _⊕_ (e ⊕ x₁) xs x ⟩
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
      next-proof acc head x p =
        begin
          acc ⊕ x
        ≡⟨ cong (_⊕ x) p ⟩
          foldl _⊕_ e head ⊕ x
        ≡⟨ foldl-last _⊕_ e head x ⟩
          foldl _⊕_ e (head ++ [ x ])
        ∎

      lemma : (acc : A)(head : List A)(p : acc ≡ foldl _⊕_ e head)
        → (xs : List A)
        → scanl _⊕_ acc xs ≡ (map (foldl _⊕_ e) ∘ (scanl _++_ head ∘ map [_])) xs
      lemma acc head p [] =
        begin
          acc ∷ []
        ≡⟨ cong (_∷ []) p ⟩
          foldl _⊕_ e head ∷ []
        ≡⟨⟩
          map (foldl _⊕_ e) (head ∷ [])
        ≡⟨⟩
          map (foldl _⊕_ e) (scanl _++_ head [])
        ≡⟨⟩
          map (foldl _⊕_ e) (scanl _++_ head (map [_] []))
        ∎
      lemma acc head p (x ∷ xs) =
        begin
          acc ∷ scanl _⊕_ (acc ⊕ x) xs
        ≡⟨ cong (acc ∷_) (lemma (acc ⊕ x) (head ++ [ x ]) (next-proof acc head x p) xs) ⟩
          acc ∷ map (foldl _⊕_ e) (scanl _++_ (head ++ [ x ]) (map [_] xs))
        ≡⟨ cong (_∷ map (foldl _⊕_ e) (scanl _++_ (head ++ [ x ]) (map [_] xs))) p ⟩
          foldl _⊕_ e head ∷ map (foldl _⊕_ e) (scanl _++_ (head ++ [ x ]) (map [_] xs))
        ≡⟨⟩
          map (foldl _⊕_ e) (head ∷ scanl _++_ (head ++ [ x ]) (map [_] xs))
        ≡⟨⟩
          map (foldl _⊕_ e) (scanl _++_ head ([ x ] ∷ map [_] xs))
        ≡⟨⟩
          map (foldl _⊕_ e) (scanl _++_ head (map [_] (x ∷ xs)))
        ∎

  reduce-is-foldr : ∀{A : Set} → (_⊕_ : A → A → A) → (e : A) → (p : IsMonoid e _⊕_) → reduce _⊕_ e p ≡ foldr _⊕_ e
  reduce-is-foldr {A} _⊕_ e p = extensionality lemma
    where
      lemma : (xs : List A) → reduce _⊕_ e p xs ≡ foldr _⊕_ e xs
      lemma [] = refl
      lemma (x ∷ xs) = cong (x ⊕_) (lemma xs)

  mss-fast : List ℕ → ℕ
  mss-fast = maximum ∘ (scanl _⊙_ 0)

  maximum-is-reducable : maximum ≡ reduce _⊔_ 0 ℕ-⊔-is-monoid
  maximum-is-reducable = sym (reduce-is-foldr _⊔_ 0 ℕ-⊔-is-monoid)

  maximum′ : List ℕ → ℕ
  maximum′ = reduce _⊔_ 0 ℕ-⊔-is-monoid

  maximum-is-maximum′ : maximum ≡ maximum′
  maximum-is-maximum′ = maximum-is-reducable

  concat-is-reducable : ∀{A : Set} → concat {A} ≡ reduce _++_ [] List-++-is-monoid
  concat-is-reducable = sym (reduce-is-foldr _++_ [] List-++-is-monoid)

  concat-is-flatten : ∀{A : Set} → concat {A} ≡ flatten {A}
  concat-is-flatten = concat-is-reducable

  sum-is-reducable : sum ≡ reduce _+_ 0 ℕ-add-is-monoid
  sum-is-reducable = sym (reduce-is-foldr _+_ 0 ℕ-add-is-monoid)

  sum′ : List ℕ → ℕ
  sum′ = reduce _+_ 0 ℕ-add-is-monoid

  sum-is-sum′ : sum ≡ sum′
  sum-is-sum′ = sum-is-reducable

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
  tails-first x [] = refl
  tails-first x (x₁ ∷ xs)
    with tails (x₁ ∷ xs) | tails-first x₁ xs
  ... | []     | ()
  ... | z ∷ zs | p =
    begin
      (x ∷ z) ∷ z ∷ zs
    ≡⟨ cong (_∷ z ∷ zs) (cong (x ∷_) (∷-injectiveˡ p)) ⟩
      (x ∷ x₁ ∷ xs) ∷ z ∷ zs
    ∎

  tails′ : ∀{A : Set} → List A → List (List A)
  tails′ []       = [] ∷ []
  tails′ (x ∷ xs) = (x ∷ xs) ∷ tails′ xs

  tails≡tails′ : ∀{A : Set} → tails ≡ tails′
  tails≡tails′ {A} = extensionality lemma
    where
      lemma : (xs : List A) → tails xs ≡ tails′ xs
      lemma [] = refl
      lemma (x ∷ xs) =
        begin
          tails (x ∷ xs)
        ≡⟨ tails-first x xs ⟩
          (x ∷ xs) ∷ tails xs
        ≡⟨ cong ((x ∷ xs) ∷_) (lemma xs) ⟩
          (x ∷ xs) ∷ tails′ xs
        ∎

  tails′-last : ∀{A : Set}(xs : List A)(x : A)
    → tails′ (xs ++ [ x ]) ≡ (map (_++ [ x ]) (tails′ xs)) ++ [ [] ]
  tails′-last [] x = refl
  tails′-last (x₁ ∷ xs) x = cong ((x₁ ∷ xs ++ [ x ]) ∷_) (tails′-last xs x)

  tails-last : ∀{A : Set}(xs : List A)(x : A)
    → tails (xs ++ [ x ]) ≡ (map (_++ [ x ]) (tails xs)) ++ [ [] ]
  tails-last xs x =
    begin
      tails (xs ++ [ x ])
    ≡⟨ cong-app tails≡tails′ (xs ++ [ x ]) ⟩
      tails′ (xs ++ [ x ])
    ≡⟨ tails′-last xs x ⟩
      map (_++ [ x ]) (tails′ xs) ++ [ [] ]
    ≡⟨ cong (_++ [ [] ]) (cong (map (_++ [ x ])) (cong-app (sym tails≡tails′) xs)) ⟩
      map (_++ [ x ]) (tails xs) ++ [ [] ]
    ∎

  horner-rule : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)(_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_)
    → (rdist : R-Dist _⊕_ _⊗_)
    -----------------------------
    → reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails ≡ foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗
  horner-rule {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist = extensionality (λ xs → helper [] xs xs (++-identityˡ xs) init-proof)
    where
      init-proof : (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) [] ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) []
      init-proof =
        begin
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) []
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) [ [] ])
        ≡⟨⟩
          reduce _⊕_ e-⊕ p ([ reduce _⊗_ e-⊗ q [] ])
        ≡⟨⟩
          reduce _⊕_ e-⊕ p ([ e-⊗ ])
        ≡⟨⟩
          e-⊗ ⊕ e-⊕
        ≡⟨ IsMonoid.identityʳ p e-⊗ ⟩
          e-⊗
        ∎

      next-proof : (xs : List A)(x : A)
        → (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) xs ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) xs
        → (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (xs ++ [ x ]) ≡ (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (xs ++ [ x ])
      next-proof [] x s =
        begin
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) ([] ++ [ x ])
        ≡⟨ cong (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (++-identityˡ [ x ]) ⟩
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) [ x ]
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (tails [ x ]))
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) ([ x ] ∷ ([] ∷ [])))
        ≡⟨⟩
          reduce _⊕_ e-⊕ p ((x ⊗ e-⊗) ∷ e-⊗ ∷ [])
        ≡⟨⟩
          (x ⊗ e-⊗) ⊕ ((e-⊗) ⊕ e-⊕)
        ≡⟨ cong ((x ⊗ e-⊗) ⊕_) (IsMonoid.identityʳ p e-⊗) ⟩
          (x ⊗ e-⊗) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (IsMonoid.identityʳ q x) ⟩
          x ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (sym (IsMonoid.identityˡ q x)) ⟩
          (e-⊗ ⊗ x) ⊕ e-⊗
        ≡⟨⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ [ x ]
        ≡⟨ cong (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (sym (++-identityˡ [ x ])) ⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ ([] ++ [ x ])
        ∎
      next-proof xa@(x₁ ∷ xs) x s =
        begin
          (reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails) (xa ++ [ x ])
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (tails (xa ++ [ x ])))
        ≡⟨ cong (reduce _⊕_ e-⊕ p) (cong (map (reduce _⊗_ e-⊗ q)) (tails-last xa x)) ⟩
          reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) ((map (_++ [ x ]) (tails xa)) ++ [ [] ]))
        ≡⟨ cong (reduce _⊕_ e-⊕ p) (map-++-commute (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)) ([ [] ])) ⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa))) ++ [ reduce _⊗_ e-⊗ q [] ])
        ≡⟨⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa))) ++ [ e-⊗ ])
        ≡⟨ reduce-commute _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa))) ([ e-⊗ ]) ⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)))) ⊕ reduce _⊕_ e-⊕ p [ e-⊗ ]
        ≡⟨⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)))) ⊕ (e-⊗ ⊕ e-⊕)
        ≡⟨ cong (reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)))) ⊕_) (IsMonoid.identityʳ p e-⊗) ⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) (map (_++ [ x ]) (tails xa)))) ⊕ e-⊗
        ≡⟨⟩
          reduce _⊕_ e-⊕ p ((map (reduce _⊗_ e-⊗ q) ∘ map (_++ [ x ])) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong-app (map-distrib (reduce _⊗_ e-⊗ q) (_++ [ x ])) (tails xa))) ⟩
          reduce _⊕_ e-⊕ p (map ((reduce _⊗_ e-⊗ q) ∘ (_++ [ x ])) (tails xa)) ⊕ e-⊗
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (λ ts → reduce _⊗_ e-⊗ q (ts ++ [ x ])) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong (λ ϕ → map ϕ (tails xa)) (extensionality (λ ts → reduce-commute _⊗_ e-⊗ q ts [ x ])))) ⟩
          reduce _⊕_ e-⊕ p (map (λ ts → reduce _⊗_ e-⊗ q ts ⊗ reduce _⊗_ e-⊗ q [ x ]) (tails xa)) ⊕ e-⊗
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (λ ts → reduce _⊗_ e-⊗ q ts ⊗ (x ⊗ e-⊗)) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong (λ ϕ → map ϕ (tails xa)) (extensionality (λ ts → cong (reduce _⊗_ e-⊗ q ts ⊗_) (IsMonoid.identityʳ q x))))) ⟩
          reduce _⊕_ e-⊕ p (map (λ ts → reduce _⊗_ e-⊗ q ts ⊗ x) (tails xa)) ⊕ e-⊗
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map ((_⊗ x) ∘ (reduce _⊗_ e-⊗ q)) (tails xa)) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong-app (sym (map-distrib (_⊗ x) (reduce _⊗_ e-⊗ q))) (tails xa))) ⟩
          reduce _⊕_ e-⊕ p ((map (_⊗ x) ∘ map (reduce _⊗_ e-⊗ q)) (tails xa)) ⊕ e-⊗
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (_⊗ x) (map (reduce _⊗_ e-⊗ q) (tails xa))) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (reduce _⊕_ e-⊕ p) (cong (map (_⊗ x)) (cong (map (reduce _⊗_ e-⊗ q)) (tails-first x₁ xs)))) ⟩
          reduce _⊕_ e-⊕ p (map (_⊗ x) (map (reduce _⊗_ e-⊗ q) (xa ∷ tails (xs)))) ⊕ e-⊗
        ≡⟨⟩
          reduce _⊕_ e-⊕ p (map (_⊗ x) (reduce _⊗_ e-⊗ q xa ∷ map (reduce _⊗_ e-⊗ q) (tails (xs)))) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (reduce-R-Dist {A} _⊕_ e-⊕ _⊗_ e-⊗ p q rdist x (reduce _⊗_ e-⊗ q xa) (map (reduce _⊗_ e-⊗ q) (tails (xs)))) ⟩
          (reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (xa ∷ tails (xs))) ⊗ x) ⊕ e-⊗
        ≡⟨ cong (_⊕ e-⊗) (cong (_⊗ x) (cong (reduce _⊕_ e-⊕ p) (cong (map (reduce _⊗_ e-⊗ q)) (sym (tails-first x₁ xs))))) ⟩
          (reduce _⊕_ e-⊕ p (map (reduce _⊗_ e-⊗ q) (tails xa)) ⊗ x) ⊕ e-⊗
        ≡⟨ cong (λ t → (t ⊗ x) ⊕ e-⊗) s ⟩
          ((foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ xa) ⊗ x) ⊕ e-⊗
        ≡⟨⟩
          foldl (λ a b → (a ⊗ b) ⊕ e-⊗) (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ xa) [ x ]
        ≡⟨ sym (foldl-++ (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗ xa [ x ]) ⟩
          (foldl (λ a b → (a ⊗ b) ⊕ e-⊗) e-⊗) (xa ++ [ x ])
        ∎

      ++-transform : (xs : List A)(y : A)(ys : List A)
        → (xs ++ [ y ]) ++ ys ≡ xs ++ (y ∷ ys)
      ++-transform [] y ys = refl
      ++-transform (x ∷ xs) y ys =
        begin
          x ∷ (xs ++ [ y ]) ++ ys
        ≡⟨⟩
          x ∷ ((xs ++ [ y ]) ++ ys)
        ≡⟨ cong (x ∷_) (++-transform xs y ys) ⟩
          x ∷ (xs ++ (y ∷ ys))
        ≡⟨⟩
          (x ∷ xs) ++ (y ∷ ys)
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

  ⊔-refl : (x : ℕ) → x ⊔ x ≡ x
  ⊔-refl zero = refl
  ⊔-refl (suc x) = cong suc (⊔-refl x)
  ⊔-only : (x y : ℕ) → (0 + x) ⊔ (y + x) ≡ y + x
  ⊔-only zero y = refl
  ⊔-only (suc x) y =
    begin
      (0 + suc x) ⊔ (y + suc x)
    ≡⟨ cong ((0 + suc x) ⊔_) (+-comm y (suc x)) ⟩
      (0 + suc x) ⊔ (suc x + y)
    ≡⟨ cong ((0 + suc x) ⊔_) (cong suc (+-comm x y)) ⟩
      (suc (0 + x)) ⊔ (suc (y + x))
    ≡⟨⟩
      suc ((0 + x) ⊔ (y + x))
    ≡⟨ cong suc (⊔-only x y) ⟩
      suc y + x
    ≡⟨ cong suc (+-comm y x) ⟩
      suc x + y
    ≡⟨ +-comm (suc x) y ⟩
      y + suc x
    ∎


  R-Dist-⊔-+ : R-Dist _⊔_ _+_
  R-Dist-⊔-+ zero zero c =
    begin
      (0 ⊔ 0) + c
    ≡⟨ +-identityˡ c ⟩
      c
    ≡⟨ sym (⊔-refl c) ⟩
      (0 + c) ⊔ (0 + c)
    ∎
  R-Dist-⊔-+ zero (suc b) c =
    begin
      (0 ⊔ suc b) + c
    ≡⟨⟩
      (suc b) + c
    ≡⟨ sym (⊔-only c (suc b)) ⟩
      (0 + c) ⊔ ((suc b) + c)
    ∎
  R-Dist-⊔-+ (suc a) zero c =
    begin
      (suc a ⊔ 0) + c
    ≡⟨ cong (_+ c) (⊔-comm (suc a) 0) ⟩
      (0 ⊔ suc a) + c
    ≡⟨ R-Dist-⊔-+ 0 (suc a) c ⟩
      (0 + c) ⊔ (suc a + c)
    ≡⟨ ⊔-comm (0 + c) (suc a + c) ⟩
      (suc a + c) ⊔ (0 + c)
    ∎
  R-Dist-⊔-+ (suc a) (suc b) c =
    begin
      (suc a ⊔ suc b) + c
    ≡⟨⟩
      suc (a ⊔ b) + c
    ≡⟨⟩
      suc ((a ⊔ b) + c)
    ≡⟨ cong suc (R-Dist-⊔-+ a b c) ⟩
      suc ((a + c) ⊔ (b + c))
    ≡⟨⟩
      (suc a + c) ⊔ (suc b + c)
    ∎

  segs′ : ∀ {A : Set} → List A → List (List A)
  segs′ = flatten ∘ map tails ∘ inits
  segs-is-segs′ : ∀ {A : Set} → segs {A} ≡ segs′ {A}
  segs-is-segs′ {A} = extensionality lemma
    where
      lemma : (xs : List A) → segs xs ≡ segs′ xs
      lemma xs = begin
          segs xs
        ≡⟨⟩
          concat (map tails (inits xs))
        ≡⟨ cong-app (concat-is-flatten {List A}) (map tails (inits {A} xs)) ⟩
          flatten (map tails (inits xs))
        ≡⟨⟩
          segs′ xs
        ∎

  derivation : mss ≡ mss-fast
  derivation =
    begin
      mss
    ≡⟨⟩
      maximum ∘ map sum ∘ segs
    ≡⟨⟩
      maximum ∘ map sum ∘ concat ∘ map tails ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (map sum ∘_) segs-is-segs′) ⟩
      maximum ∘ map sum ∘ flatten ∘ map tails ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (_∘ map tails ∘ inits) (map-promotion sum)) ⟩
      maximum ∘ flatten ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (_∘ flatten ∘ map (map sum) ∘ map tails ∘ inits) maximum-is-maximum′ ⟩
      maximum′ ∘ flatten ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (_∘ map (map sum) ∘ map tails ∘ inits) (reduce-promotion _⊔_ 0 ℕ-⊔-is-monoid) ⟩
      maximum′ ∘ map maximum′ ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (maximum′ ∘_) (cong (map maximum′ ∘_) (cong (_∘  inits) (map-distrib (map sum) tails))) ⟩
      maximum′ ∘ map maximum′ ∘ map (map sum ∘ tails) ∘ inits
    ≡⟨ cong (maximum′ ∘_) (cong (_∘ inits) (map-distrib maximum′ (map sum ∘ tails))) ⟩
      maximum′ ∘ map (maximum′ ∘ map sum ∘ tails) ∘ inits
    ≡⟨ cong (_∘ map (maximum′ ∘ map sum ∘ tails) ∘ inits) (sym maximum-is-maximum′) ⟩
      maximum ∘ map (maximum′ ∘ map sum ∘ tails) ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (_∘ inits) (cong map (cong (maximum′ ∘_) (cong (_∘ tails) (cong map sum-is-sum′))))) ⟩
      maximum ∘ map (maximum′ ∘ map sum′ ∘ tails) ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (_∘ inits) ( cong map (horner-rule _⊔_ 0 _+_ 0 ℕ-⊔-is-monoid ℕ-add-is-monoid R-Dist-⊔-+))) ⟩
      maximum ∘ map (foldl _⊙_ 0) ∘ inits
    ≡⟨ cong (maximum ∘_) (sym (acc-lemma _⊙_ 0)) ⟩
      maximum ∘ (scanl _⊙_ 0)
    ≡⟨⟩
      mss-fast
    ∎

  -- note: it is possible to avoid extensionality and instead prove the following
  --
  -- derivation-alt : ∀ xs → mss xs ≡ mss-fast xs
  -- derivation-alt = ?
  --
  -- in fact, this version should be slightly easier to write, since it (generally)
  -- produces better error messages. If you want to follow this route, go ahead and
  -- prove the above 'derivation-alt', and uncomment the following:
  --
  -- derivation : mss ≡ mss-fast
  -- derivation = extensionality derivation-alt

  -- bonus(hard): try to prove the correctness of 'mss' and 'mss-fast'
  --
  -- We have this "segment" relation (you may come up with better definitions):
  --   open import Data.List using (take; drop)
  --   infix 4 _⊆_
  --   data _⊆_ {A : Set} (xs : List A) (ys : List A) : Set where
  --     segment : ∀ m n → take m (drop n ys) ≡ xs → xs ⊆ ys
  -- We also have the "less than" relation:
  --   open import Data.Nat using (_≤_)
  -- which is defined as follows in the standard library:
  --   infix 4 _≤_
  --   data _≤_ : ℕ → ℕ → Set where
  --     z≤n : ∀ {n}                 → zero  ≤ n
  --     s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
  -- 'mss' is proven to be correct if we can prove the following two theorems:
  --   open import Data.Product using (_×_; ∃-syntax)
  --   mss-is-max : ∀ {xs ys} → ys ⊆ xs → sum ys ≤ mss xs
  --   mss-exists : ∀ {xs} → ∃[ ys ] ys ⊆ xs × sum ys ≡ mss xs

module BMF2-1 where

  open import Data.Product using (_×_; _,_; Σ-syntax; proj₁)
  open import Data.Nat using (ℕ; _+_; zero; suc)
  open import Data.List using (List; []; _∷_; [_]; _++_)
  open import Relation.Nullary using (¬_)

  infixr 5 _∷′_
  data NList (A : Set) : Set where
    [_]′ : (x : A) → NList A
    _∷′_ : (x : A) → (xs : NList A) → NList A

  infixr 5 _++′_
  _++′_ : ∀ {A : Set} → NList A → NList A → NList A
  [ x ]′ ++′ ys = x ∷′ ys
  (x ∷′ xs) ++′ ys = x ∷′ xs ++′ ys

  ++′-assoc : ∀ {A : Set} (xs ys zs : NList A) → (xs ++′ ys) ++′ zs ≡ xs ++′ ys ++′ zs
  ++′-assoc [ x ]′    ys zs = refl
  ++′-assoc (x ∷′ xs) ys zs = cong (x ∷′_) (++′-assoc xs ys zs)

  NList-++′-is-semigroup : ∀ {A : Set} → IsSemigroup {NList A} _++′_
  NList-++′-is-semigroup .assoc = ++′-assoc

  -- this reduce works on non-empty lists
  reduce : ∀ {A : Set} → (_⊕_ : A → A → A) → NList A → A
  reduce {A} _⊕_ [ x ]′ = x
  reduce {A} _⊕_ (x ∷′ xs) = x ⊕ reduce _⊕_ xs

  -- this map works on non-empty lists
  -- and it produces non-empty lists
  map : ∀ {A B : Set} → (f : A → B) → NList A → NList B
  map f [ x ]′ = [ f x ]′
  map f (x ∷′ xs) = f x ∷′ map f xs

  record IsHomomorphism
    {A : Set} {_⊕_ : A → A → A} (m₁ : IsSemigroup _⊕_)
    {B : Set} {_⊗_ : B → B → B} (m₂ : IsSemigroup _⊗_)
    (f : A → B) : Set where
    field
      distrib : (x y : A) → f (x ⊕ y) ≡ f x ⊗ f y

  open IsHomomorphism

  -- 1. prove 'split' is a homomorphism
  split : ∀ {A : Set} → NList A → List A × A
  split = reduce (λ (xs , x) (ys , y) → (xs ++ [ x ] ++ ys , y)) ∘ map ([] ,_)

  -- bonus: you may also want to prove the following theorems:
  --   _⊗_ : ∀ {A : Set} → List A × A → List A × A → List A × A
  --   R-is-semigroup : ∀ {A : Set} → IsSemigroup {List A × A} _⊗_
  --   split-is-homomorphism : ∀ {A : Set} → IsHomomorphism NList-++′-is-semigroup R-is-semigroup (split {A})
  -- Alternatively, you may find it much more desirable (satisfactory) to prove the general case:
  map-distrib : ∀ {A B : Set} → (f : A → B) → (xs ys : NList A)
    → map f (xs ++′ ys) ≡ map f xs ++′ map f ys
  map-distrib f [ x ]′ ys = refl
  map-distrib f (x ∷′ xs) ys = cong (f x ∷′_) (map-distrib f xs ys)

  reduce-distrib : ∀ {A : Set} → (_⊗_ : A → A → A)
    → (s : IsSemigroup _⊗_)
    → (xs ys : NList A)
    → reduce _⊗_ (xs ++′ ys) ≡ reduce _⊗_ xs ⊗ reduce _⊗_ ys
  reduce-distrib _⊗_ s [ x ]′ ys = refl
  reduce-distrib _⊗_ s (x ∷′ xs) ys = trans (cong (x ⊗_) (reduce-distrib _⊗_ s xs ys)) (sym (IsSemigroup.assoc s x (reduce _⊗_ xs) (reduce _⊗_ ys)))

  reduce-map-is-homomorphism : ∀ {A B : Set}
    → (f : A → B)
    → (_⊗_ : B → B → B)
    → (B-⊗-is-semigroup : IsSemigroup _⊗_)
      ---------------------------------------------------------------------------
    → IsHomomorphism NList-++′-is-semigroup B-⊗-is-semigroup (reduce _⊗_ ∘ map f)
  reduce-map-is-homomorphism f _⊗_ B-⊗-is-semigroup .distrib xs ys =
    begin
      (reduce _⊗_ ∘ map f) (xs ++′ ys)
    ≡⟨⟩
      reduce _⊗_ (map f (xs ++′ ys))
    ≡⟨ cong (reduce _⊗_) (map-distrib f xs ys) ⟩
      reduce _⊗_ (map f xs ++′ map f ys)
    ≡⟨ reduce-distrib _⊗_ B-⊗-is-semigroup (map f xs) (map f ys) ⟩
      reduce _⊗_ (map f xs) ⊗ reduce _⊗_ (map f ys)
    ≡⟨⟩
      (reduce _⊗_ ∘ map f) xs ⊗ (reduce _⊗_ ∘ map f) ys
    ∎

  -- to verify your 'split' is correct. after defining 'split', proving the following
  -- should be as easy as filling in 'refl'.
  split-is-correct : split (1 ∷′ 2 ∷′ 3 ∷′ [ 4 ]′) ≡ (1 ∷ 2 ∷ 3 ∷ [] , 4)
  split-is-correct = refl

  -- bonus: find a proper way to prove your split is indeed correct:
  -- split-is-indeed-correct : ∀ {A} xs
  --   → let (ys , z) = split {A} xs
  --     in xs ≡ ys ++ [ z ]

  -- 2. prove 'init' is not a homomorphism
  init : ∀ {A : Set} → NList A → List A
  init = proj₁ ∘ split

  -- This part might be too hard for you to prove in Agda, so you can choose
  -- to write this part in natural language. If so, comment out (or remove)
  -- the following code, and write your proof in the comments.
  --
  -- Anyway, below are some key points if you want to try to prove in Agda:
  -- (1) inequality 'x ≢ y' is negation of equality: '¬ (x ≡ y)'
  -- (2) negation '¬ x' is implication to falsity: 'x → ⊥'
  -- (3) falsity '⊥' is an empty data type, it has no constructors ...
  -- (4) ... which means we can pattern match with absurd pattern '()'

  open import Data.List.Properties using (++-identityʳ-unique; ++-assoc)

  せな法則一 : [ 0 ] ≢ [ 1 ]
  せな法則一 ()

  せな法則ニ : ∀ {_⊗_} (m : IsSemigroup _⊗_)
    → IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
    → [] ⊗ [] ≡ [ 0 ]
  せな法則ニ {_⊗_} m h =
    begin
      [] ⊗ []
    ≡⟨⟩
      init [ 0 ]′ ⊗ init [ 0 ]′
    ≡⟨ sym (IsHomomorphism.distrib h [ 0 ]′ [ 0 ]′) ⟩
      init ([ 0 ]′ ++′ [ 0 ]′)
    ≡⟨⟩
      [ 0 ]
    ∎

  せな法則三 : ∀ {_⊗_} (m : IsSemigroup _⊗_)
    → IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
    → [] ⊗ [] ≡ [ 1 ]
  せな法則三 {_⊗_} m h =
    begin
      [] ⊗ []
    ≡⟨⟩
      init [ 1 ]′ ⊗ init [ 1 ]′
    ≡⟨ sym (IsHomomorphism.distrib h [ 1 ]′ [ 1 ]′) ⟩
      init ([ 1 ]′ ++′ [ 1 ]′)
    ≡⟨⟩
      [ 1 ]
    ∎

  init-is-not-homomorphism : ∀ {_⊗_} (m : IsSemigroup _⊗_)
    → ¬ IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  init-is-not-homomorphism m h = せな法則一 (trans (sym (せな法則ニ m h)) (せな法則三 m h))

  -- Hint: you might want to follow this guideline below if you get stuck.
  --
  -- Step 1: interpret the theorem
  --   ¬ IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  -- is just another way of saying
  --   IsHomomorphism NList-++′-is-semigroup m (init {ℕ}) → ⊥
  -- (proof by contradiction)
  --
  -- Step 2: get your premise
  -- You want to derive contradiction from the premise, so the first thing
  -- to do is get the premise (add it as an argument):
  --   init-is-not-homomorphism {_⊗_} m H = ?
  -- Now we have the following premises:
  --   m : IsSemigroup _⊗_
  --   H : IsHomomorphism NList-++′-is-semigroup m (init {ℕ})
  --
  -- Step 3: derive absurd results
  -- Pass in some example to your premises, and try to get some absurd
  -- results such as 'K : [ 0 ] ≡ [ 42 ]'.
  --
  -- Step 4: show the absurdity by proving the negation
  -- e.g. for 'K : [ 0 ] ≡ [ 42 ]', write the following:
  --   ¬K : [ 0 ] ≢ [ 42 ]
  --   ¬K ()
  --
  -- Step 5: make use of that absurd result
  -- Use the result 'K' from Step 3, apply it to '¬K':
  --   ¬K K
  -- Just use this expression as the return value.
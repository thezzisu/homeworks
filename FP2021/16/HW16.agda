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

module MSS (
    extensionality : ∀ {A : Set} {B : A → Set}
        {f g : (x : A) → B x}
      → ((x : A) → f x ≡ g x)
        ---------------------
      → f ≡ g
  ) where

  open import Data.List using (List; []; _∷_; [_]; _++_; foldl; foldr; map; scanl; scanr)
  open import Data.Nat using (ℕ; _+_; zero; suc; _⊔_)

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

  module monoid where
    record IsMonoid {A : Set} (e : A) (_⊕_ : A → A → A) : Set where
      field
        assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
        identityˡ : ∀ x → e ⊕ x ≡ x
        identityʳ : ∀ x → x ⊕ e ≡ x

    open IsMonoid public

    open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
    ℕ-add-is-monoid : IsMonoid 0 _+_
    ℕ-add-is-monoid .assoc = +-assoc
    ℕ-add-is-monoid .identityˡ = +-identityˡ
    ℕ-add-is-monoid .identityʳ = +-identityʳ

    open import Data.Nat.Properties using (⊔-assoc; ⊔-identityˡ; ⊔-identityʳ)
    ℕ-⊔-is-monoid : IsMonoid 0 _⊔_
    ℕ-⊔-is-monoid .assoc = ⊔-assoc
    ℕ-⊔-is-monoid .identityˡ = ⊔-identityˡ
    ℕ-⊔-is-monoid .identityʳ = ⊔-identityʳ

    open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
    List-++-is-monoid : ∀ {A : Set} → IsMonoid {List A} [] _++_
    List-++-is-monoid .assoc = ++-assoc
    List-++-is-monoid .identityˡ = ++-identityˡ
    List-++-is-monoid .identityʳ = ++-identityʳ

  open monoid

  -- Did you know there are plenty of useful theorems in the standard library?
  open import Data.Nat.Properties using (+-distribˡ-⊔; +-distribʳ-⊔; +-identityʳ; ⊔-identityʳ; +-assoc; +-identityˡ; +-comm; ⊔-comm)
  -- +-distribˡ-⊔ : ∀ x y z → x + (y ⊔ z) ≡ (x + y) ⊔ (x + z)
  -- +-distribˡ-⊔ : ∀ x y z → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)

  _⊙_ : (a b : ℕ) → ℕ
  _⊙_ a b = (a + b) ⊔ 0

  ⊙-assoc : ∀ x y z → (x ⊙ y) ⊙ z ≡ x ⊙ (y ⊙ z)
  ⊙-assoc x y z =
    begin
      (x ⊙ y) ⊙ z
    ≡⟨⟩
      ((x ⊙ y) + z) ⊔ 0
    ≡⟨ ⊔-identityʳ ((x ⊙ y) + z) ⟩
      (x ⊙ y) + z
    ≡⟨ cong (_+ z) refl ⟩
      ((x + y) ⊔ 0) + z
    ≡⟨ cong (_+ z) (⊔-identityʳ (x + y)) ⟩
      (x + y) + z
    ≡⟨ +-assoc x y z ⟩
      x + (y + z)
    ≡⟨ cong (x +_) (sym (⊔-identityʳ (y + z))) ⟩
      x + ((y + z) ⊔ 0)
    ≡⟨⟩
      x + (y ⊙ z)
    ≡⟨ sym (⊔-identityʳ (x + (y ⊙ z))) ⟩
      (x + (y ⊙ z)) ⊔ 0
    ≡⟨⟩
      x ⊙ (y ⊙ z)
    ∎

  ⊙-identityˡ : ∀ x → 0 ⊙ x ≡ x
  ⊙-identityˡ zero = refl
  ⊙-identityˡ (suc x) = refl

  ⊙-identityʳ : ∀ x → x ⊙ 0 ≡ x
  ⊙-identityʳ x = begin
      x ⊙ 0
    ≡⟨⟩
      (x + 0) ⊔ 0
    ≡⟨ cong (_⊔ 0) (+-identityʳ x) ⟩
      x ⊔ 0
    ≡⟨ (⊔-identityʳ x) ⟩
      x
    ∎

  ℕ-⊙-is-monoid : IsMonoid 0 _⊙_
  ℕ-⊙-is-monoid .assoc = ⊙-assoc
  ℕ-⊙-is-monoid .identityˡ = ⊙-identityˡ
  ℕ-⊙-is-monoid .identityʳ = ⊙-identityʳ

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

  reduce-split : ∀{A : Set} (_⊕_ : A → A → A)(e : A)(p : IsMonoid e _⊕_)(xs ys : List A) → reduce _⊕_ e p (xs ++ ys) ≡ reduce _⊕_ e p xs ⊕ reduce _⊕_ e p ys
  reduce-split _⊕_ e p [] ys =
    begin
      reduce _⊕_ e p ([] ++ ys)
    ≡⟨⟩
      reduce _⊕_ e p ys
    ≡⟨ sym (IsMonoid.identityˡ p (reduce _⊕_ e p ys)) ⟩
      e ⊕ reduce _⊕_ e p ys
    ∎
  reduce-split _⊕_ e p (x ∷ xs) ys =
    begin
      reduce _⊕_ e p (x ∷ xs ++ ys)
    ≡⟨⟩
      x ⊕ reduce _⊕_ e p (xs ++ ys)
    ≡⟨ cong (x ⊕_) (reduce-split _⊕_ e p xs ys) ⟩
      x ⊕ (reduce _⊕_ e p xs ⊕ reduce _⊕_ e p ys)
    ≡⟨ sym (IsMonoid.assoc p x (reduce _⊕_ e p xs) (reduce _⊕_ e p ys))  ⟩
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
        ≡⟨ reduce-split _⊕_ e p xs (flatten xs₁) ⟩
          reduce _⊕_ e p xs ⊕ reduce _⊕_ e p (flatten xs₁)
        ≡⟨ cong (reduce _⊕_ e p xs ⊕_) (lemma xs₁) ⟩
          reduce _⊕_ e p xs ⊕ reduce _⊕_ e p (map (reduce _⊕_ e p) xs₁)
        ≡⟨⟩
          reduce _⊕_ e p (reduce _⊕_ e p xs ∷ map (reduce _⊕_ e p) xs₁)
        ≡⟨⟩
          reduce _⊕_ e p (map (reduce _⊕_ e p) (xs ∷ xs₁))
        ∎

  acc-lemma : ∀{A : Set} (_⊕_ : A → A → A) (e : A) → scanl _⊕_ e ≡ map (foldl _⊕_ e) ∘ inits
  acc-lemma {A} _⊕_ e = extensionality lemma
    where
      lemma : (xs : List A) → scanl _⊕_ e xs ≡ (map (foldl _⊕_ e) ∘ inits) xs
      lemma [] = refl
      lemma (x ∷ xs) =
        begin
          scanl _⊕_ e (x ∷ xs)
        ≡⟨⟩
          e ∷ scanl _⊕_ (e ⊕ x) xs
        ≡⟨ {!   !} ⟩
          map (foldl _⊕_ e) (inits (x ∷ xs))
        ≡⟨⟩
          (map (foldl _⊕_ e) ∘ inits) (x ∷ xs)
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

  maximum' : List ℕ → ℕ
  maximum' = reduce _⊔_ 0 ℕ-⊔-is-monoid

  maximum-is-maximum' : maximum ≡ maximum'
  maximum-is-maximum' = maximum-is-reducable

  concat-is-reducable : ∀{A : Set} → concat {A} ≡ reduce _++_ [] List-++-is-monoid
  concat-is-reducable = sym (reduce-is-foldr _++_ [] List-++-is-monoid)

  concat-is-flatten : ∀{A : Set} → concat {A} ≡ flatten {A}
  concat-is-flatten = concat-is-reducable

  sum-is-reducable : sum ≡ reduce _+_ 0 ℕ-add-is-monoid
  sum-is-reducable = sym (reduce-is-foldr _+_ 0 ℕ-add-is-monoid)

  sum' : List ℕ → ℕ
  sum' = reduce _+_ 0 ℕ-add-is-monoid

  sum-is-sum' : sum ≡ sum'
  sum-is-sum' = sum-is-reducable

  ∘-assoc : ∀{l l' l'' l'''}{A : Set l}{B : Set l'}{C : Set l''}{D : Set l'''}(f : C → D)(g : B → C)(h : A → B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  ∘-assoc f g h = refl

  R-Dist : ∀{A : Set} (_⊕_ : A → A → A)(_⊗_ : A → A → A) → Set
  R-Dist {A} _⊕_ _⊗_ = ∀ (a b c : A) → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊗ c)

  horner-rule : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)(_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_)
    → (rdist : R-Dist _⊕_ _⊗_)
    -----------------------------
    → reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails ≡ foldl (λ a b → (a ⊗ b) ⊕ e-⊗ ) e-⊗
  horner-rule = {!   !}

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
  
  segs' : ∀ {A : Set} → List A → List (List A)
  segs' = flatten ∘ map tails ∘ inits
  segs-is-segs' : ∀ {A : Set} → segs {A} ≡ segs' {A}
  segs-is-segs' {A} = extensionality lemma
    where
      lemma : (xs : List A) → segs xs ≡ segs' xs
      lemma xs = begin
          segs xs
        ≡⟨⟩
          concat (map tails (inits xs))
        ≡⟨ cong-app (concat-is-flatten {List A}) (map (tails {A}) (inits {A} xs)) ⟩
          flatten (map tails (inits xs))
        ≡⟨⟩
          segs' xs
        ∎

  derivation : mss ≡ mss-fast
  derivation = 
    begin
      mss
    ≡⟨⟩
      maximum ∘ map sum ∘ segs
    ≡⟨⟩
      maximum ∘ map sum ∘ concat ∘ map tails ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (map sum ∘_) segs-is-segs') ⟩
      maximum ∘ map sum ∘ flatten ∘ map tails ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (_∘ map tails ∘ inits) (map-promotion sum)) ⟩
      maximum ∘ flatten ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (_∘ flatten ∘ map (map sum) ∘ map tails ∘ inits) maximum-is-maximum' ⟩
      maximum' ∘ flatten ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (_∘ map (map sum) ∘ map tails ∘ inits) (reduce-promotion _⊔_ 0 ℕ-⊔-is-monoid) ⟩
      maximum' ∘ map maximum' ∘ map (map sum) ∘ map tails ∘ inits
    ≡⟨ cong (maximum' ∘_) (cong (map maximum' ∘_) (cong (_∘  inits) (map-distrib (map sum) tails))) ⟩
      maximum' ∘ map maximum' ∘ map (map sum ∘ tails) ∘ inits
    ≡⟨ cong (maximum' ∘_) (cong (_∘ inits) (map-distrib maximum' (map sum ∘ tails))) ⟩
      maximum' ∘ map (maximum' ∘ map sum ∘ tails) ∘ inits
    ≡⟨ cong (_∘ map (maximum' ∘ map sum ∘ tails) ∘ inits) (sym maximum-is-maximum') ⟩
      maximum ∘ map (maximum' ∘ map sum ∘ tails) ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (_∘ inits) (cong map (cong (maximum' ∘_) (cong (_∘ tails) (cong map sum-is-sum'))))) ⟩
      maximum ∘ map (maximum' ∘ map sum' ∘ tails) ∘ inits
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
  -- derivation-alt xs = ?
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
  --   mss-is-max = ?
  --   mss-exists : ∀ {xs} → ∃[ ys ] ys ⊆ xs × sum ys ≡ mss xs
  --   mss-exists = ?

module BMF2-1 where

  open import Data.Product using (_×_; _,_; Σ-syntax; proj₁)
  open import Data.List using (List; []; _∷_; [_]; _++_)
  import Data.List using (map)

  -- this reduce works on non-empty lists
  -- remark: 'Σ[ xs ∈ List A ] xs ≢ []' means
  --   those 'xs ∈ List A' such that 'xs ≢ []'
  reduce : ∀ {A : Set}
    → (_⊕_ : A → A → A)
    → Σ[ xs ∈ List A ] xs ≢ []
      ------------------------
    → A
  reduce {A} _⊕_ = λ (xs , N) → helper xs N
    module Reduce where
    helper : (xs : List A) → xs ≢ [] → A
    helper [] N with () ← N refl
    helper (x ∷ []) _ = x
    helper (x ∷ xs@(_ ∷ _)) _ = x ⊕ helper xs (λ())

  -- this map works on non-empty lists
  -- and it produces non-empty lists
  map : ∀ {A B : Set}
    → (f : A → B)
    → Σ[ xs ∈ List A ] xs ≢ []
      ------------------------
    → Σ[ ys ∈ List B ] ys ≢ []
  map f ([] , N) with () ← N refl
  map f (x ∷ xs , _) = f x ∷ Data.List.map f xs , λ()

  -- 1. prove 'split' is a homomorphism
  split : ∀ {A : Set} → Σ[ xs ∈ List A ] xs ≢ [] → List A × A
  split = reduce (λ (xs , x) (ys , y) → (xs ++ [ x ] ++ ys , y)) ∘ map λ x → ([] , x)

  -- to verify your 'split' is correct. after defining 'split', proving the following
  -- should be as easy as filling in 'refl'.
  split-is-correct : split (1 ∷ 2 ∷ 3 ∷ 4 ∷ [] , λ()) ≡ (1 ∷ 2 ∷ 3 ∷ [] , 4)
  split-is-correct = refl

  -- bonus: find a proper way to prove your split is indeed correct:
  -- split-is-indeed-correct : ∀ {A} xs
  --   → let (ys , z) = split {A} xs
  --     in proj₁ xs ≡ ys ++ [ z ]

  -- 2. prove 'init' is not a homomorphism
  init : ∀ {A : Set} → Σ[ xs ∈ List A ] xs ≢ [] → List A
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

  -- init-is-not-homomorphism : ∀ {A} {f g} → init {A} ≢ reduce f ∘ map g
  -- init-is-not-homomorphism = ?

  -- Proof in natural language:
  -- If init is a homomorphism, we'll have:
  --   init (xs ++ ys) === (init xs) ⊘ (init ys)
  -- However, init (xs ++ ys) contains element `last xs`, which is in neither `init xs` nor `init ys`.
  -- So, we cannot found a ⊘ which meets the above equation.
  -- Thus, init is not a homomorphism.

  -- Hint: you might want to follow this guideline below if you get stuck.
  --
  -- Step 1: interpret the theorem
  --   init {A} ≢ reduce f ∘ map g
  -- is just another way of saying
  --   init {A} ≡ reduce f ∘ map g → ⊥
  -- (proof by contradiction)
  --
  -- Step 2: get your premise
  -- You want to derive contradiction from the premise, so the first thing
  -- to do is get the premise (add it as an argument):
  --   init-is-not-homomorphism E = ?
  -- Now 'E' is our premise, with the type 'init {A} ≡ reduce f ∘ map g'
  --
  -- Step 3: derive absurd results
  -- Pass in some example to your premise 'E', and try to get some absurd
  -- results such as 'H : 0 ≡ 42'.
  --
  -- Step 4: make use of that absurd result
  -- Use the result 'H' from Step 3, apply it to '(λ())':
  --   (λ()) H
  -- Just use this expression as the return value. This should do the trick,
  -- because "ex falso quodlibet", or "From falsehood, anything follows."

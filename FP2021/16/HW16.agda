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
  open import Data.Nat.Properties using (+-distribˡ-⊔; +-distribʳ-⊔; +-identityʳ; ⊔-identityʳ; +-assoc)
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

  flatten : {A : Set} → List (List A) → List A
  flatten = reduce _++_ [] List-++-is-monoid

  map-promotion : ∀{A B : Set} (f : A → B) → map f ∘ flatten ≡ flatten ∘ map (map f)
  map-promotion = {!   !}

  reduce-promotion : ∀{A : Set} (_⊕_ : A → A → A) (e : A)(p : IsMonoid e _⊕_) → reduce _⊕_ e p ∘ flatten ≡ reduce _⊕_ e p ∘ map (reduce _⊕_ e p)
  reduce-promotion = {!   !}

  acc-lemma : ∀{A : Set} (_⊕_ : A → A → A) (e : A) → scanl _⊕_ e ≡ map (foldl _⊕_ e) ∘ inits
  acc-lemma = {!   !}

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

  concat-is-reducable : concat ≡ reduce _++_ [] List-++-is-monoid
  concat-is-reducable = sym (reduce-is-foldr _++_ [] List-++-is-monoid)

  concat-is-flatten : concat ≡ flatten
  concat-is-flatten = concat-is-reducable

  sum-is-reducable : sum ≡ reduce _+_ 0 ℕ-add-is-monoid
  sum-is-reducable = sym (reduce-is-foldr _+_ 0 ℕ-add-is-monoid)

  reduce-is-foldl : ∀{A : Set} → (_⊕_ : A → A → A) → (e : A) → (p : IsMonoid e _⊕_) → reduce _⊕_ e p ≡ foldl _⊕_ e
  reduce-is-foldl {A} _⊕_ e p = extensionality lemma
    where
      lemma : (xs : List A) → reduce _⊕_ e p xs ≡ foldl _⊕_ e xs
      lemma [] = refl
      lemma (x ∷ xs) = {!   !}

  ∘-assoc : ∀{ℓ ℓ' ℓ'' ℓ'''}{A : Set ℓ}{B : Set ℓ'}{C : Set ℓ''}{D : Set ℓ'''}(f : C → D)(g : B → C)(h : A → B) → (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
  ∘-assoc f g h = refl

  R-Dist : ∀{A : Set} (_⊕_ : A → A → A)(_⊗_ : A → A → A) → Set
  R-Dist {A} _⊕_ _⊗_ = ∀ (a b c : A) → (a ⊕ b) ⊗ c ≡ (a ⊗ c) ⊕ (b ⊕ c)

  horner-rule : ∀{A : Set} (_⊕_ : A → A → A) (e-⊕ : A)(_⊗_ : A → A → A) (e-⊗ : A)
    → (p : IsMonoid e-⊕ _⊕_)
    → (q : IsMonoid e-⊗ _⊗_)
    → (rdist : R-Dist _⊕_ _⊗_)
    -----------------------------
    → reduce _⊕_ e-⊕ p ∘ map (reduce _⊗_ e-⊗ q) ∘ tails ≡ foldl (λ a b → (a ⊗ b) ⊕ e-⊗ ) e-⊗
  horner-rule = {!   !}

  fuckful-rdist = R-Dist _⊔_ _+_
  fuckful-rdist = ?

  derivation : mss ≡ mss-fast
  derivation = 
    begin
      mss
    ≡⟨⟩
      maximum ∘ map sum ∘ segs
    ≡⟨⟩
      maximum ∘ map sum ∘ concat ∘ map tails ∘ inits
    ≡⟨ {!   !} ⟩
      maximum ∘ map sum ∘ flatten ∘ map tails ∘ inits
    -- ≡⟨  ⟩
    -- ≡⟨  ⟩
    ≡⟨ {!   !} ⟩
      maximum ∘ map (reduce _⊔_ 0 ℕ-⊔-is-monoid ∘ map (reduce _+_ 0 ℕ-add-is-monoid) ∘ tails) ∘ inits
    ≡⟨ cong (maximum ∘_) (cong (_∘ inits) ( {! horner-rule _⊔_ 0 _+_ 0 ℕ-⊔-is-monoid ℕ-add-is-monoid  !} )) ⟩
    --   maximum ∘ map (reduce _⊙_ 0 ℕ-⊙-is-monoid) ∘ inits
    -- ≡⟨ cong (maximum ∘_) (cong (_∘ inits) (cong map (reduce-is-foldl _⊙_ 0 ℕ-⊙-is-monoid))) ⟩
      maximum ∘ map (foldl _⊙_ 0) ∘ inits
    ≡⟨ cong (maximum ∘_) (sym (acc-lemma _⊙_ 0)) ⟩
      maximum ∘ (scanl _⊙_ 0)
    ≡⟨⟩
      mss-fast
    ∎

  -- note: it is possible to avoid extensionality and instead prove the following
  --
  -- derivation-alt : ∀ xs → mss xs ≡ mss-fast xs
  -- derivation-alt xs =
  --   begin
  --     mss xs
  --   ≡⟨⟩
  --     maximum (map sum (segs xs))
  --   ≡⟨⟩
  --     maximum (map sum (concat (map tails (inits xs))))
  --   ≡⟨ cong (λ x → maximum (map sum x)) (cong-app concat-is-flatten (map tails (inits xs))) ⟩
  --     maximum (map sum (flatten (map tails (inits xs))))
  --   ≡⟨ {!   !} ⟩
  --     mss-fast xs
  --   ∎
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
  split = reduce {!   !} ∘ map {!   !}

  -- to verify your 'split' is correct. after defining 'split', proving the following
  -- should be as easy as filling in 'refl'.
  split-is-correct : split (1 ∷ 2 ∷ 3 ∷ 4 ∷ [] , λ()) ≡ (1 ∷ 2 ∷ 3 ∷ [] , 4)
  split-is-correct = {!   !}

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

  init-is-not-homomorphism : ∀ {A} {f g} → init {A} ≢ reduce f ∘ map g
  init-is-not-homomorphism = {!   !}

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

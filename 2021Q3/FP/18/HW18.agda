module HW18 where

-- how to input '≗': type \=o
-- Tips: 'f ≗ g' is the same as '∀ xs → f x ≡ g x'

open import Function using (_∘_)
open import Data.List using ([]; _∷_; foldr; map)
open import Data.List.Properties using (foldr-fusion; map-is-foldr)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

foldr-map-fusion : ∀ {A : Set} {B : Set} {C : Set}
  → (f : A → B)
  → (_⊕_ : B → C → C)
  → (e : C)
  → foldr _⊕_ e ∘ map f ≗ foldr (λ a r → f a ⊕ r) e
foldr-map-fusion f _⊕_ e xs = begin
  (foldr _⊕_ e ∘ map f) xs ≡⟨ cong (foldr _⊕_ e) (map-is-foldr xs) ⟩
  (foldr _⊕_ e ∘ foldr (λ x ys → f x ∷ ys) []) xs ≡⟨ foldr-fusion (foldr _⊕_ e) [] (λ x y → refl) xs ⟩
  foldr (λ a r → f a ⊕ r) e xs ∎

map-composition : ∀ {A : Set} {B : Set} {C : Set}
  → (f : B → C)
  → (g : A → B)
  → map f ∘ map g ≗ map (f ∘ g)
map-composition f g xs = begin
  (map f ∘ map g) xs ≡⟨ map-is-foldr (map g xs) ⟩
  (foldr (λ x ys → f x ∷ ys) [] ∘ map g) xs ≡⟨ foldr-map-fusion g (λ x ys → f x ∷ ys) [] xs ⟩
  foldr (λ x ys → (f ∘ g) x ∷ ys) [] xs ≡⟨ sym (map-is-foldr xs) ⟩
  map (f ∘ g) xs ∎

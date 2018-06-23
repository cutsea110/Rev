module Rev where

open import Function
open import Relation.Binary.PropositionalEquality

data List (A : Set) : Set where
  [] : List A
  _∷_ : A -> List A -> List A

snoc : {A : Set} → List A → A → List A
snoc [] y = y ∷ [] 
snoc (x ∷ xs) y = x ∷ snoc xs  y

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = snoc (reverse xs) x

lemma : {A : Set}(x : A)(xs : List A) → reverse (snoc xs x) ≡ x ∷ reverse xs
lemma x [] = refl
lemma x (y ∷ ys) rewrite lemma x ys = refl

reverse∘reverse≡id : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
reverse∘reverse≡id [] = refl
reverse∘reverse≡id (x ∷ xs) rewrite lemma x (reverse xs) = cong (x ∷_) (reverse∘reverse≡id xs)

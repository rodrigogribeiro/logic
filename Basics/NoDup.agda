
open import Data.Empty using (⊥-elim)
open import Data.List
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Basics.NoDup {A : Set}(_≟_ : Decidable {A = A} _≡_) where

open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality
open import Basics.Subset


IsProp : Set → Set
IsProp P = (p1 p2 : P) → p1 ≡ p2

NoDup : List A → Set
NoDup xs = (x : A) → IsProp (x ∈ xs)

NoDup-∷ : ∀ {xs x} → NoDup xs → ¬ x ∈ xs → NoDup (x ∷ xs)
NoDup-∷ nDupxs ¬x∈xs y here here = refl
NoDup-∷ nDupxs ¬x∈xs y here (there p2) = ⊥-elim (¬x∈xs p2)
NoDup-∷ nDupxs ¬x∈xs y (there p1) here = ⊥-elim (¬x∈xs p1)
NoDup-∷ nDupxs ¬x∈xs y (there p1) (there p2) rewrite nDupxs _ p1 p2 = refl


≈-∈' : ∀ {xs ys}{x : A} → ys ≈ xs → x ∈ xs → ys ≈ (x ∷ xs)
≈-∈' ys≈xs here y = record { to = λ{ here → there (_⇔_.to (ys≈xs y) here)
                                   ; (there q) → there (_⇔_.to (ys≈xs y) (there q)) }
                           ; from = λ{ here → _⇔_.from (ys≈xs _) here
                                     ; (there q) → _⇔_.from (ys≈xs y) q } }
≈-∈' ys≈xs (there p) y = record { to = λ{ here → there (_⇔_.to (ys≈xs y) here)
                                        ; (there q) → there (_⇔_.to (ys≈xs y) (there q)) }
                                ; from = λ{ here → _⇔_.from (ys≈xs _) (there p)
                                          ; (there q) → _⇔_.from (ys≈xs y) q } }

open MembershipDec _≟_

noDup : (xs : List A) → ∃ (λ ys → NoDup ys × ys ≈ xs)
noDup [] = [] , (λ x x₁ ()) , λ ys → ≈-refl ys
noDup (x ∷ xs) with x ∈? xs | noDup xs
...| yes p | ys , noDupys , ys≈xs = ys , noDupys , ≈-∈' ys≈xs p
...| no  q | ys , noDupys , ys≈xs = x ∷ ys , NoDup-∷ noDupys (λ k → ⊥-elim (q (_⇔_.to (ys≈xs x) k))) , ≈-∷ ys≈xs

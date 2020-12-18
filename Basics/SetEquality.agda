module Basics.SetEquality where

open import Basics.Bijection
open import Basics.Membership

open import Data.Empty
open import Data.List
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no)


-- set equality for lists

private
  variable
    A : Set

infix 4 _≈_

_≈_ : List A → List A → Set
xs ≈ ys = ∀ x → x ∈ xs ⇔ x ∈ ys

-- some simple lemmas

open ⇔-Reasoning

++-comm : ∀ (xs ys : List A) → xs ++ ys ≈ ys ++ xs
++-comm xs ys = λ z →
     begin
       z ∈ (xs ++ ys)        ⇔⟨ ∈-++ xs ys z ⟩
       ((z ∈ xs) ⊎ (z ∈ ys)) ⇔⟨ ⊎-comm ⟩
       ((z ∈ ys) ⊎ (z ∈ xs)) ⇔⟨ ⇔-sym (∈-++ ys xs z) ⟩
       z ∈ (ys ++ xs)
     ∎

≈-refl : ∀ {xs : List A} → xs ≈ xs
≈-refl = λ x → record { to = λ z → z ; from = λ z → z }

≈-sym : ∀ {xs ys : List A} → xs ≈ ys → ys ≈ xs
≈-sym p = λ x → record { to = _⇔_.from (p x) ; from = _⇔_.to (p x) }

≈-trans : ∀ {xs ys zs : List A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans p q = λ x →
                  record
                  { to = λ z → _⇔_.to (q x) (_⇔_.to (p x) z)
                  ; from = λ z → _⇔_.from (p x) (_⇔_.from (q x) z)
                  }

≈-∷ : ∀ {xs ys : List A}{x : A} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
≈-∷ {x = x} p = λ z →
  record { to = λ{ here → here
                 ; (there q) → there (_⇔_.to (p z) q) }
         ; from = λ{ here → here
                   ; (there q) → there (_⇔_.from (p z) q) } }


≈-∈ : ∀ {xs ys : List A}{x : A} → xs ≈ ys → x ∈ xs → x ∈ ys
≈-∈ xs≈ys here = _⇔_.to (xs≈ys _) here
≈-∈ xs≈ys (there p) = _⇔_.to (xs≈ys _) (there p)

∈-≈-elim : ∀ {xs}{x : A} → x ∈ xs → xs ≈ (x ∷ xs)
∈-≈-elim here z = record { to = there ; from = λ{ here → here ; (there q) → q } }
∈-≈-elim (there p) z = record { to = there ; from = λ{ here → there p ; (there q) → q} }

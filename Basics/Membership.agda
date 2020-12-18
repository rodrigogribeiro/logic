module Basics.Membership where

open import Basics.Bijection

open import Data.Empty
open import Data.List
open import Data.Sum
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)

-- list membership

infix 6 _∈_

data _∈_ {A : Set}(x : A) : List A → Set where
  here  : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y ys} → x ∈ ys → x ∈ (y ∷ ys)

_∉_ : {A : Set}(x : A) → List A → Set
x ∉ xs = ¬ (x ∈ xs)

private
  variable
    A : Set

∈-[]⇔⊥ : ∀ (x : A) → x ∈ [] ⇔ ⊥
∈-[]⇔⊥ x = record { to = λ () ; from = λ () }


-- lemmas about list membership

open ⇔-Reasoning

∈-∷-inv : ∀ (xs : List A){x x' : A} → (x ∈ (x' ∷ xs)) ⇔ (x ≡ x' ⊎ x ∈ xs)
∈-∷-inv [] = record { to = λ{ here → inj₁ refl ; (there ()) }
                    ; from = λ{ (inj₁ refl) → here ; (inj₂ ())} }
∈-∷-inv (x ∷ xs) = record { to = λ { here → inj₁ refl ; (there p) → inj₂ p }
                          ; from = λ{ (inj₁ refl) → here ; (inj₂ q) → there q } }

∈-++ : ∀ (xs ys : List A)(x : A) → x ∈ (xs ++ ys) ⇔ (x ∈ xs ⊎ x ∈ ys)
∈-++ [] ys x
  = begin
      x ∈ ys                ⇔⟨ ⇔-sym ⊎-left-identity ⟩
      (⊥ ⊎ (x ∈ ys))        ⇔⟨ ⊎-cong (⇔-sym (∈-[]⇔⊥ x)) ⇔-refl ⟩
      ((x ∈ []) ⊎ (x ∈ ys))
    ∎
∈-++ (x' ∷ xs) ys x
  = begin
      x ∈ (x' ∷ xs ++ ys)             ⇔⟨ ∈-∷-inv (xs ++ ys) ⟩
      (x ≡ x' ⊎ (x ∈ (xs ++ ys)))     ⇔⟨ ⊎-cong ⇔-refl (∈-++ xs ys x) ⟩
     (x ≡ x' ⊎ ((x ∈ xs) ⊎ (x ∈ ys))) ⇔⟨ ⊎-assoc ⟩
     ((x ≡ x' ⊎ (x ∈ xs)) ⊎ (x ∈ ys)) ⇔⟨ ⊎-cong (⇔-sym (∈-∷-inv xs)) ⇔-refl ⟩
     ((x ∈ (x' ∷ xs)) ⊎ (x ∈ ys))
    ∎

-- decidability of list membership

module MembershipDec (_≟_ : Decidable {A = A} _≡_) where

  private
    lemma : ∀ {x y : A}{ys} → x ∈ (y ∷ ys) → x ≡ y ⊎ x ∈ ys
    lemma {ys = ys} here = inj₁ refl
    lemma {ys = ys} (there p) = inj₂ p

  _∈?_ : ∀ (x : A)(xs : List A) → Dec (x ∈ xs)
  x ∈? [] = no (λ ())
  x ∈? (y ∷ ys) with x ≟ y
  ...| yes p rewrite p = yes here
  ...| no  q with x ∈? ys
  ... | yes p' = yes (there p')
  ... | no q' = no ([ q , q' ]′ ∘ lemma)

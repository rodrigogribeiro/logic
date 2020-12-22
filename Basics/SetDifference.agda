open import Relation.Binary as Bin hiding (_⇔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable

module Basics.SetDifference {A : Set}(_≟_ : Bin.Decidable {A = A} _≡_) where

open import Data.Empty
open import Data.List
open import Data.Sum
open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality

-- definition of the set difference operation

infixr 4 _⊝_

_⊝_ : List A → A → List A
[] ⊝ y = []
x ∷ xs ⊝ y with x ≟ y
...| yes p = xs ⊝ y
...| no  p = x ∷ (xs ⊝ y)

∈-⊝-≢ : ∀ {xs : List A}{x y} → x ∈ xs → x ≢ y → x ∈ (xs ⊝ y)
∈-⊝-≢ {x ∷ xs}{x}{y} here neq with x ≟ y
...| yes q rewrite q = ⊥-elim (neq refl)
...| no  q = here
∈-⊝-≢ {x ∷ xs}{x1}{y} (there p) neq with x ≟ y
...| yes q rewrite q = ∈-⊝-≢ p neq
...| no  q = there (∈-⊝-≢ p neq)

open ⇔-Reasoning
open MembershipDec _≟_


-- auxiliar properties to relate equality and difference

private
  ∈-⇔-inv : ∀ (ys : List A)(z x : A)
            → ¬ (x ≡ z)
            → z ∈ ys ⇔ (z ∈ (x ∷ ys))
  ∈-⇔-inv ys z x eq
    = record { to = there
             ; from = λ{ here → ⊥-elim (eq refl)
                       ; (there q) → q} }

  ∈-⊝ : ∀ (ys : List A)(z x : A)
        → ¬ (x ≡ z) → z ∈ (ys ⊝ x) ⇔ z ∈ ys
  ∈-⊝ [] z x eq = ⇔-refl
  ∈-⊝ (x₁ ∷ ys) z x eq with x₁ ≟ x
  ...| yes q rewrite q
    = begin
        z ∈ (ys ⊝ x) ⇔⟨ ∈-⊝ ys z x eq ⟩
        z ∈ ys       ⇔⟨ ∈-⇔-inv ys z x eq ⟩
        z ∈ (x ∷ ys)
       ∎
  ...| no  q with x₁ ≟ z
  ...   | yes q' rewrite q' = record { to = λ _ → here
                                     ; from = λ _ → here }
  ...   | no  q'
    = begin
        z ∈ (x₁ ∷ (ys ⊝ x)) ⇔⟨ ⇔-sym (∈-⇔-inv (ys ⊝ x) z x₁ q') ⟩
        z ∈ (ys ⊝ x)        ⇔⟨ ∈-⊝ ys z x eq ⟩
        z ∈ ys              ⇔⟨ record { to = there
                                      ; from = λ{ here → ⊥-elim (q' refl)
                                                ; (there k) → k } } ⟩
        z ∈ (x₁ ∷ ys)
       ∎ 


-- congruence lemma for difference

≈-++-⊝ : ∀ {xs ys : List A}{x} → x ∈ xs → xs ++ (ys ⊝ x) ≈ xs ++ ys
≈-++-⊝ {xs = xs} {ys = []} {x} p = ≈-refl
≈-++-⊝ {xs = xs} {ys = x₁ ∷ ys} {x} p z with x₁ ≟ x | x ≟ z
...| yes q | yes q' rewrite q | q' = record { to = λ _ → ∈-++-inj-left p
                                            ; from = λ _ → ∈-++-inj-left p }
...| yes q | no  q' rewrite q
  = begin
      z ∈ (xs ++ (ys ⊝ x))        ⇔⟨ ∈-++ xs (ys ⊝ x) z ⟩
      ((z ∈ xs) ⊎ (z ∈ (ys ⊝ x))) ⇔⟨ ⊎-cong ⇔-refl (∈-⊝ ys _ _ q') ⟩
      ((z ∈ xs) ⊎ (z ∈ ys))       ⇔⟨ ⊎-cong ⇔-refl (∈-⇔-inv ys z x q') ⟩
      ((z ∈ xs) ⊎ (z ∈ (x ∷ ys))) ⇔⟨ ⇔-sym (∈-++ xs (x ∷ ys) z) ⟩
      z ∈ (xs ++ (x ∷ ys))
    ∎
...| no  q | yes q' rewrite q' = record { to = λ _ → ∈-++-inj-left p
                                        ; from = λ _ → ∈-++-inj-left p }
...| no  q | no  q' with x₁ ≟ z
...|   yes k rewrite k = record { to = λ _ → ∈-++-inj-right here
                                ; from = λ _ → ∈-++-inj-right here }
...|   no  k
  = begin
      z ∈ (xs ++ x₁ ∷ (ys ⊝ x))          ⇔⟨ ∈-++ xs (x₁ ∷ (ys ⊝ x)) z ⟩
      ((z ∈ xs) ⊎ (z ∈ (x₁ ∷ (ys ⊝ x)))) ⇔⟨ ⊎-cong ⇔-refl (⇔-sym (∈-⇔-inv (ys ⊝ x) z x₁ k)) ⟩
      ((z ∈ xs) ⊎ (z ∈ (ys ⊝ x)))        ⇔⟨ ⊎-cong ⇔-refl (∈-⊝ ys z x q') ⟩
      ((z ∈ xs) ⊎ (z ∈ ys))              ⇔⟨ ⊎-cong ⇔-refl (record { to = there
                                                                  ; from = λ{ here → ⊥-elim (k refl)
                                                                            ; (there j) → j } }) ⟩
      ((z ∈ xs) ⊎ (z ∈ (x₁ ∷ ys)))       ⇔⟨ ⇔-sym (∈-++ xs (x₁ ∷ ys) z) ⟩
      z ∈ (xs ++ (x₁ ∷ ys))
    ∎

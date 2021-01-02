module Propositional.System.Sequent.Properties.Cut where


open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality
open import Basics.WellFounded
open import Data.List
open import Data.List.Properties
open import Data.Product
open import Propositional.Syntax
open import Propositional.System.Sequent.SequentCalculus
open import Propositional.System.Sequent.Properties.Exchange
open import Propositional.System.Sequent.Properties.Weakening
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Basics.SetDifference ≡-Form
open import Basics.Subset

open MembershipDec ≡-Form

-- lemmas for cut theorem

genCut : ∀ {Γ Γ' C} A → Γ ⇒ A → Γ' ⇒ C → Γ ++ (Γ' ⊝ A) ⇒ C
genCut `⊥ (init x) p2 = ⊥L (∈-++-inj-left x)
genCut {Γ' = Γ'} `⊥ (⇒L {B = B} x p1 p3) p2 = ⇒L (∈-++-inj-left x)
                                                 (weakening ⊆-++-right p1)
                                                 (genCut _ p3 p2)
genCut `⊥ (⊥L x) p2 = ⊥L (∈-++-inj-left x)
genCut {C = C}(A `⊃ A₁) (init x) (init x₁) with ≡-Form C (A `⊃ A₁)
...| yes q rewrite q = init (∈-++-inj-left x)
...| no  q = weakening ⊆-++-left (init (∈-⊝-≢ x₁ q))
genCut (A `⊃ A₁) (init x) (⇒R {B = B} p2) with ≡-Form B (A `⊃ A₁)
...| yes q rewrite q = ⇒R (weakening (⊆-∷-r ⊆-++-right) (init x))
...| no  q = ⇒R (exchange (≈-∷ (≈-sym (≈-++-⊝ x)))
                          (weakening (⊆-∷ ⊆-++-left) p2))
genCut {Γ' = Γ'}(A `⊃ A₁) (init x) (⇒L {A = A₂}{B = B}{C = C} x₁ p2 p3) with ≡-Form (A₂ `⊃ B) (A `⊃ A₁) | ≡-Form C (A `⊃ A₁)
...| yes q | yes q' rewrite (proj₁ (`⊃-inv q)) | (proj₂ (`⊃-inv q)) | q' = weakening ⊆-++-right (init x)
...| no  q | yes q' rewrite q' = weakening ⊆-++-right (init x)
...| yes q | no q'  rewrite (proj₁ (`⊃-inv q)) | (proj₂ (`⊃-inv q))
  = ⇒L (∈-++-inj-left x)
       (weakening (⊆-++-⊝-left x) p2)
       (exchange (≈-sym (≈-∷-++-swap {ys = Γ' ⊝ (A `⊃ A₁)}))
                 (weakening (⊆-++-⊝-≠ (λ ()) x) p3))
...| no  q | no q'  with ≡-Form B (A `⊃ A₁) | ≡-Form A₂ (A `⊃ A₁)
...   | yes a | yes b rewrite a | b = weakening (⊆-++-⊝-head x) p3
...   | yes a | no  b rewrite a = weakening (⊆-++-⊝-head x) p3
...   | no  a | yes b rewrite b = ⇒L (∈-++-inj-right (_⇔_.from (∈-⊝ Γ' ((A `⊃ A₁) `⊃ B) (A `⊃ A₁) (λ ())) x₁))
                                     (weakening (⊆-++-⊝-left x) p2)
                                     (weakening (⊆-∷ (⊆-++-⊝-left x)) p3)
...   | no  a | no  b = ⇒L (∈-++-inj-right (_⇔_.from (∈-⊝ Γ' (A₂ `⊃ B) (A `⊃ A₁) (λ k → q (sym k))) x₁))
                           (weakening (⊆-++-⊝-left x) p2)
                           (weakening (⊆-∷ (⊆-++-⊝-left x)) p3)
genCut (A `⊃ A₁) (init x) (⊥L x₁) = ⊥L (∈-++-inj-right (∈-⊝-≢ x₁ λ ()))
genCut {C = C}(A `⊃ A₁) (⇒R p1) (init x) with ≡-Form C (A `⊃ A₁)
...| yes q rewrite q = weakening ⊆-++-right (⇒R p1)
...| no  q = init (∈-++-inj-right (_⇔_.from (∈-⊝ _ C (A `⊃ A₁) λ k → q (sym k)) x))
genCut {Γ' = Γ'}(A `⊃ A₁) (⇒R p1) (⇒R {A = A₂}{B = B} p2) with ≡-Form A₂ (A `⊃ A₁)
...| yes q rewrite q = ⇒R (exchange (≈-sym (≈-∷-++-swap {ys = Γ' ⊝ (A `⊃ A₁)}))
                                    (weakening ⊆-++-⊝-∷ (genCut _ (⇒R p1) p2)))
...| no  q = ⇒R (exchange (≈-sym (≈-∷-++-swap {ys = Γ' ⊝ (A `⊃ A₁)}))
                          (weakening (⊆-++-⊝-∷-≠ q) (genCut _ (⇒R p1) p2)))
genCut (A `⊃ A₁) (⇒R p1) (⇒L x p2 p3) = {!!}
genCut (A `⊃ A₁) (⇒R p1) (⊥L x) = ⊥L (∈-++-inj-right (_⇔_.from (∈-⊝ _ `⊥ (A `⊃ A₁) (λ ())) x))
genCut (A `⊃ A₁) (⇒L x p1 p3) p2 = {!!}
genCut (A `⊃ A₁) (⊥L x) p2 = ⊥L (∈-++-inj-left x)


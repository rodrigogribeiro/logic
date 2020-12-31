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
...| yes q | no q'   rewrite (proj₁ (`⊃-inv q)) | (proj₂ (`⊃-inv q))
  = ⇒L (∈-++-inj-left x)
       (weakening (⊆-++-⊝-left x) p2)
       (exchange (≈-sym (≈-∷-++-swap {ys = Γ' ⊝ (A `⊃ A₁)}))
                 (weakening (⊆-++-⊝-≠ (λ ()) x) p3))
...| no  q | no q'  = ⇒L (∈-++-inj-right (_⇔_.from (∈-⊝ Γ' _ _ (λ x → q (sym x))) x₁))
                         {!!}
                         (exchange (≈-sym (≈-∷-++-swap {ys = Γ' ⊝ (A `⊃ A₁)}))
                                   (weakening (⊆-++-⊝-≠ {!!} x) p3))
genCut (A `⊃ A₁) (init x) (⊥L x₁) = ⊥L (∈-++-inj-right (∈-⊝-≢ x₁ λ ()))
genCut (A `⊃ A₁) (⇒R p1) p2 = {!!}
genCut (A `⊃ A₁) (⇒L x p1 p3) p2 = {!!}
genCut (A `⊃ A₁) (⊥L x) p2 = ⊥L (∈-++-inj-left x)


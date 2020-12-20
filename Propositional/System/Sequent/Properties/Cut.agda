module Propositional.System.Sequent.Properties.Cut where


open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality
open import Basics.Subset
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

open MembershipDec ≡-Form

-- lemmas for cut theorem

genCut : ∀ {Γ Γ' C} A → Γ ⇒ A → Γ' ⇒ C → Γ ++ (Γ' ⊝ A) ⇒ C
genCut `⊥ (init x) p2 = ⊥L (∈-++-inj-left x)
genCut {Γ' = Γ'} `⊥ (⇒L {B = B} x p1 p3) p2 = ⇒L (∈-++-inj-left x)
                                                 (weakening ⊆-++-right p1)
                                                 (genCut _ p3 p2)
genCut `⊥ (⊥L x) p2 = ⊥L (∈-++-inj-left x)
genCut (A `⊃ A₁) (init x) p2 = {!!}
genCut (A `⊃ A₁) (⇒R p1) p2 = {!!}
genCut (A `⊃ A₁) (⇒L x p1 p3) p2 = {!!}
genCut (A `⊃ A₁) (⊥L x) p2 = ⊥L (∈-++-inj-left x)

-- the cut theorem

-- cut : ∀ {Γ C} A → Γ ⇒ A → (A ∷ Γ) ⇒ C → Γ ⇒ C
-- cut `⊥ (init x) p2 = ⊥L x
-- cut `⊥ (∧L₁ x p1) p2 = ∧L₁ x (cut _ p1 (weakening (⊆-snd _ `⊥ _) p2))
-- cut `⊥ (∧L₂ x p1) p2 = ∧L₂ x (cut _ p1 (weakening (⊆-snd _ `⊥ _) p2))
-- cut `⊥ (⇒L x p1 p3) p2 = ⇒L x p1 (cut _ p3 (weakening (⊆-snd _ `⊥ _) p2))
-- cut `⊥ (∨L x p1 p3) p2 = ∨L x (cut _ p1 (weakening (⊆-snd _ `⊥ _) p2))
--                               (cut _ p3 (weakening (⊆-snd _ `⊥ _) p2))
-- cut `⊥ (⊥L x) p2 = ⊥L x
-- cut `⊥ (structural x p1) p2 = structural x (cut _ p1 (exchange (≈-∷ (≈-sym x)) p2))
-- cut (A `⊃ A₁) (init x) p2 = exchange (≈-sym (∈-≈-elim x)) p2
-- cut (A `⊃ A₁) (∧L₁ x p1) p2 = ∧L₁ x (cut _ p1 (weakening (⊆-snd _ (A `⊃ A₁) _) p2))
-- cut (A `⊃ A₁) (∧L₂ x p1) p2 = ∧L₂ x (cut _ p1 (weakening (⊆-snd _ (A `⊃ A₁) _) p2))
-- cut (A `⊃ A₁) (⇒R p1) (init here) = ⇒R p1
-- cut (A `⊃ A₁) (⇒R p1) (init (there x)) = init x
-- cut (A `⊃ A₁) (⇒R p1) (∧R p2 p3) = ∧R (cut _ (⇒R p1) p2) (cut _ (⇒R p1) p3)
-- cut (A `⊃ A₁) (⇒R p1) (∧L₁ (there x) p2) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (∧L₂ x p2) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (⇒R p2) = ⇒R (cut _ {!p2!} {!!})
-- cut (A `⊃ A₁) (⇒R p1) (⇒L x p2 p3) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (∨R₁ p2) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (∨R₂ p2) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (∨L x p2 p3) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (⊥L x) = {!!}
-- cut (A `⊃ A₁) (⇒R p1) (structural x p2) = {!!}
-- cut (A `⊃ A₁) (⇒L x p1 p3) p2 = {!!}
-- cut (A `⊃ A₁) (∨L x p1 p3) p2 = {!!}
-- cut (A `⊃ A₁) (⊥L x) p2 = {!!}
-- cut (A `⊃ A₁) (structural x p1) p2 = {!!}
-- cut (A `∧ A₁) p1 p2 = {!!}
-- cut (A `∨ A₁) p1 p2 = {!!}

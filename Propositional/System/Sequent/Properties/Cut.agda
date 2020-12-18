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

open import Basics.SetDifference ≡-Form

-- the cut theorem

cut : ∀ {Γ C} A → Γ ⇒ A → (A ∷ Γ) ⇒ C → Γ ⇒ C
cut `⊥ (init x) p2 = ⊥L x
cut `⊥ (∧L₁ x p1) p2 = ∧L₁ x (cut _ p1 (weakening (⊆-snd _ `⊥ _) p2))
cut `⊥ (∧L₂ x p1) p2 = ∧L₂ x (cut _ p1 (weakening (⊆-snd _ `⊥ _) p2))
cut `⊥ (⇒L x p1 p3) p2 = ⇒L x p1 (cut _ p3 (weakening (⊆-snd _ `⊥ _) p2))
cut `⊥ (∨L x p1 p3) p2 = ∨L x (cut _ p1 (weakening (⊆-snd _ `⊥ _) p2))
                              (cut _ p3 (weakening (⊆-snd _ `⊥ _) p2))
cut `⊥ (⊥L x) p2 = ⊥L x
cut `⊥ (structural x p1) p2 = structural x (cut _ p1 (exchange (≈-∷ (≈-sym x)) p2))
cut `⊤ (init x) p2 = exchange (≈-sym (∈-≈-elim x)) p2
cut `⊤ (∧L₁ x p1) p2 = ∧L₁ x (cut _ p1 (weakening (⊆-snd _ `⊤ _) p2))
cut `⊤ (∧L₂ x p1) p2 =  ∧L₂ x (cut _ p1 (weakening (⊆-snd _ `⊤ _) p2))
cut `⊤ (⇒L x p1 p3) p2 = ⇒L x p1 (cut _ p3 (weakening (⊆-snd _ `⊤ _) p2))
cut `⊤ (∨L x p1 p3) p2 = ∨L x (cut _ p1 (weakening (⊆-snd _ `⊤ _) p2))
                              (cut _ p3 (weakening (⊆-snd _ `⊤ _) p2))
cut `⊤ ⊤R p2 = {!!}
cut `⊤ (⊥L x) p2 = ⊥L x
cut `⊤ (structural x p1) p2 = structural x (cut _ p1 (exchange (≈-∷ (≈-sym x)) p2))
cut (A `⊃ A₁) p1 p2 = {!!}
cut (A `∧ A₁) p1 p2 = {!!}
cut (A `∨ A₁) p1 p2 = {!!}

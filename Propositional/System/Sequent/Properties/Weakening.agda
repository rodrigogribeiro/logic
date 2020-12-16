module Propositional.System.Sequent.Properties.Weakening where

open import Basics.Bijection   using (⇔-sym)
open import Basics.Membership  using (_∈_ ; here ; there)
open import Basics.SetEquality using (_≈_ ; ≈-sym ; ≈-refl)
open import Basics.Subset
open import Data.List
open import Propositional.Syntax
open import Propositional.System.Sequent.SequentCalculus

weakening : ∀ {Γ Γ' : Ctx}{C : Form}
            → Γ ⊆ Γ'
            → Γ ⇒ C
            → Γ' ⇒ C
weakening Γ⊆Γ' (init x) = init (Γ⊆Γ' _ x)
weakening Γ⊆Γ' (∧R p p₁) = ∧R (weakening Γ⊆Γ' p) (weakening Γ⊆Γ' p₁)
weakening Γ⊆Γ' (∧L₁ x p) = ∧L₁ (Γ⊆Γ' _ x) (weakening (⊆-∷ Γ⊆Γ') p)
weakening Γ⊆Γ' (∧L₂ x p) = ∧L₂ (Γ⊆Γ' _ x) (weakening (⊆-∷ Γ⊆Γ') p)
weakening Γ⊆Γ' (⇒R p) = ⇒R (weakening (⊆-∷ Γ⊆Γ') p)
weakening Γ⊆Γ' (⇒L x p p₁) = ⇒L (Γ⊆Γ' _ x) (weakening Γ⊆Γ' p) (weakening (⊆-∷ Γ⊆Γ') p₁)
weakening Γ⊆Γ' (∨R₁ p) = ∨R₁ (weakening Γ⊆Γ' p)
weakening Γ⊆Γ' (∨R₂ p) = ∨R₂ (weakening Γ⊆Γ' p)
weakening Γ⊆Γ' (∨L x p p₁) = ∨L (Γ⊆Γ' _ x) (weakening (⊆-∷ Γ⊆Γ') p) (weakening (⊆-∷ Γ⊆Γ') p₁)
weakening Γ⊆Γ' ⊤R = ⊤R
weakening Γ⊆Γ' (⊥L x) = ⊥L (Γ⊆Γ' _ x)
weakening Γ⊆Γ' (structural x p) = weakening (⊆-cong (≈-sym x) ≈-refl Γ⊆Γ') p

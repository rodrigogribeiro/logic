module Propositional.System.Sequent.Properties.Contraction where

open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality
open import Data.List
open import Data.Product
open import Propositional.Syntax
open import Propositional.System.Sequent.SequentCalculus
open import Propositional.System.Sequent.Properties.Exchange


open import Basics.NoDup ≡-Form


contraction : ∀ {Γ C} → Γ ⇒ C → let r = noDup Γ in (proj₁ r) ⇒ C
contraction {Γ}(init x) with noDup Γ
...| Γ' , nds , Γ≈Γ' = init (_⇔_.from (Γ≈Γ' _) x)
contraction (∧R p p₁) = ∧R (contraction p) (contraction p₁)
contraction {Γ} (∧L₁ x p) with noDup Γ
...| Γ' , nds , Γ≈Γ' = ∧L₁ (_⇔_.from (Γ≈Γ' _) x) {!contraction p!}
contraction (∧L₂ x p) = {!!}
contraction (⇒R p) = {!!}
contraction (⇒L x p p₁) = {!!}
contraction (∨R₁ p) = {!!}
contraction (∨R₂ p) = {!!}
contraction (∨L x p p₁) = {!!}
contraction ⊤R = ⊤R
contraction (⊥L x) = {!!}
contraction (structural x p) = {!!}

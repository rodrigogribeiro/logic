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
contraction {Γ} p with noDup Γ
...| Γ' , nodup , Γ≈Γ' = exchange (≈-sym Γ≈Γ') p

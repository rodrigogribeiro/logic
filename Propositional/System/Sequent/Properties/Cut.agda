module Propositional.System.Sequent.Properties.Cut where


open import Basics.Bijection
open import Basics.Induction
open import Basics.Membership
open import Basics.SetEquality
open import Basics.WellFounded
open import Data.List
open import Data.Product
open import Propositional.Syntax
open import Propositional.System.Sequent.SequentCalculus

cut : ∀ {Γ A C} → Γ ⇒ A → (A ∷ Γ) ⇒ C → Γ ⇒ C
cut p1 p2 = build {!InverseImage.!} {!!} {!!} {!!}

module Propositional.System.Sequent.SequentCalculus where

open import Basics.SetEquality
open import Basics.Membership
open import Data.List
open import Data.Nat
open import Propositional.Syntax

-- sequent calculus definition

infix 4 _⇒_

data _⇒_ : Ctx → Form → Set where
  init : ∀ {Γ A} → A ∈ Γ → Γ ⇒ A
  ⇒R : ∀ {Γ A B}
    → A ∷ Γ ⇒ B
    → Γ ⇒ A `⊃ B
  ⇒L : ∀ {Γ A B C}
    → (A `⊃ B) ∈ Γ
    → Γ ⇒ A
    → B ∷ Γ ⇒ C
    → Γ ⇒ C
  ⊥L : ∀ {Γ C}
    → `⊥ ∈ Γ
    → Γ ⇒ C

-- derivation size

deriv-size : ∀ {Γ C} → Γ ⇒ C → ℕ
deriv-size (init x) = 0
deriv-size (⇒R p) = 1 + deriv-size p
deriv-size (⇒L x p p₁) = 1 + deriv-size p ⊔ deriv-size p₁
deriv-size (⊥L _) = 0

module Propositional.Syntax where

open import Data.List
open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (Decidable)
open import Relation.Nullary

-- definition of formula syntax

data Form : Set where
  `⊥  : Form
  `⊤  : Form
  _`⊃_ : Form → Form → Form
  _`∧_ : Form → Form → Form
  _`∨_ : Form → Form → Form

-- definition of formula contexts

Ctx : Set
Ctx = List Form

-- definition of the formula size

form-size : Form → ℕ
form-size `⊥ = 0
form-size `⊤ = 0
form-size (f `⊃ f') = 1 + form-size f ⊔ form-size f'
form-size (f `∧ f') = 1 + form-size f ⊔ form-size f'
form-size (f `∨ f') = 1 + form-size f ⊔ form-size f'

-- decidability test

`⊃-inv : ∀ {a a' b b' : Form} → (a `⊃ b) ≡ (a' `⊃ b') → a ≡ a' × b ≡ b'
`⊃-inv refl = refl , refl

`∧-inv : ∀ {a a' b b' : Form} → (a `∧ b) ≡ (a' `∧ b') → a ≡ a' × b ≡ b'
`∧-inv refl = refl , refl

`∨-inv : ∀ {a a' b b' : Form} → (a `∨ b) ≡ (a' `∨ b') → a ≡ a' × b ≡ b'
`∨-inv refl = refl , refl


≡-Form : Decidable {A = Form} _≡_
≡-Form `⊥ `⊥ = yes refl
≡-Form `⊥ `⊤ = no (λ ())
≡-Form `⊥ (b `⊃ b₁) = no (λ ())
≡-Form `⊥ (b `∧ b₁) = no (λ ())
≡-Form `⊥ (b `∨ b₁) = no (λ ())
≡-Form `⊤ `⊥ = no (λ ())
≡-Form `⊤ `⊤ = yes refl
≡-Form `⊤ (b `⊃ b₁) = no (λ ())
≡-Form `⊤ (b `∧ b₁) = no (λ ())
≡-Form `⊤ (b `∨ b₁) = no (λ ())
≡-Form (a `⊃ a₁) `⊥ = no (λ ())
≡-Form (a `⊃ a₁) `⊤ = no (λ ())
≡-Form (a `⊃ a₁) (b `⊃ b₁) with ≡-Form a b | ≡-Form a₁ b₁
...| yes refl | yes refl = yes refl
...| no p     | _        = no (p ∘ proj₁ ∘ `⊃-inv)
...| _        | no q     = no (q ∘ proj₂ ∘ `⊃-inv)
≡-Form (a `⊃ a₁) (b `∧ b₁) = no (λ ())
≡-Form (a `⊃ a₁) (b `∨ b₁) = no (λ ())
≡-Form (a `∧ a₁) `⊥ = no (λ ())
≡-Form (a `∧ a₁) `⊤ = no (λ ())
≡-Form (a `∧ a₁) (b `⊃ b₁) = no (λ ())
≡-Form (a `∧ a₁) (b `∧ b₁)  with ≡-Form a b | ≡-Form a₁ b₁
...| yes refl | yes refl = yes refl
...| no p     | _        = no (p ∘ proj₁ ∘ `∧-inv)
...| _        | no q     = no (q ∘ proj₂ ∘ `∧-inv)
≡-Form (a `∧ a₁) (b `∨ b₁) = no (λ ())
≡-Form (a `∨ a₁) `⊥ = no (λ ())
≡-Form (a `∨ a₁) `⊤ = no (λ ())
≡-Form (a `∨ a₁) (b `⊃ b₁) = no (λ ())
≡-Form (a `∨ a₁) (b `∧ b₁) = no (λ ())
≡-Form (a `∨ a₁) (b `∨ b₁)  with ≡-Form a b | ≡-Form a₁ b₁
...| yes refl | yes refl = yes refl
...| no p     | _        = no (p ∘ proj₁ ∘ `∨-inv)
...| _        | no q     = no (q ∘ proj₂ ∘ `∨-inv)

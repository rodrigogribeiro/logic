open import Relation.Binary as Bin
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable

module Basics.SetDifference {A : Set}(_≟_ : Bin.Decidable {A = A} _≡_) where

open import Data.Empty
open import Data.List
open import Basics.Membership

-- definition of the set difference operation

infixr 4 _⊝_

_⊝_ : List A → A → List A
[] ⊝ y = []
x ∷ xs ⊝ y with x ≟ y
...| yes p = xs ⊝ y
...| no  p = x ∷ (xs ⊝ y)

∈-⊝-≢ : ∀ {xs : List A}{x y} → x ∈ xs → x ≢ y → x ∈ (xs ⊝ y)
∈-⊝-≢ {x ∷ xs}{x}{y} here neq with x ≟ y
...| yes q rewrite q = ⊥-elim (neq refl)
...| no  q = here
∈-⊝-≢ {x ∷ xs}{x1}{y} (there p) neq with x ≟ y
...| yes q rewrite q = ∈-⊝-≢ p neq
...| no  q = there (∈-⊝-≢ p neq)

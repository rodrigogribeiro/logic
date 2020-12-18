open import Relation.Binary as Bin
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

module Basics.SetDifference {A : Set}(_≟_ : Bin.Decidable {A = A} _≡_) where

open import Data.List
open import Basics.Membership
open MembershipDec _≟_

-- definition of the set difference operation

infixr 4 _⊝_

_⊝_ : List A → List A → List A
[] ⊝ ys = []
x ∷ xs ⊝ ys with x ∈? ys
...| yes p = xs ⊝ ys
...| no  p = x ∷ (xs ⊝ ys)

module Basics.Subset where

open import Basics.Bijection
open import Basics.Membership
open import Basics.SetEquality
open import Data.Empty
open import Data.List
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

private
  variable
    A : Set

-- subset for lists

infix 4 _⊆_

_⊆_ : List A → List A → Set
xs ⊆ ys = ∀ z → z ∈ xs → z ∈ ys

⊆-refl : ∀ {xs : List A} → xs ⊆ xs
⊆-refl xs = λ z → z

⊆-trans : ∀ {xs ys zs : List A}
          → xs ⊆ ys
          → ys ⊆ zs
          → xs ⊆ zs
⊆-trans p q = λ z z₁ → q z (p z z₁)


⊆-++-left : ∀ {xs ys : List A}
            → xs ⊆ (ys ++ xs)
⊆-++-left {A} {xs} {[]} z p = p
⊆-++-left {A} {xs} {x ∷ ys} z p = there (⊆-++-left z p)

⊆-++-right : ∀ {xs ys : List A}
             → xs ⊆ (xs ++ ys)
⊆-++-right z here = here
⊆-++-right z (there p) = there (⊆-++-right z p)

⊆-cong : ∀ {xs ys zs ws : List A}
       → xs ≈ zs
       → ys ≈ ws
       → xs ⊆ ys
       → zs ⊆ ws
⊆-cong xs≈zs ys≈ws xs⊆ys z p
  = _⇔_.to (ys≈ws z) (xs⊆ys z (_⇔_.from (xs≈zs z) p))


⊆-∷ : ∀ {xs ys : List A}{x : A} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
⊆-∷ p = λ z → λ{ here → here ; (there q) → there (p z q) }

⊆-snd : ∀ (xs : List A)(x y : A) → x ∷ xs ⊆ x ∷ y ∷ xs
⊆-snd xs x y .x here = here
⊆-snd xs x y z (there p) = there (there p)

⊆-∷-r : ∀ {xs ys : List A}{x} → xs ⊆ ys → xs ⊆ (x ∷ ys)
⊆-∷-r p z q = there (p _ q)

module ⊆-Reasoning where

  infix  3 _∎
  infixr 2 step-⊆
  infix  1 begin_

  begin_ : ∀{xs ys : List A} → xs ⊆ ys → xs ⊆ ys
  begin_ xs⊆ys = xs⊆ys

  step-⊆ : ∀ (xs {ys zs} : List A) → ys ⊆ zs → xs ⊆ ys → xs ⊆ zs
  step-⊆ _ ys⊆zs xs⊆ys = ⊆-trans xs⊆ys ys⊆zs

  _∎ : ∀ (xs : List A) → xs ⊆ xs
  _∎ _ = ⊆-refl

  syntax step-⊆  x y⊆z x⊆y = x ⊆⟨ x⊆y ⟩ y⊆z

open ⊆-Reasoning

⊆-++ : ∀ {xs xs' ys ys'  : List A} → xs ⊆ xs'
                                   → ys ⊆ ys'
                                   → (xs ++ ys) ⊆ (xs' ++ ys')
⊆-++ {xs = []} {xs' = []} {ys = ys} {ys' = ys'} xs⊆xs' ys⊆ys' = ys⊆ys'
⊆-++ {xs = []} {xs' = x ∷ xs'} {ys = ys} {ys' = ys'} xs⊆xs' ys⊆ys' z z∈ys = ∈-++-inj-right (ys⊆ys' _ z∈ys)
⊆-++ {xs = x ∷ xs} {xs' = xs'} {ys = ys} {ys' = ys'} xs⊆xs' ys⊆ys' .x here = ∈-++-inj-left (xs⊆xs' _ here)
⊆-++ {xs = x ∷ xs} {xs' = xs'} {ys = ys} {ys' = ys'} xs⊆xs' ys⊆ys' z (there z∈x∷xs++ys) with _⇔_.to (∈-++ xs ys z) z∈x∷xs++ys
... | inj₁ a = ∈-++-inj-left (xs⊆xs' z (there a))
... | inj₂ b = ∈-++-inj-right (ys⊆ys' z b)

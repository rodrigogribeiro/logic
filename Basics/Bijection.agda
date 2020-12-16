module Basics.Bijection where

open import Data.Empty
open import Data.Sum
open import Function using (id ; _∘_)

-- definition of bijection

infix 4 _⇔_

record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

-- bijection is an equivalence

private
  variable
    A B C D : Set

⇔-refl : A ⇔ A
⇔-refl = record {to = id ; from = id}

⇔-sym : A ⇔ B → B ⇔ A
⇔-sym p = record { to = _⇔_.from p
                 ; from = _⇔_.to p }

⇔-trans :  A ⇔ B → B ⇔ C → A ⇔ C
⇔-trans p q = record { to = _⇔_.to q ∘ _⇔_.to p
                     ; from = _⇔_.from p ∘ _⇔_.from q}


-- bijections for coproducts

⊎-left-identity : (⊥ ⊎ A) ⇔ A
⊎-left-identity = record { to = [ (λ ()) , id ]′
                         ; from = inj₂ }

⊎-right-identity : (A ⊎ ⊥) ⇔ A
⊎-right-identity = record { to = [ id , (λ ()) ]′
                          ; from = inj₁ }

⊎-cong : A ⇔ C → B ⇔ D → (A ⊎ B) ⇔ (C ⊎ D)
⊎-cong A⇔C B⇔D
  = record { to = λ{  (inj₁ x) → inj₁ (_⇔_.to A⇔C x)
                   ;  (inj₂ y) → inj₂ (_⇔_.to B⇔D y) }
           ; from = λ { (inj₁ x) → inj₁ (_⇔_.from A⇔C x)
                      ; (inj₂ y) → inj₂ (_⇔_.from B⇔D y) } }

⊎-assoc : (A ⊎ (B ⊎ C)) ⇔ ((A ⊎ B) ⊎ C)
⊎-assoc = record { to = λ { (inj₁ x) → inj₁ (inj₁ x)
                          ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x)
                          ; (inj₂ (inj₂ y)) → inj₂ y }
                 ; from = λ{ (inj₁ (inj₁ x)) → inj₁ x
                           ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
                           ; (inj₂ y) → inj₂ (inj₂ y) } }

⊎-comm : (A ⊎ B) ⇔ (B ⊎ A)
⊎-comm = record { to = λ{ (inj₁ x) → inj₂ x
                        ; (inj₂ y) → inj₁ y}
                ; from = λ{ (inj₁ x) → inj₂ x
                          ; (inj₂ y) → inj₁ y } }

-- equational reasoning for bijections

module ⇔-Reasoning where

  infix  3 _∎
  infixr 2 step-⇔
  infix  1 begin_

  begin_ : ∀{A B : Set} → A ⇔ B → A ⇔ B
  begin_ x≡y = x≡y

  step-⇔ : ∀ (A {B C} : Set) → B ⇔ C → A ⇔ B → A ⇔ C
  step-⇔ _ y⇔z x⇔y = ⇔-trans x⇔y y⇔z

  _∎ : ∀ (A : Set) → A ⇔ A
  _∎ _ = ⇔-refl

  syntax step-⇔  x y≡z x≡y = x ⇔⟨  x≡y ⟩ y≡z

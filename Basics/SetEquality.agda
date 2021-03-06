module Basics.SetEquality where

open import Basics.Bijection
open import Basics.Membership

open import Data.Empty
open import Data.List
open import Data.Sum
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)


-- set equality for lists

private
  variable
    A : Set

infix 4 _≈_

_≈_ : List A → List A → Set
xs ≈ ys = ∀ x → x ∈ xs ⇔ x ∈ ys

-- some simple lemmas

open ⇔-Reasoning

++-comm : ∀ (xs ys : List A) → xs ++ ys ≈ ys ++ xs
++-comm xs ys = λ z →
     begin
       z ∈ (xs ++ ys)        ⇔⟨ ∈-++ xs ys z ⟩
       ((z ∈ xs) ⊎ (z ∈ ys)) ⇔⟨ ⊎-comm ⟩
       ((z ∈ ys) ⊎ (z ∈ xs)) ⇔⟨ ⇔-sym (∈-++ ys xs z) ⟩
       z ∈ (ys ++ xs)
     ∎

≈-refl : ∀ {xs : List A} → xs ≈ xs
≈-refl = λ x → record { to = λ z → z ; from = λ z → z }

≈-sym : ∀ {xs ys : List A} → xs ≈ ys → ys ≈ xs
≈-sym p = λ x → record { to = _⇔_.from (p x) ; from = _⇔_.to (p x) }

≈-trans : ∀ {xs ys zs : List A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans p q = λ x →
                  record
                  { to = λ z → _⇔_.to (q x) (_⇔_.to (p x) z)
                  ; from = λ z → _⇔_.from (p x) (_⇔_.from (q x) z)
                  }

≈-∷ : ∀ {xs ys : List A}{x : A} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
≈-∷ {x = x} p = λ z →
  record { to = λ{ here → here
                 ; (there q) → there (_⇔_.to (p z) q) }
         ; from = λ{ here → here
                   ; (there q) → there (_⇔_.from (p z) q) } }


≈-[] : ∀ {xs : List A} → xs ≈ [] → xs ≡ []
≈-[] {xs = []} eq = refl
≈-[] {xs = x ∷ xs} eq with eq x
... | record { to = to ; from = from } = ⊥-elim (absurd (to here))
  where
    absurd : ∀ {x : A} → ¬ (x ∈ [])
    absurd ()

≈-∈ : ∀ {xs ys : List A}{x : A} → xs ≈ ys → x ∈ xs → x ∈ ys
≈-∈ xs≈ys here = _⇔_.to (xs≈ys _) here
≈-∈ xs≈ys (there p) = _⇔_.to (xs≈ys _) (there p)

∈-≈-elim : ∀ {xs}{x : A} → x ∈ xs → xs ≈ (x ∷ xs)
∈-≈-elim here z = record { to = there ; from = λ{ here → here ; (there q) → q } }
∈-≈-elim (there p) z = record { to = there ; from = λ{ here → there p ; (there q) → q} }

≈-swap : ∀ {xs}{x y : A} → x ∷ y ∷ xs ≈ y ∷ x ∷ xs
≈-swap z = record { to = λ{ here → there here
                          ; (there here) → here
                          ; (there (there q)) → there (there q) }
                  ; from = λ{ here → there here
                            ; (there here) → here
                            ; (there (there q)) → there (there q)} }


≈-∷-++-swap : ∀ {xs ys : List A}{x} → (x ∷ xs ++ ys) ≈ (xs ++ x ∷ ys)
≈-∷-++-swap {xs = xs}{ys = ys}{x = x} z
  = begin
      z ∈ (x ∷ xs ++ ys)                    ⇔⟨ ∈-++ (x ∷ xs) ys z ⟩
      ((z ∈ (x ∷ xs)) ⊎ (z ∈ ys))           ⇔⟨ ⊎-cong ⇔-refl ⇔-refl ⟩
      ((z ∈ ([ x ] ++ xs)) ⊎ (z ∈ ys))      ⇔⟨ ⊎-cong lemma ⇔-refl ⟩
      (((z ∈ xs) ⊎ (z ∈ [ x ])) ⊎ (z ∈ ys)) ⇔⟨ ⇔-sym ⊎-assoc ⟩
      ((z ∈ xs) ⊎ ((z ∈ [ x ]) ⊎ (z ∈ ys))) ⇔⟨ ⊎-cong ⇔-refl (⇔-sym (∈-++ [ x ] ys z)) ⟩
      ((z ∈ xs) ⊎ (( z ∈ ( [ x ] ++ ys )))) ⇔⟨ ⇔-refl ⟩
      ((z ∈ xs) ⊎ (z ∈ (x ∷ ys)))           ⇔⟨ ⇔-sym (∈-++ xs (x ∷ ys) z) ⟩
      z ∈ (xs ++ (x ∷ ys))
    ∎
  where
    lemma : z ∈ (x ∷ xs) ⇔ ((z ∈ xs) ⊎ (z ∈ [ x ]))
    lemma
      = begin
           z ∈ (x ∷ xs) ⇔⟨ ⇔-refl ⟩
           z ∈ ([ x ] ++ xs) ⇔⟨ ∈-++ [ x ] xs z ⟩
           ((z ∈ [ x ]) ⊎ (z ∈ xs)) ⇔⟨ ⊎-comm ⟩
           ((z ∈ xs) ⊎ (z ∈ [ x ]))
         ∎

≈-++-cong : ∀ {xs xs' ys ys' : List A}
            → xs ≈ xs'
            → ys ≈ ys'
            → xs ++ ys ≈ xs' ++ ys'
≈-++-cong {xs = xs}{xs' = xs'}{ys = ys}{ys' = ys'} eq1 eq2 z
  = begin
      z ∈ (xs ++ ys)          ⇔⟨ ∈-++ xs ys z ⟩
      ((z ∈ xs) ⊎ (z ∈ ys))   ⇔⟨ ⊎-cong (eq1 z) (eq2 z) ⟩
      ((z ∈ xs') ⊎ (z ∈ ys')) ⇔⟨ ⇔-sym (∈-++ xs' ys' z) ⟩
      z ∈ (xs' ++ ys')
    ∎ 

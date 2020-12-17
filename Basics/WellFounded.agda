open import Relation.Binary.PropositionalEquality
open import Relation.Unary hiding (Pred)
open import Relation.Nullary

module Wellfounded where


  -- general form of relations

  Rel : Set → Set₁
  Rel A = A → A → Set

  -- general form of predicates

  Pred : Set → Set₁
  Pred A = A → Set

  -- recursion structures

  RecStruct : Set → Set₁
  RecStruct A = Pred A → Pred A

  WfRec : ∀ {A} → Rel A → RecStruct A
  WfRec _<_ P x = ∀ y → y < x → P y

  -- the accessibility predicate

  data Acc {A : Set}(R : Rel A)(x : A) : Set where
    acc : (∀ y → R y x → Acc R y) → Acc R x

  -- fold for Acc

  acc-fold : {A : Set}                         →
             {R : Rel A}                       →
             {P : A → Set}                     →
             (∀ x → (∀ y → R y x → P y) → P x) →
             ∀ z → Acc R z → P z
  acc-fold IH z (acc H) = IH z (λ y y<z → acc-fold IH y (H y y<z))


  -- well founded relation definition

  WellFounded : {A : Set}(R : Rel A) → Set
  WellFounded R = ∀ x → Acc R x

  -- recursor

  wfRec : {A : Set}                         →
          (R : Rel A)                       →
          WellFounded R                     →
          ∀ (P : A → Set)                   →
          (∀ x → (∀ y → R y x → P y) → P x) →
          ∀ a → P a
  wfRec R wf P IH a = acc-fold IH a (wf a)

  -- natural numbers, under <, are well formed

  module Nat-WF where

    open import Data.Nat

    -- another definition of less than relation

    data _<'_ (n : ℕ) : ℕ → Set where
      <'-base : n <' suc n
      <'-step : ∀ {m} → n <' m → n <' suc m

    <'-inv : ∀ {n m} → suc n <' suc m → n <' m
    <'-inv {zero} {.1} <'-base = <'-base
    <'-inv {zero} {.2} (<'-step <'-base) = <'-step <'-base
    <'-inv {zero} {.(suc _)} (<'-step (<'-step p)) = <'-step (<'-inv (<'-step p))
    <'-inv {suc n} {zero} (<'-step ())
    <'-inv {suc n} {suc .(suc n)} <'-base = <'-base
    <'-inv {suc n} {suc m} (<'-step p) = <'-step (<'-inv p)

    <'-suc : ∀ {n m} → suc n <' suc m → n <' suc m
    <'-suc {zero} {.1} <'-base = <'-step <'-base
    <'-suc {zero} {suc m} (<'-step p) = <'-step (<'-suc p)
    <'-suc {suc n} {.(suc (suc n))} <'-base = <'-step <'-base
    <'-suc {suc n} {suc m} (<'-step p) = <'-step (<'-suc p)

    -- <' is well formed

    <'-ℕ-wf : WellFounded _<'_
    <'-ℕ-wf x = acc (IH x)
        where
          IH : ∀ x y → y <' x → Acc _<'_ y
          IH (suc x) .x <'-base = <'-ℕ-wf x
          IH (suc x) y (<'-step y<x) = IH x y y<x

  -- constructing well-founded relations: inverse image construction

  module InverseImageWellFounded {A B}(f : A → B)(_<_ : Rel B) where

    _<img_ : Rel A
    x <img y = f x < f y

    inv-img-acc : ∀ {x} → Acc _<_ (f x) → Acc _<img_ x
    inv-img-acc (acc g) = acc (λ y fy<fx → inv-img-acc (g (f y) fy<fx))

    inv-img-WF : WellFounded _<_ → WellFounded _<img_
    inv-img-WF wf x = inv-img-acc (wf (f x))

  -- lexicographic induction

  module Lexicographic {A : Set}{B : A → Set}(RelA : Rel A)(RelB : ∀ x → Rel (B x)) where

    open import Data.Product

    data _<lex_ : Rel (Σ A B) where
      left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA x₁ x₂) → (x₁ , y₁) <lex (x₂ , y₂)
      right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB x y₁ y₂) → (x  , y₁) <lex (x  , y₂)

    mutual
      accessibleA : ∀ {x y} → Acc RelA x →
                              (∀ {x} → WellFounded (RelB x)) →
                              Acc _<lex_ (x , y)
      accessibleA accA wfB = acc (accessibleB accA (wfB _) wfB)

      accessibleB : ∀ {x y} → Acc RelA x →
                              Acc (RelB x) y →
                              (∀ {x} → WellFounded (RelB x)) →
                              WfRec _<lex_ (Acc _<lex_) (x , y)
      accessibleB (acc rsA) _    wfB ._ (left  x′<x) = accessibleA (rsA _ x′<x) wfB
      accessibleB accA (acc rsB) wfB ._ (right y′<y) = acc (accessibleB accA (rsB _ y′<y) wfB)

    wellFounded : WellFounded RelA → (∀ {x} → WellFounded (RelB x)) → WellFounded _<lex_
    wellFounded wfA wfB p = accessibleA (wfA (proj₁ p)) wfB


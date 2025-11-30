{-

This file contains:

- Definition of set quotients

-}
{-# OPTIONS --safe #-}
module Cubical.HITs.SetQuotients.Base where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

-- Set quotients as a higher inductive type:
data _/_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  [_] : (a : A) → A / R
  eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
  squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q

_/ʰ_ : ∀ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') → hSet (ℓ-max ℓ ℓ')
A /ʰ R = A / R , squash/

record isEquivRel {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isRefl : ∀ {x} → R x x
    isSym : ∀ {x y} → R x y → R y x
    isTrans : ∀ {x y z} → R x y → R y z → R x z

pathPreservesProp : ∀ {ℓ} {A B : Type ℓ} → (isProp A) → (p : A ≡ B) → ∀ i → isProp (p i)
pathPreservesProp isPropA p i =
  transport-filler (λ j → isProp (p j)) isPropA i 

module _ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') (equiv : isEquivRel R) where
  open isEquivRel equiv

  module _ {ℓ''} {B : A / R → hSet ℓ''} (f : (a : A) → ⟨ B [ a ] ⟩)
           (fp : (a b : A) → (r : R a b)
               → PathP (λ i → fst (B (eq/ a b r i))) (f a) (f b)) where
    lift-f : (a : A / R) → ⟨ B a ⟩
    lift-f [ a ] = f a
    lift-f (eq/ a b r i) = fp a b r i
    lift-f (squash/ x y p q i j) =
      isSet→SquareP (λ i j → str (B (squash/ x y p q i j))) (λ j → lift-f (p j)) (λ j → lift-f (q j)) (λ i → lift-f x) (λ i → lift-f y) i j

  data R̂ (a : A) (x : A / R) : Type (ℓ-max ℓ ℓ') where
    mkR̂ : (b : A) (p : [ b ] ≡ x) (r : R a b) → R̂ a x

  R' : A → A / R → {!!}
  R' a = lift-f f fp
    where
    f : ∀ (x : A) → Type (ℓ-max ℓ ℓ')
    f x = ∥ R̂ a [ x ] ∥₁
    fp : ∀ x y (rxy : R x y) → f x ≡ f y
    fp x y rxy = {!!}
      where
      ϕ : ∥ R̂ a [ x ] ∥₁ → ∥ R̂ a [ y ] ∥₁
      ϕ ∣ rax ∣₁ = ∣ isTrans rax rxy ∣₁
      ϕ (squash₁ u v i) = isPropPropTrunc (ϕ u) (ϕ v) i
      ψ : ∥ R a y ∥₁ → ∥ R a x ∥₁
      ψ ∣ ray ∣₁ = ∣ isTrans ray (isSym rxy) ∣₁
      ψ (squash₁ u v i) = isPropPropTrunc (ψ u) (ψ v) i
      p : ∥ R a x ∥₁ ≡ ∥ R a y ∥₁
      p = ua (propBiimpl→Equiv isPropPropTrunc isPropPropTrunc ϕ ψ)


  -- -- R' : A → A / R → hProp _
  -- -- R' a [ a' ] = ∥ R a a' ∥₁ , isPropPropTrunc
  -- -- R' a (eq/ x y rxy i) = ΣPathP (p , {!q!}) i
  -- --   where
  -- --   ϕ : ∥ R a x ∥₁ → ∥ R a y ∥₁
  -- --   ϕ ∣ rax ∣₁ = ∣ isTrans rax rxy ∣₁
  -- --   ϕ (squash₁ u v i) = isPropPropTrunc (ϕ u) (ϕ v) i
  -- --   ψ : ∥ R a y ∥₁ → ∥ R a x ∥₁
  -- --   ψ ∣ ray ∣₁ = ∣ isTrans ray (isSym rxy) ∣₁
  -- --   ψ (squash₁ u v i) = isPropPropTrunc (ψ u) (ψ v) i
  -- --   p : ∥ R a x ∥₁ ≡ ∥ R a y ∥₁
  -- --   p = ua (propBiimpl→Equiv isPropPropTrunc isPropPropTrunc ϕ ψ)
  -- --   q : ∀ i → isProp (p i)
  -- --   q i = pathPreservesProp isPropPropTrunc p i
  -- --   s : PathP (λ i → isProp (p i))
  -- --             isPropPropTrunc
  -- --             (transport (λ j → isProp (p j)) isPropPropTrunc)
  -- --   s = transport-filler (λ j → isProp (p j)) isPropPropTrunc
  -- --   t : PathP (λ i → isProp (p i)) isPropPropTrunc isPropPropTrunc
  -- --   t = s ▷ sym (transport-filler {!!} rxy i)
  -- -- -- R' a (squash/ x y p q i j) = r i j
  -- -- --   where
  -- -- --   C : I → I → Type _
  -- -- --   C i j = Type ℓ'

  -- --   setC : (i j : I) → isSet (C i j)
  -- --   setC i j = {!!}

  -- --   r : SquareP C
  -- --         (λ j → R' a (p j))
  -- --         (λ j → R' a (q j))
  -- --         (λ _ → R' a x)
  -- --         (λ _ → R' a y)
  -- --   r = isSet→SquareP setC
  -- --         (λ j → R' a (p j))
  -- --         (λ j → R' a (q j))
  -- --         (λ _ → R' a x)
  -- --         (λ _ → R' a y)

  -- -- isSetValuedR' : ∀ a x → isSet (R' a x)
  -- -- isSetValuedR' a x = {!isProp→isSet isPropPropTrunc!}
  
  -- -- isEffectiveR : ∀ a b → [ a ] ≡ [ b ] → R a b
  -- -- isEffectiveR a b p = {!!}

  

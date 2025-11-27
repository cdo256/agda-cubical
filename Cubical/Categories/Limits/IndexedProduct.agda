{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.IndexedProduct where

open import Cubical.Categories.Category.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    ℓ ℓ' ℓI : Level

module _ {ℓI} (C : Category ℓ ℓ') where
  open Category C

  module _ (I : hSet ℓI) (S : ⟨ I ⟩ → ob) {ΠS : ob}
           (proj : ∀ i → Hom[ ΠS , S i ]) where

    isProduct : Type (ℓ-max (ℓ-max ℓ ℓ') ℓI)
    isProduct = ∀ {z : ob} (f : ∀ i → Hom[ z , S i ]) →
        ∃![ g ∈ Hom[ z , ΠS ] ] ∀ i → (g ⋆ proj i ≡ f i)

    isPropIsProduct : isProp isProduct
    isPropIsProduct = isPropImplicitΠ (λ _ → isPropΠ λ _ → isPropIsContr)

  record Product (I : hSet ℓI) (S : ⟨ I ⟩ → ob) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓI) where
    field
      prodOb : ob
      prodProj : ∀ i → Hom[ prodOb , S i ]
      univProp : isProduct I S prodProj

  Products : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓI))
  Products = ∀ (I : hSet ℓI) (S : ⟨ I ⟩ → ob) → Product I S

  hasProducts : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓI))
  hasProducts = ∥ Products ∥₁

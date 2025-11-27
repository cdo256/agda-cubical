{-# OPTIONS --safe #-}

module Cubical.Categories.Limits.IndexedCoproduct where

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

  module _ (I : hSet ℓI) (S : ⟨ I ⟩ → ob) {ΣS : ob}
           (inj : ∀ i → Hom[ S i , ΣS ]) where

    isCoproduct : Type (ℓ-max (ℓ-max ℓ ℓ') ℓI)
    isCoproduct = ∀ {z : ob} (f : ∀ i → Hom[ S i , z ]) →
        ∃![ g ∈ Hom[ ΣS , z ] ] ∀ i → (inj i ⋆ g ≡ f i)

    isPropIsCoproduct : isProp isCoproduct
    isPropIsCoproduct = isPropImplicitΠ (λ _ → isPropΠ λ _ → isPropIsContr)

  record Coproduct (I : hSet ℓI) (S : ⟨ I ⟩ → ob) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓI) where
    field
      coprodOb : ob
      coprodInj : ∀ i → Hom[ S i , coprodOb ]
      univProp : isCoproduct I S coprodInj

  Coproducts : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓI))
  Coproducts = ∀ (I : hSet ℓI) (S : ⟨ I ⟩ → ob) → Coproduct I S

  hasCoproducts : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓI))
  hasCoproducts = ∥ Coproducts ∥₁

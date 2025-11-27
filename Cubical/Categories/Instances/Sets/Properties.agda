{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets.Properties where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets.Base
open import Cubical.Categories.Limits.BinCoproduct
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.IndexedCoproduct
open import Cubical.Categories.Limits.IndexedProduct
open import Cubical.Categories.NaturalTransformation
open import Cubical.Data.Prod.Properties 
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)

private
  variable
    ℓ ℓ' ℓI ℓI' : Level

Lift-hSet : ∀ {ℓ ℓ'} → hSet ℓ → hSet (ℓ-max ℓ ℓ')
Lift-hSet {ℓ' = ℓ'} X = Lift {j = ℓ'} ⟨ X ⟩ , isOfHLevelLift 2 (str X)

-- helper for Lift
liftLower : ∀ {ℓ ℓ'} {A : Type ℓ} (x : Lift {j = ℓ'} A) → lift (x .lower) ≡ x
liftLower (lift a) = refl

----------------------------------------------------------------------
-- Binary products
----------------------------------------------------------------------

module _ (X Y : hSet ℓ) where
  open BinProduct

  private
    X×Y : hSet ℓ
    X×Y = ⟨ X ⟩ × ⟨ Y ⟩ , isSet× (str X) (str Y)

  binProduct : BinProduct (SET ℓ) X Y
  binProduct .binProdOb  = X×Y
  binProduct .binProdPr₁ = fst
  binProduct .binProdPr₂ = snd
  binProduct .univProp {z = Z} f₁ f₂ = u , isUniv
    where
    Pf : (⟨ Z ⟩ → ⟨ X×Y ⟩) → Type ℓ
    Pf f = (fst ∘ f ≡ f₁) × (snd ∘ f ≡ f₂)

    Univ : Type ℓ
    Univ = Σ (⟨ Z ⟩ → ⟨ X×Y ⟩) Pf

    isPropPf : ∀ g → isProp (Pf g)
    isPropPf g =
      isProp× (isSet→ (str X) (fst ∘ g) f₁)
              (isSet→ (str Y) (snd ∘ g) f₂)

    f : ⟨ Z ⟩ → ⟨ X×Y ⟩
    f z = f₁ z , f₂ z

    u : Univ
    u = f , (refl , refl)

    isUniv : (v : Univ) → u ≡ v
    isUniv v = Σ≡Prop isPropPf f≡g
      where
      g  = v .fst
      p₁ = v .snd .fst
      p₂ = v .snd .snd

      f≡g : f ≡ g
      f≡g = funExt λ z →
        cong₂ _,_ (funExt⁻ (sym p₁) z)
                  (funExt⁻ (sym p₂) z)

----------------------------------------------------------------------
-- Binary coproducts
----------------------------------------------------------------------

module _ (X Y : hSet ℓ) where
  open BinCoproduct

  private
    X+Y : hSet ℓ
    X+Y = ⟨ X ⟩ ⊎ ⟨ Y ⟩ , isSet⊎ (str X) (str Y)

  binCoproduct : BinCoproduct (SET ℓ) X Y
  binCoproduct .binCoprodOb   = X+Y
  binCoproduct .binCoprodInj₁ = inl
  binCoproduct .binCoprodInj₂ = inr
  binCoproduct .univProp {z = Z} f₁ f₂ = u , isUniv
    where
    Pf : (⟨ X+Y ⟩ → ⟨ Z ⟩) → Type ℓ
    Pf f = (f ∘ inl ≡ f₁) × (f ∘ inr ≡ f₂)

    Univ : Type ℓ
    Univ = Σ (⟨ X+Y ⟩ → ⟨ Z ⟩) Pf

    isPropPf : ∀ g → isProp (Pf g)
    isPropPf g =
      isProp× (isSet→ (str Z) (g ∘ inl) f₁)
              (isSet→ (str Z) (g ∘ inr) f₂)

    f : ⟨ X+Y ⟩ → ⟨ Z ⟩
    f (inl x) = f₁ x
    f (inr y) = f₂ y

    u : Univ
    u = f , (refl , refl)

    isUniv : (v : Univ) → u ≡ v
    isUniv v = Σ≡Prop isPropPf f≡g
      where
      g  = v .fst
      p₁ = v .snd .fst
      p₂ = v .snd .snd

      f≡g : f ≡ g
      f≡g = funExt
        λ { (inl x) → funExt⁻ (sym p₁) x
          ; (inr y) → funExt⁻ (sym p₂) y
          }

----------------------------------------------------------------------
-- Indexed products
----------------------------------------------------------------------

module _ (I : hSet ℓ) (S : ⟨ I ⟩ → hSet ℓ') where
  open Product

  private
    ΠS : hSet (ℓ-max ℓ ℓ')
    ΠS = (∀ i → ⟨ S i ⟩) , isSetΠ (λ i → str (S i))

  product : Product (SET (ℓ-max ℓ ℓ')) I (λ i → Lift-hSet {ℓ' = ℓ} (S i))
  product .prodOb       = ΠS
  product .prodProj i Γ = lift (Γ i)
  product .univProp {z = Z} f = u , isUniv
    where
    Pf : (⟨ Z ⟩ → ⟨ ΠS ⟩) → Type (ℓ-max ℓ ℓ')
    Pf g = ∀ i → (λ Γ → lift (Γ i)) ∘ g ≡ f i

    Univ : Type (ℓ-max ℓ ℓ')
    Univ = Σ (⟨ Z ⟩ → ⟨ ΠS ⟩) Pf

    isPropPf : ∀ g → isProp (Pf g)
    isPropPf g =
      isPropΠ λ i →
        isSet→ (isOfHLevelLift 2 (str (S i)))
               ((λ Γ → lift (Γ i)) ∘ g)
               (f i)

    g : ⟨ Z ⟩ → ⟨ ΠS ⟩
    g z i = (f i z) .lower

    u : Univ
    u = g , λ i → funExt λ z → liftLower (f i z)

    isUniv : (v : Univ) → u ≡ v
    isUniv v = Σ≡Prop isPropPf g≡h
      where
      h = v .fst
      p = v .snd

      g≡h : g ≡ h
      g≡h = funExt λ z → funExt λ i →
        sym (cong lower (funExt⁻ (p i) z))

----------------------------------------------------------------------
-- Indexed coproducts
----------------------------------------------------------------------

module _ (I : hSet ℓ) (S : ⟨ I ⟩ → hSet ℓ') where
  open Coproduct

  private
    ΣS : hSet (ℓ-max ℓ ℓ')
    ΣS = (Σ[ i ∈ ⟨ I ⟩ ] ⟨ S i ⟩)
       , isSetΣ (str I) (λ i → str (S i))

  coproduct : Coproduct (SET (ℓ-max ℓ ℓ')) I (λ i → Lift-hSet {ℓ' = ℓ} (S i))
  coproduct .coprodOb = ΣS
  coproduct .coprodInj i (lift s) = i , s
  coproduct .univProp {z = Z} f = u , isUniv
    where
    inj' : ∀ i → ⟨ Lift-hSet (S i) ⟩ → ⟨ ΣS ⟩
    inj' i (lift s) = i , s

    Pf : (⟨ ΣS ⟩ → ⟨ Z ⟩) → Type (ℓ-max ℓ ℓ')
    Pf g = ∀ i → g ∘ inj' i ≡ f i

    Univ : Type (ℓ-max ℓ ℓ')
    Univ = Σ (⟨ ΣS ⟩ → ⟨ Z ⟩) Pf

    isPropPf : ∀ g → isProp (Pf g)
    isPropPf g =
      isPropΠ λ i →
        isSet→ (str Z) (g ∘ inj' i) (f i)

    g : ⟨ ΣS ⟩ → ⟨ Z ⟩
    g (i , s) = f i (lift s)

    u : Univ
    u = g , λ i → funExt λ where (lift s) → refl

    isUniv : (v : Univ) → u ≡ v
    isUniv v = Σ≡Prop isPropPf g≡h
      where
      h  = v .fst
      p  = v .snd
      pᵍ = u .snd

      g≡h : g ≡ h
      g≡h = funExt λ (i , s) →
        let qg = cong (λ k → k (lift s)) (pᵍ i)
            qh = cong (λ k → k (lift s)) (p  i)
        in qg ∙ sym qh

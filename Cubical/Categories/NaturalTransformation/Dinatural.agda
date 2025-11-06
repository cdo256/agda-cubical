{-# OPTIONS --safe #-}
module Cubical.Categories.NaturalTransformation.Dinatural where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism renaming (iso to iIso)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Commutativity
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor.Bifunctor 
open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓC ℓC' ℓD ℓD' : Level
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    module C = Category C
    module D = Category D
  record DinaturalTrans (F G : Bifunctor (C ^op) C D)
       : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    eta-equality
    private
      module F = Functor F
      module G = Functor G

    field
      α          : ∀ X → D [ F.F-ob (X , X) , G.F-ob (X , X) ]
      hexagon    : ∀ {X Y} (f : C [ X , Y ])
                → F.F-hom (f , C.id) D.⋆ α X D.⋆ G.F-hom (C.id , f)
                ≡ F.F-hom (C.id , f) D.⋆ α Y D.⋆ G.F-hom (f , C.id)
  
  module _ (F : Bifunctor (C ^op) C D) where
    open Functor F
    diamond : ∀ {X Y} (f : C [ X , Y ])
            → F-hom (f , C.id) D.⋆ F-hom (C.id , f)
            ≡ F-hom (C.id , f) D.⋆ F-hom (f , C.id)
    diamond f =
      F-hom (f , C.id) D.⋆ F-hom (C.id , f)
        ≡⟨ sym (F-seq (f , C.id) (C.id , f)) ⟩
      F-hom (C.id C.⋆ f , C.id C.⋆ f)
        ≡⟨ cong (λ ○ → F-hom (○ , ○)) (C.⋆IdL f ∙ sym (C.⋆IdR f)) ⟩
      F-hom (f C.⋆ C.id , f C.⋆ C.id)
        ≡⟨ F-seq (C.id , f) (f , C.id)  ⟩
      F-hom (C.id , f) D.⋆ F-hom (f , C.id) ∎

  module _ {F G H : Bifunctor (C ^op) C D} where
    private
      module F = Functor F
      module G = Functor G
      module H = Functor H
      open F using () renaming (F-ob to F₀; F-hom to F₁)
      open G using () renaming (F-ob to G₀; F-hom to G₁)
      open H using () renaming (F-ob to H₀; F-hom to H₁)
    -- open Functor
    -- open DinaturalTrans


    module LeftComposition (θ : NatTrans G H) (β : DinaturalTrans F G) where
      private
        module θ = NatTrans θ
        module β = DinaturalTrans β
        open θ using () renaming (N-ob to θ₀)
        open β using () renaming (α to β₀)
      α : (X : C.ob) → D [ F₀ (X , X) , H₀ (X , X) ]
      α X = β₀ X D.⋆ θ₀ (X , X) 
      hexagon : ∀ {X Y} → (f : C [ X , Y ])
              → F₁ (f , C.id) D.⋆ α X D.⋆ H₁ (C.id , f)
              ≡ F₁ (C.id , f) D.⋆ α Y D.⋆ H₁ (f , C.id) 
      hexagon {X} {Y} f = 
        F₁ (f , C.id) D.⋆ ((β₀ X D.⋆ θ₀ (X , X)) D.⋆ H₁ (C.id , f))
          ≡⟨ cong (F₁ (f , C.id) D.⋆_) (D.⋆Assoc _ _ _) ⟩
        F₁ (f , C.id) D.⋆ (β₀ X D.⋆ (θ₀ (X , X) D.⋆ H₁ (C.id , f)))
          ≡⟨ cong (λ ○ → F₁ (f , C.id) D.⋆ (β₀ X D.⋆ ○)) (sym (θ.N-hom _)) ⟩
        F₁ (f , C.id) D.⋆ (β₀ X D.⋆ (G₁ (C.id , f) D.⋆ θ₀ (X , Y)))
          ≡⟨ cong (F₁ (f , C.id) D.⋆_) (sym (D.⋆Assoc _ _ _)) ⟩
        F₁ (f , C.id) D.⋆ ((β₀ X D.⋆ G₁ (C.id , f)) D.⋆ θ₀ (X , Y))
          ≡⟨ sym (D.⋆Assoc _ _ _) ⟩
        (F₁ (f , C.id) D.⋆ (β₀ X D.⋆ G₁ (C.id , f))) D.⋆ θ₀ (X , Y)
          ≡⟨ cong (D._⋆ θ₀ (X , Y)) (β.hexagon f) ⟩
        (F₁ (C.id , f) D.⋆ (β₀ Y D.⋆ G₁ (f , C.id))) D.⋆ θ₀ (X , Y)
          ≡⟨ D.⋆Assoc _ _ _ ⟩
        F₁ (C.id , f) D.⋆ ((β₀ Y D.⋆ G₁ (f , C.id)) D.⋆ θ₀ (X , Y))
          ≡⟨ cong (F₁ (C.id , f) D.⋆_) (D.⋆Assoc _ _ _) ⟩
        F₁ (C.id , f) D.⋆ (β₀ Y D.⋆ (G₁ (f , C.id) D.⋆ θ₀ (X , Y)))
          ≡⟨ cong (λ ○ → F₁ (C.id , f) D.⋆ (β₀ Y D.⋆ ○))
                  (θ.N-hom (f , C.id)) ⟩
        F₁ (C.id , f) D.⋆ (β₀ Y D.⋆ (θ₀ (Y , Y) D.⋆ H₁ (f , C.id)))
          ≡⟨ cong (F₁ (C.id , f) D.⋆_) (sym (D.⋆Assoc _ _ _)) ⟩
        F₁ (C.id , f) D.⋆ ((β₀ Y D.⋆ θ₀ (Y , Y)) D.⋆ H₁ (f , C.id)) ∎

      _<∘_ : DinaturalTrans F H
      _<∘_ = record { α = α ; hexagon = hexagon}
      infixr 9 _<∘_
    open LeftComposition using (_<∘_)

    module RightComposition (θ : DinaturalTrans G H) (β : NatTrans F G) where
      private
        module θ = DinaturalTrans θ
        module β = NatTrans β
        open θ using () renaming (α to θ₀)
        open β using () renaming (N-ob to β₀)

      α : (X : C.ob) → D [ F₀ (X , X) , H₀ (X , X) ]
      α X = β₀ (X , X) D.⋆ θ₀ X 

      hexagon : ∀ {X Y} → (f : C [ X , Y ])
              → F₁ (f , C.id) D.⋆ α X D.⋆ H₁ (C.id , f)
              ≡ F₁ (C.id , f) D.⋆ α Y D.⋆ H₁ (f , C.id) 
      hexagon {X} {Y} f = 
        F₁ (f , C.id) D.⋆ ((β₀ (X , X) D.⋆ θ₀ X) D.⋆ H₁ (C.id , f))
          ≡⟨ sym (D.⋆Assoc _ _ _) ⟩
        (F₁ (f , C.id) D.⋆ (β₀ (X , X) D.⋆ θ₀ X)) D.⋆ H₁ (C.id , f)
          ≡⟨ cong (D._⋆ H₁ (C.id , f)) (sym (D.⋆Assoc _ _ _)) ⟩
        ((F₁ (f , C.id) D.⋆ β₀ (X , X)) D.⋆ θ₀ X) D.⋆ H₁ (C.id , f)
          ≡⟨ cong (λ ○ → (○ D.⋆ θ₀ X) D.⋆ H₁ (C.id , f)) (β.N-hom (f , C.id)) ⟩
        ((β₀ (Y , X) D.⋆ G₁ (f , C.id)) D.⋆ θ₀ X) D.⋆ H₁ (C.id , f)
          ≡⟨ cong (D._⋆ H₁ (C.id , f)) (D.⋆Assoc _ _ _) ⟩
        (β₀ (Y , X) D.⋆ (G₁ (f , C.id) D.⋆ θ₀ X)) D.⋆ H₁ (C.id , f)
          ≡⟨ D.⋆Assoc _ _ _ ⟩
        β₀ (Y , X) D.⋆ ((G₁ (f , C.id) D.⋆ θ₀ X) D.⋆ H₁ (C.id , f))
          ≡⟨ cong (β₀ (Y , X) D.⋆_) (D.⋆Assoc _ _ _) ⟩
        β₀ (Y , X) D.⋆ (G₁ (f , C.id) D.⋆ (θ₀ X D.⋆ H₁ (C.id , f)))
          ≡⟨ cong (λ ○ → β₀ (Y , X) D.⋆ ○) (θ.hexagon f) ⟩
        β₀ (Y , X) D.⋆ (G₁ (C.id , f) D.⋆ (θ₀ Y D.⋆ H₁ (f , C.id)))
          ≡⟨ cong (β₀ (Y , X) D.⋆_) (sym (D.⋆Assoc _ _ _)) ⟩
        β₀ (Y , X) D.⋆ ((G₁ (C.id , f) D.⋆ θ₀ Y) D.⋆ H₁ (f , C.id))
          ≡⟨ cong (β₀ (Y , X) D.⋆_) (D.⋆Assoc _ _ _) ⟩
        β₀ (Y , X) D.⋆ (G₁ (C.id , f) D.⋆ (θ₀ Y D.⋆ H₁ (f , C.id)))
          ≡⟨ sym (D.⋆Assoc _ _ _) ⟩
        (β₀ (Y , X) D.⋆ G₁ (C.id , f)) D.⋆ (θ₀ Y D.⋆ H₁ (f , C.id))
          ≡⟨ cong (D._⋆ (θ₀ Y D.⋆ H₁ (f , C.id))) (sym (β.N-hom (C.id , f))) ⟩
        (F₁ (C.id , f) D.⋆ β₀ (Y , Y)) D.⋆ (θ₀ Y D.⋆ H₁ (f , C.id))
          ≡⟨ D.⋆Assoc _ _ _ ⟩
        F₁ (C.id , f) D.⋆ (β₀ (Y , Y) D.⋆ (θ₀ Y D.⋆ H₁ (f , C.id)))
          ≡⟨ cong (F₁ (C.id , f) D.⋆_) (sym (D.⋆Assoc _ _ _)) ⟩
        F₁ (C.id , f) D.⋆ ((β₀ (Y , Y) D.⋆ θ₀ Y) D.⋆ H₁ (f , C.id)) ∎

      _∘>_ : DinaturalTrans F H
      _∘>_ = record { α = α ; hexagon = hexagon }
      infixl 9 _∘>_
    open RightComposition using (_∘>_)


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

    infixr 9 _<∘_
    infixl 9 _∘>_

    module _ (θ : NatTrans G H) (β : DinaturalTrans F G) where
      private
        module θ = NatTrans θ
        module β = DinaturalTrans β
        open θ using () renaming (N-ob to θ₀)
        open β using () renaming (α to β₀)
        open C using (id)
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
          ≡⟨ {!cong (F₁ (f , C.id) D.⋆_) ?!} ⟩
        F₁ (f , C.id) D.⋆ ((β₀ X D.⋆ G₁ (C.id , f)) D.⋆ θ₀ (X , Y))
          ≡⟨ {!cong (F₁ (f , C.id) D.⋆_) ?!} ⟩
        F₁ (C.id , f) D.⋆ ((β₀ Y D.⋆ θ₀ (Y , Y)) D.⋆ H₁ (f , C.id)) ∎
        where
        rect : {!θ!}
        rect = {!!}

      _<∘_ : DinaturalTrans F H
      (_<∘_) = record { α = α ; hexagon = hexagon}
      -- X = β₀ X D.⋆ θ₀ (X , X)
      -- (_<∘_) .hexagon {X} {Y} f =
      --   F-hom F (f , C.id) D.⋆ α _<∘_ X D.⋆ F-hom H (C.id , f)
      --     ≡⟨ {!!} ⟩
      --   F-hom F (f , C.id) D.⋆ α _<∘_ X D.⋆ F-hom H (C.id , f)
      --     ≡⟨ {!!} ⟩
      --   F-hom F (C.id , f) D.⋆ α _<∘_ Y D.⋆ F-hom H (f , C.id) ∎

    -- _∘>_ : DinaturalTrans G H → NatTrans F G → DinaturalTrans F H
    -- β ∘> θ = record
    --   { α       = λ X → N-ob (X , X) ⋆ α X
    --   ; hexagon = λ {X Y} f → {!!}    }
    --   where module θ = NatTrans θ
    --         module β = DinaturalTrans β
    --         open θ
    --         open β

  -- module _ {F G : Bifunctor (Category.op C) C D} where
  --   private
  --     module C = Category C
  --   open Category D
  --   open HomReasoning
  --   open Functor
  --   open MR D

  --   infixl 9 _∘ʳ_

  --   _∘ʳ_ : ∀ {E : Category o ℓ e} →
  --            DinaturalTrans F G → (K : Functor E C) → DinaturalTrans (F ∘F ((Functor.op K) ⁂ K)) (G ∘F ((Functor.op K) ⁂ K))
  --   _∘ʳ_ {E = E} β K = dtHelper record
  --     { α       = λ X → α (F₀ K X)
  --     ; hexagon = λ {X Y} f → begin
  --       F₁ G (F₁ K E.id , F₁ K f) ∘ α (F₀ K X) ∘ F₁ F (F₁ K f , F₁ K E.id)
  --         ≈⟨ F-resp-≈ G (identity K , C.Equiv.refl) ⟩∘⟨ Equiv.refl ⟩∘⟨ F-resp-≈ F (C.Equiv.refl , identity K) ⟩
  --       F₁ G (C.id , F₁ K f) ∘ α (F₀ K X) ∘ F₁ F (F₁ K f , C.id)
  --         ≈⟨ hexagon (F₁ K f) ⟩
  --       F₁ G (F₁ K f , C.id) ∘ α (F₀ K Y) ∘ F₁ F (C.id , F₁ K f)
  --         ≈˘⟨ F-resp-≈ G (C.Equiv.refl , identity K) ⟩∘⟨ Equiv.refl ⟩∘⟨ F-resp-≈ F (identity K , C.Equiv.refl) ⟩
  --       F₁ G (F₁ K f , F₁ K E.id) ∘ α (F₀ K Y) ∘ F₁ F (F₁ K E.id , F₁ K f)
  --         ∎
  --     }
  --     where module β = DinaturalTrans β
  --           module E = Category E
  --           open β

  --   infix 4 _≃_

  --   _≃_ : Rel (DinaturalTrans F G) _
  --   β ≃ δ = ∀ {X} → α β X ≈ α δ X
  --     where open DinaturalTrans

  --   ≃-isEquivalence : IsEquivalence _≃_
  --   ≃-isEquivalence = record
  --     { refl  = Equiv.refl
  --     ; sym   = λ eq → Equiv.sym eq
  --     ; trans = λ eq eq′ → Equiv.trans eq eq′
  --     }

  --   ≃-setoid : Setoid _ _
  --   ≃-setoid = record
  --     { Carrier       = DinaturalTrans F G
  --     ; _≈_           = _≃_
  --     ; isEquivalence = ≃-isEquivalence
  --     }


-- -- for convenience, the following are some helpers for the cases
-- -- in which the bifunctor on the right is extranatural.
-- Extranaturalʳ : ∀ {C : Category o ℓ e} → Category.Obj D → (F : Bifunctor (Category.op C) C D) → Set _
-- Extranaturalʳ A F = DinaturalTrans (const A) F

-- Extranaturalˡ : ∀ {C : Category o ℓ e} → (F : Bifunctor (Category.op C) C D) → Category.Obj D → Set _
-- Extranaturalˡ F A = DinaturalTrans F (const A)

-- module _ {F : Bifunctor (Category.op C) C D} where
--   open Category D
--   private
--     module C = Category C
--     variable
--       A : Obj
--       X Y : C.Obj
--       f : X C.⇒ Y
--   open Functor F
--   open HomReasoning
--   open MR D

--   extranaturalʳ : (a : ∀ X → A ⇒ F₀ (X , X)) →
--                   (∀ {X X′ f} → F₁ (C.id , f) ∘ a X ≈ F₁ (f , C.id) ∘ a X′) →
--                   Extranaturalʳ A F
--   extranaturalʳ a comm = dtHelper record
--     { α       = a
--     ; hexagon = λ f → ∘-resp-≈ʳ identityʳ ○ comm ○ ∘-resp-≈ʳ (⟺ identityʳ)
--     }

--   open DinaturalTrans

--   extranatural-commʳ : (β : DinaturalTrans (const A) F) →
--                        F₁ (C.id , f) ∘ α β X ≈ F₁ (f , C.id) ∘ α β Y
--   extranatural-commʳ {f = f} β = ∘-resp-≈ʳ (⟺ identityʳ) ○ hexagon β f ○ ∘-resp-≈ʳ identityʳ

--   -- the dual case, the bifunctor on the left is extranatural.

--   extranaturalˡ : (a : ∀ X → F₀ (X , X) ⇒ A) →
--                   (∀ {X X′ f} → a X ∘ F₁ (f , C.id) ≈ a X′ ∘ F₁ (C.id , f)) →
--                   Extranaturalˡ F A
--   extranaturalˡ a comm = dtHelper record
--     { α       = a
--     ; hexagon = λ f → pullˡ identityˡ ○ comm ○ ⟺ (pullˡ identityˡ)
--     }

--   extranatural-commˡ : (β : DinaturalTrans F (const A)) →
--                        α β X ∘ F₁ (f , C.id) ≈ α β Y ∘ F₁ (C.id , f)
--   extranatural-commˡ {f = f} β = ⟺ (pullˡ identityˡ) ○ hexagon β f ○ pullˡ identityˡ

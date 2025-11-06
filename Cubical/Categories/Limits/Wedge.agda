{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Limits.Wedge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Cospan
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Functor.Bifunctor
open import Cubical.Categories.NaturalTransformation.Dinatural
open import Cubical.Categories.Functors.Constant 
open import Cubical.Categories.Constructions.BinProduct 

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (F : Bifunctor (C ^op) C D) where
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    Const = Constant (C ^op ×C C) D 

  module Wedge where
    record Wedge : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
      field
        E         : D.ob
        dinatural : DinaturalTrans {C = C} (Const E) F
      open DinaturalTrans dinatural public
    open Wedge
    open DinaturalTrans
    retract : {A : D.ob} (W : Wedge) → D [ A , W .E ] → Wedge
    retract {A = A} W f .E = A
    retract {A = A} W f .dinatural .α X = f D.⋆ α W X
    retract {A = A} W f .dinatural .hexagon {X} {Y} g =
      D.id D.⋆ ((f D.⋆ α W X) D.⋆ F₁ (C.id , g))
        ≡⟨ D.⋆IdL _ ⟩
      (f D.⋆ α W X) D.⋆ F₁ (C.id , g)
        ≡⟨ D.⋆Assoc f (α W X) (F₁ (C.id , g)) ⟩
      f D.⋆ (α W X D.⋆ F₁ (C.id , g))
        ≡⟨ cong (f D.⋆_) (sym (D.⋆IdL _)) ⟩
      f D.⋆ (D.id D.⋆ (α W X D.⋆ F₁ (C.id , g)))
        ≡⟨ cong (f D.⋆_) (W .hexagon g) ⟩
      f D.⋆ (D.id D.⋆ (α W Y D.⋆ F₁ (g , C.id)))
        ≡⟨ cong (f D.⋆_) (D.⋆IdL _) ⟩
      f D.⋆ (α W Y D.⋆ F₁ (g , C.id))
        ≡⟨ sym (D.⋆Assoc _ _ _) ⟩
      (f D.⋆ α W Y) D.⋆ F₁ (g , C.id)
        ≡⟨ sym (D.⋆IdL _) ⟩
      D.id D.⋆ ((f D.⋆ α W Y) D.⋆ F₁ (g , C.id)) ∎
      where open Functor F using () renaming (F-hom to F₁)

    record Morphism (W W' : Wedge)
         : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
      private
        module W = Wedge W
        module W' = Wedge W'
      field
        u : D [ W.E , W'.E ]
        triangle : ∀ {X} → u D.⋆ W'.α X ≡ W.α X
    open Morphism

    id : {W : Wedge} → Morphism W W
    id {W} .u = D.id
    id {W} .triangle = D.⋆IdL _

    private
      variable
        W₁ W₂ W₃ W₄ : Wedge

    _⋆_ : Morphism W₁ W₂ → Morphism W₂ W₃ → Morphism W₁ W₃
    (f ⋆ g) .u = f .u D.⋆ g .u
    _⋆_ {W₁} {W₂} {W₃} f g .triangle {X} =
      (f .u D.⋆ g .u) D.⋆ α W₃ X
        ≡⟨ D.⋆Assoc _ _ _ ⟩
      f .u D.⋆ (g .u D.⋆ α W₃ X)
        ≡⟨ cong (f .u D.⋆_) (g .triangle) ⟩
      f .u D.⋆ α W₂ X
        ≡⟨ f .triangle ⟩
      α W₁ X ∎

    Morphism≡ : {f g : Morphism W₁ W₂}
              → f .u ≡ g .u → f ≡ g
    Morphism≡ p i .u = p i
    Morphism≡ p i .triangle = D.isSetHom _ _ _ _ i

    ⋆IdL : (f : Morphism W₁ W₂) → id ⋆ f ≡ f
    ⋆IdL f = Morphism≡ (D.⋆IdL (f .u))

    ⋆IdR : (f : Morphism W₁ W₂) → f ⋆ id ≡ f
    ⋆IdR f = Morphism≡ (D.⋆IdR (f .u))

    ⋆Assoc
      : (f : Morphism W₁ W₂) (g : Morphism W₂ W₃) (h : Morphism W₃ W₄)
      → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
    ⋆Assoc f g h = Morphism≡ (D.⋆Assoc _ _ _) 

    isSetHom : isSet (Morphism W₁ W₂)
    isSetHom f g p q i j .u =
      D.isSetHom (f .u) (g .u) (λ j → p j .u) (λ j → q j .u) i j
    isSetHom {W₁ = W₁} {W₂ = W₂} f g p q i j .triangle {X} =
      {!v i j!}
      where
        p' : f .u ≡ g .u
        p' = λ j → p j .u
        q' : f .u ≡ g .u
        q' = λ j → q j .u
        isSet-u : (λ j → p j .u) ≡ (λ j → q j .u)
        isSet-u = D.isSetHom (f .u) (g .u) (λ j → p j .u) (λ j → q j .u)
        Triangle : D [ W₁ .E , W₂ .E ] → Type _
        Triangle f = f D.⋆ α W₂ X ≡ α W₁ X
        s : ∀ i → Triangle (p' i) ≡ Triangle (q' i)
        s i = {!!}
        w : ∀ i j → Triangle (isSet-u i j)
        w = congP {A = λ i → {!!}}
                  {B = λ i f → {!!}} (λ i a → {!!}) {!!} {!!}
        -- v : isSet→SquareP {A = λ i j → {!Triangle!}} (λ i j → {!D.isSetHom!}) {!!} {!!} {!!} {!!} {!!} {!!} {!!}

    -- isSetHom : isSet (Morphism W₁ W₂)
    -- isSetHom f g p q i j .u =
    --   D.isSetHom (f .u) (g .u) (λ j → p j .u) (λ j → q j .u) i j
    -- isSetHom {W₁ = W₁} {W₂ = W₂} f g p q i j .triangle {X} = {!!}
    --   where
    --     p' : f .u ≡ g .u
    --     p' j = p j .u
    --     q' : f .u ≡ g .u
    --     q' j = q j .u
    --     s : p' ≡ q'
    --     s = D.isSetHom (f .u) (g .u) p' q'
    --     Triangle : D [ W₁ .E , W₂ .E ] → Type _
    --     Triangle f = f D.⋆ α W₂ X ≡ α W₁ X
    --     r : (p : f ≡ g) → PathP (λ i → Triangle (p i .u))
    --                             (f .triangle {X}) (g .triangle {X})
    --     r p = fill {!!} {!!} {!!} {!!}
    --   -- isProp→isSet {!!} {!!} {!!} {!!} {!!} {!!}

  record Cowedge : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      E         : D.ob
      dinatural : DinaturalTrans {C = C} F (Const E)
    open DinaturalTrans dinatural public

    

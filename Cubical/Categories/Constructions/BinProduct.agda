-- Product of two categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.BinProduct where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Isomorphism 
open import Cubical.Categories.Functors.Constant

private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    ℓA'' ℓA''' ℓB'' ℓB''' ℓC'' ℓC''' ℓD'' ℓD''' ℓE'' ℓE''' : Level


open Category

_×C_ : (C : Category ℓC ℓC') → (D : Category ℓD ℓD')
    → Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')

(C ×C D) .ob = (ob C) × (ob D)
(C ×C D) .Hom[_,_] (c , d) (c' , d') = (C [ c , c' ]) × (D [ d , d' ])
(C ×C D) .id = (id C , id D)
(C ×C D) ._⋆_ _ _ = (_ ⋆⟨ C ⟩ _ , _ ⋆⟨ D ⟩ _)
(C ×C D) .⋆IdL _ = ≡-× (⋆IdL C _) (⋆IdL D _)
(C ×C D) .⋆IdR _ = ≡-× (⋆IdR C _) (⋆IdR D _)
(C ×C D) .⋆Assoc _ _ _ = ≡-× (⋆Assoc C _ _ _) (⋆Assoc D _ _ _)
(C ×C D) .isSetHom = isSet× (isSetHom C) (isSetHom D)

infixr 5 _×C_

open Functor

Fst : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C ×C D) C
F-ob (Fst C D) = fst
F-hom (Fst C D) = fst
F-id (Fst C D) = refl
F-seq (Fst C D) _ _ = refl

Snd : (C : Category ℓC ℓC') → (D : Category ℓD ℓD') → Functor (C ×C D) D
F-ob (Snd C D) = snd
F-hom (Snd C D) = snd
F-id (Snd C D) = refl
F-seq (Snd C D) _ _ = refl

module _ where
  private
    variable
      A : Category ℓA ℓA'
      B : Category ℓB ℓB'
      C : Category ℓC ℓC'
      D : Category ℓD ℓD'
      E : Category ℓE ℓE'
      C' : Category ℓA'' ℓA'''
      D' : Category ℓD'' ℓD'''
      E' : Category ℓE'' ℓE'''

  open Functor

  _,F_ : Functor C D → Functor C E → Functor C (D ×C E)
  (G ,F H) .F-ob a = (G ⟅ a ⟆ , H ⟅ a ⟆)
  (G ,F H) .F-hom g = (G ⟪ g ⟫ , H ⟪ g ⟫)
  (G ,F H) .F-id = ≡-× (G .F-id) (H .F-id)
  (G ,F H) .F-seq _ _ = ≡-× (G .F-seq _ _) (H .F-seq _ _)

  _×F_ : Functor A C → Functor B D → Functor (A ×C B) (C ×C D)
  _×F_ {A = A} {B = B} G H = G ∘F Fst A B ,F H ∘F Snd A B

Δ : ∀ (C : Category ℓC ℓC') → Functor C (C ×C C)
Δ C = Id ,F Id

Sym : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} → Functor (C ×C D) (D ×C C)
Sym {C = C}{D = D} = Snd C D ,F Fst C D

-- Some useful functors
module _ (C : Category ℓC ℓC')
         (D : Category ℓD ℓD') where
  open Functor

  module _ (E : Category ℓE ℓE') where
    open isFunctorIso

    -- Associativity of product
    ×C-assoc : Functor (C ×C (D ×C E)) ((C ×C D) ×C E)
    ×C-assoc .F-ob (c , (d , e)) = ((c , d), e)
    ×C-assoc .F-hom (f , (g , h)) = ((f , g), h)
    ×C-assoc .F-id = refl
    ×C-assoc .F-seq _ _ = refl

    ×C-assoc⁻ : Functor ((C ×C D) ×C E) (C ×C (D ×C E))
    ×C-assoc⁻ .F-ob ((c , d) , e) = (c , (d , e))
    ×C-assoc⁻ .F-hom ((f , g) , h) = (f , (g , h))
    ×C-assoc⁻ .F-id = refl
    ×C-assoc⁻ .F-seq _ _ = refl

    assoc≅ꟳ : (C ×C (D ×C E)) ≅ꟳ ((C ×C D) ×C E)
    assoc≅ꟳ = ×C-assoc , mkFunctorIso ×C-assoc⁻ li ri
      where
      li : ×C-assoc ∘F ×C-assoc⁻ ≡ Id
      li = Functor≡ (λ _ → refl) p
        where
          p : ∀ {c c'} (f : ((C ×C D) ×C E) [ c , c' ])
            → F-hom (×C-assoc ∘F ×C-assoc⁻) f
            ≡ F-hom (Id {C = ((C ×C D) ×C E)}) {x = c} {y = c'} f
          p f = refl

      ri : ×C-assoc⁻ ∘F ×C-assoc ≡ Id
      ri = Functor≡ (λ _ → refl) q
        where
          q : ∀ {c c'} (f : (C ×C (D ×C E)) [ c , c' ])
            → F-hom (×C-assoc⁻ ∘F ×C-assoc) f
            ≡ F-hom (Id {C = (C ×C (D ×C E))}) {x = c} {y = c'} f
          q f = refl
    

  -- Left/right injections into product
  linj : (d : ob D) → Functor C (C ×C D)
  linj d = Id ,F Constant C D d

  rinj : (c : ob C) → Functor D (C ×C D)
  rinj c = Constant D C c ,F Id

{-
  TODO:
    - define inverse to `assoc`, prove isomorphism
    - prove product is commutative up to isomorphism
-}


  -- The isomorphisms in product category

  open isIso

  CatIso× : {x y : C .ob}{z w : D .ob} → CatIso C x y → CatIso D z w → CatIso (C ×C D) (x , z) (y , w)
  CatIso× f g .fst = f .fst , g .fst
  CatIso× f g .snd .inv = f .snd .inv , g .snd .inv
  CatIso× f g .snd .sec i = f .snd .sec i , g .snd .sec i
  CatIso× f g .snd .ret i = f .snd .ret i , g .snd .ret i

  Id×Id≡Id : Id {C = C} ×F Id {C = D} ≡ Id {C = C ×C D}
  Id×Id≡Id =
    Functor≡
      (λ (c , d) → refl)
      (λ (f , g) → refl)


module _
      {C : Category ℓC ℓC'}
      {D : Category ℓD ℓD'}
      {E : Category ℓE ℓE'}
      {C' : Category ℓA'' ℓA'''}
      {D' : Category ℓD'' ℓD'''}
      {E' : Category ℓE'' ℓE'''} where

  open Functor

  ×F-comp-distrib : (F : Functor C D) (G : Functor C' D')
                  → (F' : Functor D E) (G' : Functor D' E')
                  → (F' ×F G') ∘F (F ×F G) ≡ (F' ∘F F) ×F (G' ∘F G)
  ×F-comp-distrib F G F' G' =
    Functor≡ (λ x → refl) (λ f → refl)

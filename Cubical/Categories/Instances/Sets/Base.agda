{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Structure

open import Cubical.Categories.Limits

open Category hiding (_∘_)

module _ ℓ where
  SET : Category (ℓ-suc ℓ) ℓ
  ob SET = hSet ℓ
  Hom[_,_] SET (A , _) (B , _) = A → B
  id SET x = x
  _⋆_ SET f g x = g (f x)
  ⋆IdL SET f = refl
  ⋆IdR SET f = refl
  ⋆Assoc SET f g h = refl
  isSetHom SET {A} {B} = isSetΠ (λ _ → snd B)

private
  variable
    ℓ ℓ' ℓI ℓI' : Level

open Functor

-- Hom functors
_[-,_] : (C : Category ℓ ℓ') → (c : C .ob) → Functor (C ^op) (SET ℓ')
(C [-, c ]) .F-ob x    = (C [ x , c ]) , C .isSetHom
(C [-, c ]) .F-hom f k = f ⋆⟨ C ⟩ k
(C [-, c ]) .F-id      = funExt λ _ → C .⋆IdL _
(C [-, c ]) .F-seq _ _ = funExt λ _ → C .⋆Assoc _ _ _

_[_,-] : (C : Category ℓ ℓ') → (c : C .ob)→ Functor C (SET ℓ')
(C [ c ,-]) .F-ob x    = (C [ c , x ]) , C .isSetHom
(C [ c ,-]) .F-hom f k = k ⋆⟨ C ⟩ f
(C [ c ,-]) .F-id      = funExt λ _ → C .⋆IdR _
(C [ c ,-]) .F-seq _ _ = funExt λ _ → sym (C .⋆Assoc _ _ _)

-- Lift functor
LiftF : Functor (SET ℓ) (SET (ℓ-max ℓ ℓ'))
LiftF {ℓ}{ℓ'} .F-ob A = (Lift {ℓ}{ℓ'} (A .fst)) , isOfHLevelLift 2 (A .snd)
LiftF .F-hom f x = lift (f (x .lower))
LiftF .F-id = refl
LiftF .F-seq f g = funExt λ x → refl

module _ {ℓ ℓ' : Level} where
  isFullyFaithfulLiftF : isFullyFaithful (LiftF {ℓ} {ℓ'})
  isFullyFaithfulLiftF X Y = isoToIsEquiv LiftFIso
    where
    open Iso
    LiftFIso : Iso (X .fst → Y .fst)
                   (Lift {ℓ}{ℓ'} (X .fst) → Lift {ℓ}{ℓ'} (Y .fst))
    fun LiftFIso = LiftF .F-hom {X} {Y}
    inv LiftFIso = λ f x → f (lift x) .lower
    rightInv LiftFIso = λ _ → funExt λ _ → refl
    leftInv LiftFIso = λ _ → funExt λ _ → refl

module _ {C : Category ℓ ℓ'} {F : Functor C (SET ℓ')} where
  open NatTrans

  -- natural transformations by pre/post composition
  preComp : {x y : C .ob}
          → (f : C [ x , y ])
          → C [ x ,-] ⇒ F
          → C [ y ,-] ⇒ F
  preComp f α .N-ob c k = (α ⟦ c ⟧) (f ⋆⟨ C ⟩ k)
  preComp f α .N-hom {x = c} {d} k
    = (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ (l ⋆⟨ C ⟩ k)))
    ≡[ i ]⟨ (λ l → (α ⟦ d ⟧) (⋆Assoc C f l k (~ i))) ⟩
      (λ l → (α ⟦ d ⟧) (f ⋆⟨ C ⟩ l ⋆⟨ C ⟩ k))
    ≡[ i ]⟨ (λ l → (α .N-hom k) i (f ⋆⟨ C ⟩ l)) ⟩
      (λ l → (F ⟪ k ⟫) ((α ⟦ c ⟧) (f ⋆⟨ C ⟩ l)))
    ∎

-- properties
-- TODO: move to own file
open isIso renaming (inv to cInv)
open Iso

module _ {A B : (SET ℓ) .ob } where

  Iso→CatIso : Iso (fst A) (fst B)
             → CatIso (SET ℓ) A B
  Iso→CatIso is .fst = is .fun
  Iso→CatIso is .snd .cInv = is .inv
  Iso→CatIso is .snd .sec = funExt λ b → is .rightInv b -- is .rightInv
  Iso→CatIso is .snd .ret = funExt λ b → is .leftInv b -- is .rightInv

  CatIso→Iso : CatIso (SET ℓ) A B
             → Iso (fst A) (fst B)
  CatIso→Iso cis .fun = cis .fst
  CatIso→Iso cis .inv = cis .snd .cInv
  CatIso→Iso cis .rightInv = funExt⁻ λ b → cis .snd .sec b
  CatIso→Iso cis .leftInv  = funExt⁻ λ b → cis .snd .ret b


  Iso-Iso-CatIso : Iso (Iso (fst A) (fst B)) (CatIso (SET ℓ) A B)
  fun Iso-Iso-CatIso = Iso→CatIso
  inv Iso-Iso-CatIso = CatIso→Iso
  rightInv Iso-Iso-CatIso b = refl
  fun (leftInv Iso-Iso-CatIso a i) = fun a
  inv (leftInv Iso-Iso-CatIso a i) = inv a
  rightInv (leftInv Iso-Iso-CatIso a i) = rightInv a
  leftInv (leftInv Iso-Iso-CatIso a i) = leftInv a

  Iso-CatIso-≡ : Iso (CatIso (SET ℓ) A B) (A ≡ B)
  Iso-CatIso-≡ = compIso (invIso Iso-Iso-CatIso) (hSet-Iso-Iso-≡ _ _)

-- SET is univalent

isUnivalentSET : isUnivalent {ℓ' = ℓ} (SET _)
isUnivalent.univ isUnivalentSET (A , isSet-A) (B , isSet-B)  =
   precomposesToId→Equiv
      pathToIso _ (funExt w) (isoToIsEquiv Iso-CatIso-≡)
   where
     w : _
     w ci =
       invEq
         (congEquiv (isoToEquiv (invIso Iso-Iso-CatIso)))
         (SetsIso≡-ext isSet-A isSet-B
            (λ x i → transp (λ _ → B) i (ci .fst (transp (λ _ → A) i x)))
            (λ x i → transp (λ _ → A) i (ci .snd .cInv (transp (λ _ → B) i x))))

module _ {A}{B} (f : CatIso (SET ℓ) A B) a where
  open isUnivalent
  -- univalence of SET behaves as expected
  univSetβ : transport (cong fst (CatIsoToPath isUnivalentSET f)) a
             ≡ f .fst a
  univSetβ = (transportRefl _
    ∙ transportRefl _
    ∙ transportRefl _
    ∙ cong (f .fst) (transportRefl _ ∙ transportRefl _ ))


-- SET is complete
open LimCone
open Cone

completeSET : ∀ {ℓJ ℓJ'} → Limits {ℓJ} {ℓJ'} (SET (ℓ-max ℓJ ℓJ'))
lim (completeSET J D) = Cone D (Unit* , isOfHLevelLift 2 isSetUnit) , isSetCone D _
coneOut (limCone (completeSET J D)) j e = coneOut e j tt*
coneOutCommutes (limCone (completeSET J D)) j i e = coneOutCommutes e j i tt*
univProp (completeSET J D) c cc =
  uniqueExists
    (λ x → cone (λ v _ → coneOut cc v x) (λ e i _ → coneOutCommutes cc e i x))
    (λ _ → funExt (λ _ → refl))
    (λ x → isPropIsConeMor cc (limCone (completeSET J D)) x)
    (λ x hx → funExt (λ d → cone≡ λ u → funExt (λ _ → sym (funExt⁻ (hx u) d))))



module _ {ℓ} where

-- While pullbacks can be obtained from limits
-- (using `completeSET` & `LimitsOfShapeCospanCat→Pullbacks` from `Cubical.Categories.Limits.Pullback`),
-- this direct construction can be more convenient when only pullbacks are needed.
-- It also has better behavior in terms of inferring implicit arguments

 open Pullback

 PullbacksSET : Pullbacks (SET ℓ)
 PullbacksSET (cospan l m r s₁ s₂) = pb
  where
  pb : Pullback (SET ℓ) (cospan l m r s₁ s₂)
  pbOb pb = _ , isSetΣ (isSet× (snd l) (snd r))
   (uncurry λ x y → isOfHLevelPath 2 (snd m) (s₁ x) (s₂ y))
  pbPr₁ pb = fst ∘ fst
  pbPr₂ pb = snd ∘ fst
  pbCommutes pb = funExt snd
  fst (fst (univProp pb h k H')) d = _ , (H' ≡$ d)
  snd (fst (univProp pb h k H')) = refl , refl
  snd (univProp pb h k H') y =
   Σ≡Prop
    (λ _ → isProp× (isSet→ (snd l) _ _) (isSet→ (snd r) _ _))
     (funExt λ x → Σ≡Prop (λ _ → (snd m) _ _)
        λ i → fst (snd y) i x , snd (snd y) i x)

-- LiftF : SET ℓ → SET (ℓ-suc ℓ) preserves "small" limits
-- i.e. limits over diagram shapes J : Category ℓ ℓ
module _ {ℓ : Level} where
  preservesLimitsLiftF : preservesLimits {ℓJ = ℓ} {ℓJ' = ℓ} (LiftF {ℓ} {ℓ-suc ℓ})
  preservesLimitsLiftF = preservesLimitsChar _
                           completeSET
                           completeSETSuc
                           limSetIso
                           λ _ _ _ → refl
    where
    -- SET (ℓ-suc ℓ) has limits over shapes J : Category ℓ ℓ
    completeSETSuc : Limits {ℓJ = ℓ} {ℓJ' = ℓ} (SET (ℓ-suc ℓ))
    lim (completeSETSuc J D) = Cone D (Unit* , isOfHLevelLift 2 isSetUnit) , isSetCone D _
    coneOut (limCone (completeSETSuc J D)) j e = coneOut e j tt*
    coneOutCommutes (limCone (completeSETSuc J D)) j i e = coneOutCommutes e j i tt*
    univProp (completeSETSuc J D) c cc =
      uniqueExists
        (λ x → cone (λ v _ → coneOut cc v x) (λ e i _ → coneOutCommutes cc e i x))
        (λ _ → funExt (λ _ → refl))
        (λ x → isPropIsConeMor cc (limCone (completeSETSuc J D)) x)
        (λ x hx → funExt (λ d → cone≡ λ u → funExt (λ _ → sym (funExt⁻ (hx u) d))))

    lowerCone : ∀ J D
             → Cone (LiftF ∘F D) (Unit* , isOfHLevelLift 2 isSetUnit)
             → Cone D (Unit* , isOfHLevelLift 2 isSetUnit)
    coneOut (lowerCone J D cc) v tt* = cc .coneOut v tt* .lower
    coneOutCommutes (lowerCone J D cc) e =
      funExt λ { tt* → cong lower (funExt⁻ (cc .coneOutCommutes e) tt*) }

    liftCone : ∀ J D
             → Cone D (Unit* , isOfHLevelLift 2 isSetUnit)
             → Cone (LiftF ∘F D) (Unit* , isOfHLevelLift 2 isSetUnit)
    coneOut (liftCone J D cc) v tt* = lift (cc .coneOut v tt*)
    coneOutCommutes (liftCone J D cc) e =
      funExt λ { tt* → cong lift (funExt⁻ (cc .coneOutCommutes e) tt*) }

    limSetIso : ∀ J D → CatIso (SET (ℓ-suc ℓ))
                                (completeSETSuc J (LiftF ∘F D) .lim)
                                (LiftF  .F-ob (completeSET J D .lim))
    fst (limSetIso J D) cc = lift (lowerCone J D cc)
    cInv (snd (limSetIso J D)) cc = liftCone J D (cc .lower)
    sec (snd (limSetIso J D)) = funExt (λ _ → liftExt (cone≡ λ _ → refl))
    ret (snd (limSetIso J D)) = funExt (λ _ → cone≡ λ _ → refl)

open import Cubical.Categories.Instances.Discrete

hSet→hGroupoid : hSet ℓ → hGroupoid ℓ
hSet→hGroupoid (X , isSet) = X , isSet→isGroupoid isSet

DiscreteDiagram
  : (J : hSet ℓ) (J' : ⟨ J ⟩ → hSet ℓ')
  → Functor (DiscreteCategory (hSet→hGroupoid J)) (SET ℓ')
DiscreteDiagram J J' .F-ob x = J' x
DiscreteDiagram J J' .F-hom f x' =
  subst (λ ○ → ⟨ J' ○ ⟩) f x'
DiscreteDiagram J J' .F-id =
  funExt transportRefl
DiscreteDiagram J J' .F-seq {x} {y} {z} f g i w =
  substComposite (λ ○ → ⟨ J' ○ ⟩) f g w i

-- module DiscreteColimit
--   {ℓ ℓ'}
--   (J : hSet ℓ) (J' : ⟨ J ⟩ → hSet ℓ')
--   where

--   open import Cubical.HITs.SetTruncation

--   record DiscreteCocone : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
--     field
--       apex : hSet (ℓ-max ℓ ℓ')
--       leg : ∀ j → ⟨ J' j ⟩ → ⟨ apex ⟩

--   open DiscreteCocone

--   isLimitingCocone : DiscreteCocone → Type (ℓ-max ℓ (ℓ-suc ℓ'))
--   isLimitingCocone L = ∀ D → ∃![ f ∈ (⟨ L .apex ⟩ → ⟨ D .apex ⟩) ] (∀ j → f ∘ L .leg j ≡ D .leg j)

--   Colimit : Type (ℓ-max ℓ (ℓ-suc ℓ'))
--   Colimit = Σ DiscreteCocone isLimitingCocone

--   data RawApex : Type (ℓ-max ℓ (ℓ')) where
--     _,_ : (j : ⟨ J ⟩) (x : ⟨ J' j ⟩) → RawApex
--     glue : (i j : ⟨ J ⟩) (x : ⟨ J' j ⟩)

--   Apex = ∥ RawApex ∥₂

--   L : DiscreteCocone
--   L .apex = Apex , isSetSetTrunc
--   L .leg = λ j x → ∣ j , x ∣₂

--   L' : DiscreteCocone
--   L' .apex = RawApex , _
--   L' .leg = λ j x → j , x

--   isLimitL : isLimitingCocone L
--   isLimitL D .fst .fst ∣ j , x ∣₂ = D .leg j x
--   isLimitL D .fst .fst (squash₂ x y p q i j) = {!!}
--   isLimitL D .fst .snd j i x = D .leg j x
--   isLimitL D .snd (f , leg-eq) i .fst x =
--     {!!}
--     where
--     p : isLimitL D .fst .fst x ≡ f x
--     p = {!!}
--   isLimitL D .snd (f , leg-eq) i .snd = {!!}

--   isLimitL' : isLimitingCocone L'
--   isLimitL' D .fst .fst (j , x) = D .leg j x
--   isLimitL' D .fst .snd j i x = D .leg j x
--   isLimitL' D .snd (f , leg-eq) =
--     Σ≡Prop isPropLeg g≡f
--     where
--     isPropLeg : ∀ f →
--                  isProp (∀ j → (λ g → f (L' .leg j g)) ≡ λ g → D .leg j g)
--     isPropLeg f = isPropΠ λ j → isSet→ (D .apex .snd) (λ g → f (L' .leg j g)) (D .leg j) 
--     g≡f : isLimitL' D .fst .fst ≡ f
--     g≡f i (j , x) = {!!}


-- -- i .fst (j , x) = q i
-- --     where
-- --     q : D .leg j x ≡ (f (L' .leg j x))
-- --     q = sym (funExt⁻ (leg-eq j) x)
-- --   isLimitL' D .snd (f , leg-eq) i .snd j =
-- --     funExt p
-- --     where
-- --     p : ∀ x → sym (funExt⁻ (leg-eq j) x) i ≡ D .leg j x
-- --     p x i = {!!}



-- module Colimit {ℓ ℓJ ℓJ'} (J : Category ℓJ ℓJ') (D : Functor J (SET ℓ)) where

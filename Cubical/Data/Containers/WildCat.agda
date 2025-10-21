{-# OPTIONS --lossy-unification --safe #-}

module Cubical.Data.Containers.WildCat where

open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Foundations.Prelude hiding (_◁_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

-- I-ary containers
record IContainer {ℓ} (I : Type ℓ)  (ℓ' ℓ'' : Level): Type (ℓ-max ℓ (ℓ-suc (ℓ-max ℓ' ℓ''))) where
  constructor _◁_
  field
    S : Type ℓ'
    P : I → S → Type ℓ''

-- Unary containers
Container : (ℓ ℓ' : Level) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
Container ℓ ℓ' = IContainer Unit ℓ ℓ'

open WildCat hiding (_∘_)
open WildFunctor

-- Wild category of I-indexed families of types
module _ {ℓ : Level} (I : Type ℓ) (ℓ' : Level) where

  FamCat : WildCat (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ob FamCat = I → Type ℓ'
  Hom[_,_] FamCat A B = (i : I) → A i → B i
  id FamCat _ x = x
  _⋆_ FamCat f g i x = g i (f i x)
  ⋆IdL FamCat f = refl
  ⋆IdR FamCat f = refl
  ⋆Assoc FamCat f g h = refl

-- I-ary container functors
module ⟦_⟧F {ℓ : Level} (I : Type ℓ) {ℓ' ℓ'' : Level} where

  ⟦_⟧ : IContainer I ℓ' ℓ'' → WildFunctor (FamCat I (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) (TypeCat (ℓ-max (ℓ-max ℓ ℓ') ℓ''))
  F-ob ⟦ S ◁ P ⟧ X = Σ[ s ∈ S ] ((i : I) → P i s → X i)
  fst (F-hom ⟦ S ◁ P ⟧ f (s , g)) = s
  snd (F-hom ⟦ S ◁ P ⟧ f (s , g)) i p = f i (g i p)
  fst (F-id ⟦ S ◁ P ⟧ i (s , g)) = s
  snd (F-id ⟦ S ◁ P ⟧ i (s , g)) = g
  fst (F-seq ⟦ S ◁ P ⟧ f g i (s , h)) = s
  snd (F-seq ⟦ S ◁ P ⟧ f g i (s , h)) j z = g j (f j (h j z))


-- notation for I-container functors
⟦_◁_⟧ob : ∀ {ℓI ℓ ℓ' ℓ''} {I : Type ℓI} (S : Type ℓ) (P : (i : I) (s : S) → Type ℓ') (X : I → Type ℓ'')
  → Type (ℓ-max ℓI (ℓ-max (ℓ-max ℓ ℓ') ℓ''))
⟦ S ◁ P ⟧ob X = Σ[ s ∈ S ] ((i : _) → P i s → X i)

-- Container functor algebra
open ⟦_⟧F Unit

-- notation for unary container functors
⟦_◁_⟧¹ob : ∀ {ℓ ℓ' ℓ''} (S : Type ℓ) (Q : (s : S) → Type ℓ') (X : Type ℓ'')
  → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
⟦ S ◁ Q ⟧¹ob X = Σ[ s ∈ S ] (Q s → X)


record ⟦_⟧-alg {ℓ ℓ' : Level} (C : Container ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    X : Type (ℓ-max ℓ ℓ')
    α : ⟦ C ⟧ .F-ob (λ _ → X) → X

module _ {ℓ ℓ' : Level} where

  Alg⟦_⟧ : (C : Container ℓ ℓ') → WildCat (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ob (Alg⟦ S ◁ P ⟧) = Σ[ X ∈ Type (ℓ-max ℓ ℓ') ] (⟦ S ◁ P ⟧ .F-ob (λ _ → X) → X)
  Hom[_,_] Alg⟦ S ◁ P ⟧ (X , α) (Y , β) = Σ[ f ∈ (X → Y) ] ((f ∘ α) ≡ β ∘ (⟦ S ◁ P ⟧ .F-hom λ _ → f))
  fst (id Alg⟦ S ◁ P ⟧) x = x
  snd (id Alg⟦ S ◁ P ⟧ {x}) i (s , f) = snd x (⟦ S ◁ P ⟧ .F-id (~ i) (s , f))
  fst (_⋆_ Alg⟦ S ◁ P ⟧ {(X , α)} {(Y , β)} {(Z , γ)} (xy , eq1) (yz , eq2)) = yz ∘ xy
  snd (_⋆_ Alg⟦ S ◁ P ⟧ {(X , α)} {(Y , β)} {(Z , γ)} (xy , eq1) (yz , eq2)) =
    funExt λ st → cong yz (funExt⁻ eq1 st) ∙ funExt⁻ eq2 (fst st , (λ _ → xy ∘ st .snd tt))
    ∙ cong γ (funExt⁻ (⟦ S ◁ P ⟧ .F-seq (λ _ → xy) (λ _ → yz)) st)
  ⋆IdL Alg⟦ S ◁ P ⟧ {x = x} {y = y} (xy , eq)  =
    ΣPathP (refl , cong funExt
      (funExt λ f → sym (lUnit _) ∙ sym (rUnit _)))
  ⋆IdR Alg⟦ S ◁ P ⟧ f = ΣPathP (refl , cong funExt (funExt λ x
    → cong₂ _∙_ refl (sym (rUnit _)) ∙ sym (rUnit _)))
  ⋆Assoc Alg⟦ S ◁ P ⟧ {(X , α)} {(Y , β)} {(Z , γ)} (xy , eq1) (yz , eq2)  (zw , eq3) =
    ΣPathP (refl
    , cong funExt (funExt λ x
      → cong₂ _∙_ (cong (cong zw) (cong₂ _∙_ refl (sym (rUnit _))))
                   (sym (rUnit _))
      ∙ sym (cong₂ _∙_ refl (sym (rUnit _) ∙ cong₂ _∙_ refl (sym (rUnit _)))
            ∙ sym (cong₂ _∙_ (cong-∙ zw _ _) refl ∙ sym (assoc _ _ _)))))

  isInitialAlg⟦_⟧ : (C : Container ℓ ℓ') → Alg⟦ C ⟧ .ob → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  isInitialAlg⟦_⟧ C A = (A' : Alg⟦ C ⟧ .ob) → isContr ((Alg⟦ C ⟧ .Hom[_,_]) A A')

module _ {ℓ ℓ' : Level} where

  CoAlg⟦_⟧ : (C : Container ℓ ℓ') → WildCat (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  ob CoAlg⟦ S ◁ P ⟧ = Σ[ X ∈ Type (ℓ-max ℓ ℓ') ] (X → ⟦ S ◁ P ⟧ .F-ob (λ _ → X))
  Hom[_,_] CoAlg⟦ S ◁ P ⟧ (X , α) (Y , β) = Σ[ f ∈ (X → Y) ] ⟦ S ◁ P ⟧ .F-hom (λ _ → f) ∘ α ≡ β ∘ f
  fst (id CoAlg⟦ S ◁ P ⟧) x = x
  snd (id CoAlg⟦ S ◁ P ⟧) = refl
  fst (_⋆_ CoAlg⟦ S ◁ P ⟧ {x = s} (f , fc) (g , gc)) = g ∘ f
  snd (_⋆_ CoAlg⟦ S ◁ P ⟧ {x = s} (f , fc) (g , gc)) = funExt λ x
    → cong (⟦_⟧F.⟦ Unit ⟧ (S ◁ P) .F-hom (λ _ → g)) (funExt⁻ fc x)
    ∙ funExt⁻ gc (f x)
  ⋆IdL CoAlg⟦ S ◁ P ⟧ (f , eq) = ΣPathP (refl , cong funExt (funExt λ x → sym (lUnit _)))
  ⋆IdR CoAlg⟦ S ◁ P ⟧ (f , eq) = ΣPathP (refl , cong funExt (funExt λ x → sym (rUnit _)))
  ⋆Assoc CoAlg⟦ S ◁ P ⟧ (f , eq1) (g , eq2) (h , eq3) =
    ΣPathP (refl , cong funExt (funExt λ x
       → cong₂ _∙_ (cong-∙ (⟦_⟧F.⟦ Unit ⟧ (S ◁ P) .F-hom (λ _ → h)) _ _) refl
       ∙ sym (assoc _ _ _)))

  isTerminalCoAlg⟦_⟧ : (C : Container ℓ ℓ') → CoAlg⟦ C ⟧ .ob → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
  isTerminalCoAlg⟦_⟧ C A = (A' : CoAlg⟦ C ⟧ .ob) → isContr ((CoAlg⟦ C ⟧ .Hom[_,_]) A' A)

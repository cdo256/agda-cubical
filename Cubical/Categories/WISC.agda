module Cubical.Categories.WISC where

open import Cubical.Foundations.Prelude hiding (I)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws 
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Function
open import Cubical.Core.Primitives hiding (I)
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Isomorphism 

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

open Category hiding (_∘_)

Cov : ∀ {ℓ} → (Y : hSet ℓ) → Category (ℓ-suc ℓ) ℓ
Cov {ℓ} Y .ob = Σ[ X ∈ hSet ℓ ] ⟨ X ⟩ ↠ ⟨ Y ⟩  
Cov {ℓ} Y .Hom[_,_] (U , (f , _)) (V , (g , _)) = Σ[ h ∈ (⟨ U ⟩ → ⟨ V ⟩) ] (g ∘ h ≡ f)
Cov {ℓ} Y .id {x = U} = (λ x → x) , refl
Cov {ℓ} Y ._⋆_ (f , L) (g , M) = (g ∘ f) , cong (_∘ f) M ∙ L
Cov {ℓ} Y .⋆IdL (f , L) i = f , rUnit L (~ i)
Cov {ℓ} Y .⋆IdR (f , L) i = f , lUnit L (~ i)
Cov {ℓ} Y .⋆Assoc (f , L) (g , M) (h , N) i = (h ∘ g ∘ f) , p i
  where 
  p : (λ j → N j ∘ g ∘ f) ∙ (λ j → M j ∘ f) ∙ L
    ≡ (λ j → ((λ i₂ → N i₂ ∘ g) ∙ M) j ∘ f) ∙ L
  p =
    (λ j → N j ∘ g ∘ f) ∙ ((λ j → M j ∘ f) ∙ L)
      ≡⟨ assoc _ _ _ ⟩
    ((λ j → N j ∘ g ∘ f) ∙ (λ j → M j ∘ f)) ∙ L
      ≡⟨ cong (_∙ L) refl ⟩
    (λ j → ((λ k → N k ∘ g) ∙ M) j ∘ f) ∙ L ∎
Cov {ℓ} Y .isSetHom {x = U , _} {y = V , _} = isSetΣ (isSet→ (str V)) λ x → isSet→isGroupoid (isSet→ (str Y)) _ _

WeaklyInitialObj : (C : Category ℓ ℓ') → C .ob → Type (ℓ-max ℓ ℓ')
WeaklyInitialObj C x = ∀ y → C [ x , y ] -- Exists morphism to every other element in the category

WeaklyInitialSet : {I : hSet ℓ} (C : Category ℓ ℓ') → (⟨ I ⟩ → C .ob) → Type (ℓ-max ℓ ℓ')
WeaklyInitialSet {I = I} C S = ∀ y → Σ[ i ∈ ⟨ I ⟩ ] C [ S i , y ]

AC : ∀ {ℓ} {ℓ'} {ℓ''} (A : Type ℓ) (B : Type ℓ') (P : A → B → Type ℓ'')
   → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
AC A B P =
    (∀ (a : A) → ∃[ b ∈ B ] P a b)
  → (∃[ f ∈ (A → B) ] (∀ (a : A) → P a (f a)))

record CategoryFamily ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,_
  field
    Idx : hSet ℓ
    Fib : ⟨ Idx ⟩ → hSet ℓ'
⟦_⟧ : CategoryFam ℓ ℓ' → Type (ℓ-max ℓ ℓ')
⟦ Idx , Fib ⟧ = Σ ⟨ Idx ⟩ λ i → ⟨ Fib i ⟩
isSetFam : {F : SetFam ℓ ℓ'} → isSet ⟦ F ⟧
isSetFam {F = Idx , Fib} = isSetΣ (str Idx) λ i → str (Fib i)

record SetFam ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor _,_
  field
    Idx : hSet ℓ
    Fib : ⟨ Idx ⟩ → hSet ℓ'

⟦_⟧ : SetFam ℓ ℓ' → Type (ℓ-max ℓ ℓ')
⟦ Idx , Fib ⟧ = Σ ⟨ Idx ⟩ λ i → ⟨ Fib i ⟩
isSetFam : {F : SetFam ℓ ℓ'} → isSet ⟦ F ⟧
isSetFam {F = Idx , Fib} = isSetΣ (str Idx) λ i → str (Fib i)

WISC : ∀ {ℓ} (Y : hSet ℓ) → Type (ℓ-suc (ℓ-suc ℓ))
WISC Y = Σ (hSet _) (λ I → Σ (⟨ I ⟩ → Cov Y .ob) (WeaklyInitialSet (Cov Y)))

module _ (A : Type ℓ) (B : Type ℓ') (f : B ↠ A) where
  private
    P : A → B → Type _
    P a b = f .fst b ≡ a

  AC-GivesSection : (ac : AC A B P) → ∃[ g ∈ (A → B) ] (section (f .fst) g)
  AC-GivesSection ac = ac (f .snd)

-- postulate
--   wisc : ∀ ℓ → WISC ℓ

-- module _ {ℓ ℓ'} (a!c : A!C ℓ ℓ') where
--   private
--     A : Type _
--     A = Unit*
--     f : (Y : hSet ℓ) → ⟨ Y ⟩ ↠ ⟨ Y ⟩
--     f Y = (λ y → y) , λ y → ∣ y , refl ∣₁

--   isWISC : (Y : hSet ℓ) → WeaklyInitialSet (Cov Y) (λ _ → Y , f Y)
--   isWISC Y (U , g) = Y , {!!} , {!!}
  
--   A!C→WISC : WISC ℓ
--   A!C→WISC Y = A , (λ _ → Y , f Y) , {!!}


-- -- A!C→WISC A!C Y .fst .fst = Y
-- -- A!C→WISC A!C Y .fst .snd = (λ y → y) , λ y → ∣ y , refl ∣₁
-- -- A!C→WISC A!C Y .snd (U , f) .fst = {!!}
-- -- A!C→WISC A!C Y .snd (U , f) .snd = {!!}

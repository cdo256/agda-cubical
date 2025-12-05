module Scratch where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic
open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

prop↔To≡ : ∀ {ℓ} {A B : hProp ℓ} → ⟨ A ⇒ B ⟩ → ⟨ B ⇒ A ⟩ → A ≡ B
prop↔To≡ {A = A} {B = B} A⇒B B⇒A =
  hProp≡ (ua e)
  where
  e : ⟨ A ⟩ ≃ ⟨ B ⟩
  e .fst = A⇒B
  e .snd .equiv-proof b .fst = (B⇒A b) , str B _ b
  e .snd .equiv-proof b .snd (a , fib) = ΣPathP (q , p)
    where
    q : B⇒A b ≡ a
    q = sym (cong B⇒A fib) ∙ str A _ _
    p : (λ i → A⇒B (q i) ≡ b) [ str B (A⇒B (B⇒A b)) b ≡ fib ]
    p = isSet→SquareP (λ _ _ → isProp→isSet (str B)) _ fib (λ i → A⇒B (q i)) λ i → b

module _ {ℓ} {A B : Type ℓ} (isSetA : isSet A) (isSetB : isSet B) where
  isSurjection : (f : A → B) → hProp ℓ
  isSurjection f = ∀[ b ] ∃[ a ] f a ≡ₚ b

  isInjection : (f : A → B) → hProp ℓ
  isInjection f = ∀[ a₁ ] ∀[ a₂ ] f a₁ ≡ₚ f a₂ ⇒ a₁ ≡ₚ a₂ 

  isBijection : (f : A → B) → hProp ℓ
  isBijection f = isSurjection f ⊓ isInjection f
    

  module Bij→Iso (f : A → B) (surj : ⟨ isSurjection f ⟩) (inj : ⟨ isInjection f ⟩) where
    isPropFiber : (b : B) → isProp (fiber f b)
    isPropFiber b (x , inj-x) (y , inj-y) i = x≡y i , inj-x≡inj-y i
      where
      ∣x≡y∣ = inj x y ∣ inj-x ∙ sym inj-y ∣₁
      x≡y = transport (propTruncIdempotent (isSetA x y)) ∣x≡y∣
      inj-x≡inj-y : PathP (λ i → f (x≡y i) ≡ b) inj-x inj-y
      inj-x≡inj-y = isSet→SquareP (λ _ _ → isSetB) inj-x inj-y (cong f x≡y) (λ _ → b)


    isPropIsEquiv'' : (f : A → B) → isProp (isEquiv f)
    isPropIsEquiv'' f e1 e2 i .equiv-proof b = ΣPathP (p , r) i
      where
      p : e1 .equiv-proof b .fst ≡ e2 .equiv-proof b .fst
      p = e1 .equiv-proof b .snd (e2 .equiv-proof b .fst)
      q : (a : A) → (fa≡b : f a ≡ b)
        → (λ i → p i ≡ (a , fa≡b))
        [ e1 .equiv-proof b .snd (a , fa≡b)
        ≡ e2 .equiv-proof b .snd (a , fa≡b) ]
      q a fa≡b = isSet→SquareP (λ _ _ → isSetΣ isSetA λ a → isProp→isSet (isSetB (f a) b)) _ _ _ _
      r : (λ i → (y : fiber f b) → p i ≡ y) [ e1 .equiv-proof b .snd ≡ e2 .equiv-proof b .snd ]
      r i (a , fa≡b) = q a fa≡b i


    isInhabFiber : (b : B) → fiber f b
    isInhabFiber b = S→a S , {!!}
      where
      S : ⟨ ∃[ a ] f a ≡ₚ b ⟩
      S = surj b
      S→a : ⟨ ∃[ a ] f a ≡ₚ b ⟩ → A
      S→a ∣ a , fa≡b ∣₁ = a
      S→a (squash₁ x y i) = p i
        where
        p : S→a x ≡ S→a y
        p = {!!}


    -- inflateFiber : (f : A → B) (b : B) → f a ≡ₚ b → f a ≡ b
    -- inflateFiber f b = {!!}


    contrFib : (f : A → B) (b : B) → isContr (fiber f b)
    contrFib f b = {!inhab!} , {!uniq!}
      where
      inhab : ⟨ ∃[ a ] f a ≡ₚ b ⟩ → fiber f b
      inhab ∣ a , fa≡b ∣₁ = a , {!!}
      inhab (squash₁ x x₁ i) = {!!}
      uniq : ∀ y → inhab ≡ y
      uniq y = {!isPropFiber f y!}



  Bij→Iso : (f : A → B) → hProp ℓ
  Bij→Iso f = isBijection f ⇒ ∥ isIso f ∥ₚ


  
  
  bij→iso : ∀ f → ⟨ Bij→Iso f ⟩
  bij→iso f = ⇒i imp
    where
    imp : ⟨ isBijection f ⟩ → ⟨ ∥ isIso f ∥ₚ ⟩
    imp (surj , inj) = ∣ {!!} , {!!} ∣₁
      where
      eq : isEquiv f
      eq .equiv-proof b = ((let w = surj b in {!!}) , {!!}) , {!!}
      -- e : A ≃ B
      -- e = f , eq
      -- g : B → A
      -- g b = {!!}

isContrSingl' : ∀ {ℓ} {A : Type ℓ} (a : A) → isContr (singl a)
isContrSingl' a = (a , refl) , prop
  where
  prop : ∀ (b̂ : singl a) → (a , refl) ≡ b̂
  prop (b , p) i = (p i) , λ j → p (i ∧ j)


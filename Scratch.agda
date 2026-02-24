module Scratch where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence 
open import Cubical.Foundations.Structure
-- open import Cubical.Functions.Logic
-- open import Cubical.Data.Equality

open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Bool as 𝟚 renaming (Bool to 𝟚) 
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation



module DNE where
  DNE : Type₁
  DNE = (A : Type) → ((A → ⊥) → ⊥) → A

  -- Double negation of Booleans is inhabited
  notnotBool : (𝟚 → ⊥) → ⊥
  notnotBool h = h true

  ¬DNE : DNE → ⊥
  ¬DNE dne = 
    let
      f : (A : Type) → ((A → ⊥) → ⊥) → A
      f = dne

      -- Point in 𝟚 calculated by dne
      b : 𝟚
      b = f 𝟚 notnotBool

      -- The path p : 𝟚 ≡ 𝟚 induced by 'not'
      p : 𝟚 ≡ 𝟚
      p = {!!}

      -- Action of f on the path p
      -- f p : PathOver (λ X → (¬¬ X → X)) p (f 𝟚) (f 𝟚)
      pathOver : PathP (λ i → ((p i → ⊥) → ⊥) → p i) (f 𝟚) (f 𝟚)
      pathOver = λ i → dne (p i) -- or simply: λ i → dne (p i)

      -- Apply to a generic double negation inhabitant
      -- Since ¬¬ A is a proposition, we don't care about the specific path there
      sq : PathP (λ i → p i) (f 𝟚 (λ h → h true)) (f 𝟚 (λ h → h (transport p true)))
      sq i = pathOver i (λ h → h (transport-filler p true i))

      -- Simplified: transport p b ≡ b
      eq : transport p b ≡ b
      eq = ?
      -- eq = transport (λ i → p i) b              ≡[ i ]≡ pathOver i (λ _ → dne (p i) (λ h → h (p i))) -- conceptual

      -- -- Direct calculation:
      -- res : not b ≡ b
      -- res = 
      --   not b                                   ≡⟨ (λ i → transportRefl (not b) i) ⟩
      --   transport refl (not b)                  ≡⟨ (λ i → transport (λ j → p (~ i ∨ j)) (not b)) ⟩
      --   transport p b                           ≡⟨ (λ i → transport (λ j → p j) (f 𝟚 notnotBool)) ⟩
      --   f 𝟚 (transport (λ j → ((p j → ⊥) → ⊥)) p notnotBool) ≡⟨ refl ⟩ -- by f p
      --   b
    in {!!} -- falseNotTrue (sym (boolHasNoFixedPoint b res))
    

-- module AnyTrees where
--   open import Cubical.Data.Nat
--   open import Cubical.Data.Bool
--   𝓘 = Bool
--   data AnyTree : Type (ℓ-suc ℓ-zero) where
--     leaf : AnyTree
--     node : (X : Type) → ∥ X ≡ 𝓘 ∥₁ → (X → AnyTree) → AnyTree

--   fork : AnyTree → AnyTree → AnyTree
--   fork s t = node Bool ∣ refl ∣₁ (if_then s else t)

--   fork-swap : ∀ s t → fork s t ≡ fork t s
--   fork-swap s t = {!!}
--     where
--     p : node Bool ∣ refl ∣₁ (if_then s else t) ≡ node Bool ∣ notEq ∣₁ (if_then s else t)
--     p = λ i → node Bool (squash₁ ∣ refl ∣₁ ∣ notEq ∣₁ i) (if_then s else t)
--     q : node Bool ∣ notEq ∣₁ (if_then s else t) ≡ node Bool ∣ refl ∣₁ (if_then t else s)
--     q = cong₂ (node Bool) (squash₁ ∣ notEq ∣₁ ∣ refl ∣₁) λ i b → {!!}

-- module AnyTrees3 where
--   open import Cubical.Data.Nat
--   open import Cubical.Data.Bool
--   open import Cubical.Relation.Nullary.Base 
--   𝓘 = Bool
--   data AnyTree : Type (ℓ-suc ℓ-zero) where
--     leaf : AnyTree
--     node : (((X : Type) → Dec X → ∥ X ≡ 𝓘 ∥₁ → X) → AnyTree) → AnyTree

--   fork : AnyTree → AnyTree → AnyTree
--   fork s t = node λ x → {!!}

--   --- fork-swap : ∀ s t → fork s t ≡ fork t s
--   --- fork-swap s t = {!!}
--   ---   where
--   ---   p : node Bool ∣ refl ∣₁ (if_then s else t) ≡ node Bool ∣ notEq ∣₁ (if_then s else t)
--   ---   p = λ i → node Bool (squash₁ ∣ refl ∣₁ ∣ notEq ∣₁ i) (if_then s else t)
--   ---   q : node Bool ∣ notEq ∣₁ (if_then s else t) ≡ node Bool ∣ refl ∣₁ (if_then t else s)
--   ---   q = cong₂ (node Bool) (squash₁ ∣ notEq ∣₁ ∣ refl ∣₁) λ i b → {!!}

-- module AnyTrees2 where
--   open import Cubical.Data.Nat
--   open import Cubical.Data.Bool
--   data AnyTree : Type (ℓ-suc ℓ-zero) where
--     leaf : AnyTree
--     node : (X : Type) → X ≡ Bool → (X → AnyTree) → AnyTree

--   fork : AnyTree → AnyTree → AnyTree
--   fork s t = node Bool refl (if_then s else t)

--   fork-swap : ∀ s t → fork s t ≡ fork t s
--   fork-swap s t = {!!}
--     -- where
--     -- p : node Bool ∣ refl ∣₁ (if_then s else t) ≡ node Bool ∣ notEq ∣₁ (if_then s else t)
--     -- p = λ i → node Bool (squash₁ ∣ refl ∣₁ ∣ notEq ∣₁ i) (if_then s else t)
--     -- q : node Bool ∣ notEq ∣₁ (if_then s else t) ≡ node Bool ∣ refl ∣₁ (if_then t else s)
--     -- q = cong₂ (node Bool) (squash₁ ∣ notEq ∣₁ ∣ refl ∣₁) λ i b → {!!}

-- prop↔To≡ : ∀ {ℓ} {A B : hProp ℓ} → ⟨ A ⇒ B ⟩ → ⟨ B ⇒ A ⟩ → A ≡ B
-- prop↔To≡ {A = A} {B = B} A⇒B B⇒A =
--   hProp≡ (ua e)
--   where
--   e : ⟨ A ⟩ ≃ ⟨ B ⟩
--   e .fst = A⇒B
--   e .snd .equiv-proof b .fst = (B⇒A b) , str B _ b
--   e .snd .equiv-proof b .snd (a , fib) = ΣPathP (q , p)
--     where
--     q : B⇒A b ≡ a
--     q = sym (cong B⇒A fib) ∙ str A _ _
--     p : (λ i → A⇒B (q i) ≡ b) [ str B (A⇒B (B⇒A b)) b ≡ fib ]
--     p = isSet→SquareP (λ _ _ → isProp→isSet (str B)) _ fib (λ i → A⇒B (q i)) λ i → b

-- module _ {ℓ} {A B : Type ℓ} (isSetA : isSet A) (isSetB : isSet B) where
--   isSurjection : (f : A → B) → hProp ℓ
--   isSurjection f = ∀[ b ] ∃[ a ] f a ≡ₚ b

--   isInjection : (f : A → B) → hProp ℓ
--   isInjection f = ∀[ a₁ ] ∀[ a₂ ] f a₁ ≡ₚ f a₂ ⇒ a₁ ≡ₚ a₂ 

--   isBijection : (f : A → B) → hProp ℓ
--   isBijection f = isSurjection f ⊓ isInjection f
    

--   module Bij→Iso (f : A → B) (surj : ⟨ isSurjection f ⟩) (inj : ⟨ isInjection f ⟩) where
--     isPropFiber : (b : B) → isProp (fiber f b)
--     isPropFiber b (x , inj-x) (y , inj-y) i = x≡y i , inj-x≡inj-y i
--       where
--       ∣x≡y∣ = inj x y ∣ inj-x ∙ sym inj-y ∣₁
--       x≡y = transport (propTruncIdempotent (isSetA x y)) ∣x≡y∣
--       inj-x≡inj-y : PathP (λ i → f (x≡y i) ≡ b) inj-x inj-y
--       inj-x≡inj-y = isSet→SquareP (λ _ _ → isSetB) inj-x inj-y (cong f x≡y) (λ _ → b)


--     isPropIsEquiv'' : (f : A → B) → isProp (isEquiv f)
--     isPropIsEquiv'' f e1 e2 i .equiv-proof b = ΣPathP (p , r) i
--       where
--       p : e1 .equiv-proof b .fst ≡ e2 .equiv-proof b .fst
--       p = e1 .equiv-proof b .snd (e2 .equiv-proof b .fst)
--       q : (a : A) → (fa≡b : f a ≡ b)
--         → (λ i → p i ≡ (a , fa≡b))
--         [ e1 .equiv-proof b .snd (a , fa≡b)
--         ≡ e2 .equiv-proof b .snd (a , fa≡b) ]
--       q a fa≡b = isSet→SquareP (λ _ _ → isSetΣ isSetA λ a → isProp→isSet (isSetB (f a) b)) _ _ _ _
--       r : (λ i → (y : fiber f b) → p i ≡ y) [ e1 .equiv-proof b .snd ≡ e2 .equiv-proof b .snd ]
--       r i (a , fa≡b) = q a fa≡b i


--     isInhabFiber : (b : B) → fiber f b
--     isInhabFiber b = S→a S , {!!}
--       where
--       S : ⟨ ∃[ a ] f a ≡ₚ b ⟩
--       S = surj b
--       S→a : ⟨ ∃[ a ] f a ≡ₚ b ⟩ → A
--       S→a ∣ a , fa≡b ∣₁ = a
--       S→a (squash₁ x y i) = p i
--         where
--         p : S→a x ≡ S→a y
--         p = {!!}


--     -- inflateFiber : (f : A → B) (b : B) → f a ≡ₚ b → f a ≡ b
--     -- inflateFiber f b = {!!}


--     contrFib : (f : A → B) (b : B) → isContr (fiber f b)
--     contrFib f b = {!inhab!} , {!uniq!}
--       where
--       inhab : ⟨ ∃[ a ] f a ≡ₚ b ⟩ → fiber f b
--       inhab ∣ a , fa≡b ∣₁ = a , {!!}
--       inhab (squash₁ x x₁ i) = {!!}
--       uniq : ∀ y → inhab ≡ y
--       uniq y = {!isPropFiber f y!}



--   Bij→Iso : (f : A → B) → hProp ℓ
--   Bij→Iso f = isBijection f ⇒ ∥ isIso f ∥ₚ


  
  
--   bij→iso : ∀ f → ⟨ Bij→Iso f ⟩
--   bij→iso f = ⇒i imp
--     where
--     imp : ⟨ isBijection f ⟩ → ⟨ ∥ isIso f ∥ₚ ⟩
--     imp (surj , inj) = ∣ {!!} , {!!} ∣₁
--       where
--       eq : isEquiv f
--       eq .equiv-proof b = ((let w = surj b in {!!}) , {!!}) , {!!}
--       -- e : A ≃ B
--       -- e = f , eq
--       -- g : B → A
--       -- g b = {!!}

-- isContrSingl' : ∀ {ℓ} {A : Type ℓ} (a : A) → isContr (singl a)
-- isContrSingl' a = (a , refl) , prop
--   where
--   prop : ∀ (b̂ : singl a) → (a , refl) ≡ b̂
--   prop (b , p) i = (p i) , λ j → p (i ∧ j)


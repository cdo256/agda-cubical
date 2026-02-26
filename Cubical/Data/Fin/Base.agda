{-# OPTIONS --safe #-}

module Cubical.Data.Fin.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Recursive using () renaming (_≤_ to _≤′_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; _⊎?_; inl; inr)

open import Cubical.Relation.Nullary

-- Finite types.
--
-- Currently it is most convenient to define these as a subtype of the
-- natural numbers, because indexed inductive definitions don't behave
-- well with cubical Agda. This definition also has some more general
-- attractive properties, of course, such as easy conversion back to
-- ℕ.
Fin : ℕ → Type₀
Fin n = Σ[ k ∈ ℕ ] k < n

private
  v

-- A case analysis helper for induction.
fsplit
  : ∀(fj : Fin (suc k))
  → (fzero ≡ fj) ⊎ (Σ[ fk ∈ Fin k ] fsuc fk ≡ fj)
fsplit (0 , k<sn) = inl (toℕ-injective refl)
fsplit (suc k , k<sn) = inr ((k , pred-≤-pred k<sn) , toℕ-injective refl)

inject< : ∀ {m n} (m<n : m < n) → Fin m → Fin n
inject< m<n (k , k<m) = k , <-trans k<m m<n

injectSuc : {n : ℕ} → Fin n → Fin (suc n)
injectSuc {n = n} = inject< (0 , refl)

flast : Fin (suc k)
flast {k = k} = k , suc-≤-suc ≤-refl

-- Fin 0 is empty
¬Fin0 : ¬ Fin 0
¬Fin0 (k , k<0) = ¬-<-zero k<0

-- The full inductive family eliminator for finite types.
elim
  : ∀(P : ∀{k} → Fin k → Type ℓ)
  → (∀{k} → P {suc k} fzero)
  → (∀{k} {fn : Fin k} → P fn → P (fsuc fn))
  → {k : ℕ} → (fn : Fin k) → P fn
elim P fz fs {zero} = ⊥.rec ∘ ¬Fin0
elim P fz fs {suc k} fj
  = case fsplit fj return (λ _ → P fj) of λ
  { (inl p) → subst P p fz
  ; (inr (fk , p)) → subst P p (fs (elim P fz fs fk))
  }

any? : ∀ {n} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec (Σ (Fin n) P)
any? {n = zero}  {P = _} P? = no (λ (x , _) → ¬Fin0 x)
any? {n = suc n} {P = P} P? =
  mapDec
    (λ
      { (inl P0) → fzero , P0
      ; (inr (x , Px)) → fsuc x , Px
      }
    )
    (λ n h → n (helper h))
    (P? fzero ⊎? any? (P? ∘ fsuc))
  where
    helper : Σ (Fin (suc n)) P → P fzero ⊎ Σ (Fin n) λ z → P (fsuc z)
    helper (x , Px) with fsplit x
    ... | inl x≡0 = inl (subst P (sym x≡0) Px)
    ... | inr (k , x≡sk) = inr (k , subst P (sym x≡sk) Px)

FinPathℕ : {n : ℕ} (x : Fin n) (y : ℕ) → fst x ≡ y → Σ[ p ∈ _ ] (x ≡ (y , p))
FinPathℕ {n = n} x y p =
    ((fst (snd x)) , (cong (λ y → fst (snd x) + y) (cong suc (sym p)) ∙ snd (snd x)))
  , (Σ≡Prop (λ _ → isProp≤) p)

FinVec : (A : Type ℓ) (n : ℕ) → Type ℓ
FinVec A n = Fin n → A

FinFamily : (n : ℕ) (ℓ : Level) → Type (ℓ-suc ℓ)
FinFamily n ℓ = FinVec (Type ℓ) n

FinFamily∙ : (n : ℕ) (ℓ : Level) → Type (ℓ-suc ℓ)
FinFamily∙ n ℓ = FinVec (Pointed ℓ) n

predFinFamily : {n : ℕ} → FinFamily (suc n) ℓ → FinFamily n ℓ
predFinFamily A n = A (finj n)

predFinFamily∙ : {n : ℕ} → FinFamily∙ (suc n) ℓ → FinFamily∙ n ℓ
fst (predFinFamily∙ A x) = predFinFamily (fst ∘ A) x
snd (predFinFamily∙ A x) = snd (A _)

prodFinFamily : (n : ℕ) → FinFamily (suc n) ℓ → Type ℓ
prodFinFamily zero A = A fzero
prodFinFamily (suc n) A = prodFinFamily n (predFinFamily A) × A flast

prodFinFamily∙ : (n : ℕ) → FinFamily∙ (suc n) ℓ → Pointed ℓ
fst (prodFinFamily∙ n A) = prodFinFamily n (fst ∘ A)
snd (prodFinFamily∙ zero A) = snd (A fzero)
snd (prodFinFamily∙ (suc n) A) =
  snd (prodFinFamily∙ n (predFinFamily∙ A)) , snd (A flast)

-- summation
sumFinGen : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A) (f : Fin n → A) → A
sumFinGen {n = zero} _+_ 0A f = 0A
sumFinGen {n = suc n} _+_ 0A f = f flast + sumFinGen _+_ 0A (f ∘ injectSuc)

module Cubical.HITs.NonWellFounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat renaming (iter to iterℕ)
import Cubical.HITs.SetQuotients as Quot
open Quot hiding (rec)
open import Cubical.Data.Prod

private
  variable
    ℓ ℓ' : Level

module 1Cycle where
  data 1Cycle : Type where
    z : 1Cycle
    s : 1Cycle → 1Cycle
    n : s z ≡ z
    squash : isSet 1Cycle

  module _ (P : 1Cycle → Type ℓ)
           (set : ∀ x → isSet (P x))
           (pz : P z)
           (ps : ∀ x → P x → P (s x))
           (pn : PathP (λ i → P (n i)) (ps z pz) pz) where
    rec : ∀ x → P x
    rec z = pz
    rec (s x) = ps x (rec x)
    rec (n i) = pn i
    rec (squash x y p q i j) = r i j
      where
      A : I → I → Type ℓ
      A i j = P (squash x y p q i j)
      r : SquareP A (λ j → rec (p j)) (λ j → rec (q j)) (λ i → rec x) λ i → rec y
      r = isSet→SquareP (λ i j → set _) _ _ _ _

  sx≡x : ∀ x → s x ≡ x
  sx≡x = rec (λ x → s x ≡ x)
             (λ _ → isSet→isGroupoid squash _ _)
             n
             (λ y sy≡y → cong s sy≡y) 
             (isSet→SquareP (λ _ _ → squash) (cong s n) n (cong s n) n)

  _≡z : ∀ x → x ≡ z
  _≡z = rec (_≡ z)
            (λ _ → isSet→isGroupoid squash _ _)
            refl
            (λ x x≡z → sx≡x x ∙ x≡z)
            (isSet→SquareP (λ _ _ → squash) (n ∙ refl) refl n refl)

  isContr1Cycle : isContr 1Cycle
  isContr1Cycle = z , λ x → sym (x ≡z)


module nCycle (n : ℕ) where
  data nCycle : Type where
    z      : nCycle
    s      : nCycle → nCycle
    loop   : iterℕ n s z ≡ z
    squash : isSet nCycle

  -- module _ (A : Type ℓ)
  --          (ps : A → A)
  --          (pz : A)
  --          where
  --   -- R : ∀ {A : Type ℓ} → A → A → Type ℓ
  --   -- R a1 a2 = (iterℕ n ps pz ≡ a1) × (pz ≡ a2)
  --   iter : nCycle → A
  --   iter z = pz
  --   iter (s x) = ps {!iter x!}
  --   iter (loop i) = {!!}
  --   iter (squash x x₁ x₂ y i i₁) = {!!}

  module _ (A : Type ℓ)
           (Aset : isSet A)
           (ps : A → A)
           (pz : A)
           (ploop : iterℕ n ps pz ≡ pz) where

    data R : ℕ → ℕ → Type ℓ where
      Rrefl : ∀ {x} → R x x
      Rsym : ∀ {x y} → R x y → R y x
      Rtrans : ∀ {x y z} → R x y → R y z → R x z
      Rloop : R n 0
      Rsuc : ∀ {x y} → R x y → R (suc x) (suc y)

    inc : ℕ / R → ℕ / R
    inc [ a ] = [ suc a ]
    inc (eq/ x y r i) =
      eq/ (suc x) (suc y) (Rsuc r) i
    inc (squash/ x y p q i j) =
      squash/ (inc x) (inc y) (cong inc p) (cong inc q) i j

    toQuot : nCycle → ℕ / R

    toQuot z = [ 0 ]
    toQuot (s x) = inc (toQuot x)
    toQuot (loop i) = q i
      where
      q : toQuot (iterℕ n s z) ≡ toQuot z
      q = {!!} ∙ eq/ n 0 Rloop ∙ {!!}
    toQuot (squash x x₁ x₂ y i i₁) = {!!}

    toQuotIter : ∀ k → toQuot (iterℕ k s z) ≡ [ k ]
    toQuotIter zero = {!refl!}
    toQuotIter (suc k) = {!!}

    -- iter : nCycle → A
    -- iter-iterℕ : ∀ k → iter (iterℕ k s z) ≡ iterℕ k ps pz

    -- iter z = pz
    -- iter (s x) = ps (iter x)
    -- iter (loop i) = {!!}
    -- iter (squash x x₁ x₂ y i i₁) = {!!}

  --   iter-iterℕ zero = refl
  --   iter-iterℕ (suc k) = cong ps (iter-iterℕ k)

  -- module _ (P : nCycle → Type ℓ)
  --          (pset : ∀ x → isSet (P x))
  --          (pz : P z)
  --          (ps : ∀ x → P x → P (s x))
  --          (ploop : PathP (λ i → P (loop i)) {!!} pz) where
  --   rec : ∀ x → P x
  --   rec z = pz
  --   rec (s x) = ps x (rec x)
  --   rec (loop i) = {!!}
  --   -- rec (squash x y p q i j) = r i j
  --   --   where
  --   --   A : I → I → Type ℓ
  --   --   A i j = P (squash x y p q i j)
  --   --   r : SquareP A (λ j → rec (p j)) (λ j → rec (q j)) (λ i → rec x) λ i → rec y
  --   --   r = isSet→SquareP (λ i j → set _) _ _ _ _
  

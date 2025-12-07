module Cubical.BarInduction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Maybe
open import Cubical.Data.Empty
open import Cubical.Induction.WellFounded 

module _ {ℓ} (A : Type ℓ) where
  FinSeq = List A
  InfSeq = ℕ → A

  prefix : ℕ → InfSeq → FinSeq
  prefix zero α = []
  prefix (suc n) α = α 0 ∷ prefix n λ i → α (suc i)

  prefixFin : ℕ → FinSeq → Maybe FinSeq
  prefixFin zero xs = just []
  prefixFin (suc n) [] = nothing
  prefixFin (suc n) (x ∷ xs) =
    map-Maybe (x ∷_) (prefixFin n xs)

  isBar : (B : FinSeq → Type ℓ) → Type ℓ
  isBar B = ∀ (α : InfSeq) → ∃[ i ∈ ℕ ] B (prefix i α)

  MaybeType→Type : Maybe (Type ℓ) → Type ℓ
  MaybeType→Type nothing = ⊥*
  MaybeType→Type (just X) = X

  FinSeqCrossesBar
    : (B : FinSeq → Type ℓ)
    → (xs : FinSeq) → Type ℓ
  FinSeqCrossesBar B xs = ∃[ i ∈ ℕ ]
    MaybeType→Type (map-Maybe B (prefixFin i xs))

  module BarInduction
         (B : FinSeq → Type ℓ)
         (isBarB : isBar B)
         (P : FinSeq → Type ℓ)
         where

    BaseType : Type ℓ
    BaseType = ∀ xs → FinSeqCrossesBar B xs → P xs

    InductiveType : Type ℓ
    InductiveType =
      ∀ xs → (∀ x → P (xs ++ [ x ])) → P xs

    infix 3 _<_
    infix 3 _≤_

    data _<_ : (xs ys : FinSeq) → Type ℓ where
      <base : ∀ y ys → y ∷ ys < []
      <suc : ∀ xs ys x → xs < ys → x ∷ xs < x ∷ ys

    data Bar {ℓ} {A : Type ℓ} (P : List A → Type ℓ) (xs : List A) : Type ℓ where
      now   : P xs → Bar P xs
      later : (∀ x → Bar P (x ∷ xs)) → Bar P xs

    _≤_ : (xs ys : FinSeq) → Type ℓ
    xs ≤ ys = (xs ≡ ys) ⊎ (xs < ys)

    -- barInduction : BaseType → InductiveType → P []
    -- barInduction base ind = {!!}


    -- <split-inc : ∀ z xs ys → ys ≤ xs → z ∷ ys ≤ z ∷ xs
    -- <split-inc z xs ys (inl p) = inl (cong (z ∷_) p)
    -- <split-inc z xs ys (inr ys<xs) =
    --   inr (<suc ys xs z ys<xs)

    -- <split : ∀ z xs ys → ys < z ∷ xs → ys ≤ xs
    -- <split z [] [] lt = inl refl
    -- <split z [] (y ∷ ys) (<suc _ _ _ ())
    -- <split z (x ∷ xs) [] lt = inr (<base x xs)
    -- <split y (x ∷ xs) (y ∷ ys) (<suc _ _ _ lt) =
    --   r (<split x xs ys lt)
    --   where
    --   x≡z : x ≡ y
    --   x≡z = {!!}
    --   r : ys ≤ xs → (y ∷ ys) ≤ (x ∷ xs)
    --   r (inl ys≡xs) = {!!}
    --   r (inr (<base y ys)) = {!!}
    --   r (inr (<suc xs ys x x₁)) = {!!}
    
    -- <-wellFounded : WellFounded _<_
    -- <-wellFounded [] = acc (λ _ ()) 
    -- <-wellFounded (x ∷ xs) = acc r
    --   where
    --   r : WFRec _<_ (Acc _<_) (x ∷ xs)
    --   r [] _ = acc (λ _ ())
    --   r (y ∷ ys) (<suc ys xs x ys<xs) = {!!}


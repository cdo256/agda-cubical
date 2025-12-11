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

  -- isBar : (B : FinSeq → Type ℓ) → Type ℓ
  -- isBar B = ∀ (α : InfSeq) → ∃[ i ∈ ℕ ] B (prefix i α)

  MaybeType→Type : Maybe (Type ℓ) → Type ℓ
  MaybeType→Type nothing = ⊥*
  MaybeType→Type (just X) = X

  FinSeqCrossesBar
    : (B : FinSeq → Type ℓ)
    → (xs : FinSeq) → Type ℓ
  FinSeqCrossesBar B xs = ∃[ i ∈ ℕ ]
    MaybeType→Type (map-Maybe B (prefixFin i xs))


  data Bar {ℓ} {A : Type ℓ} (P : List A → Type ℓ)
       : (xs : List A) → Type ℓ where
    now   : ∀ xs → P xs → Bar P xs
    later : ∀ xs → (∀ x → Bar P (x ∷ xs)) → Bar P xs

  module BarInduction
         (P : FinSeq → Type ℓ)
         (Q : FinSeq → Type ℓ)
         where

    BaseType : Type ℓ
    BaseType = ∀ xs → P xs → Q xs

    InductiveType : Type ℓ
    InductiveType = ∀ xs → (∀ x → Q (x ∷ xs)) → Q xs

    barInduction 
      : ∀ xs (B : Bar P xs) → BaseType
      → InductiveType → Q xs
    barInduction xs (now xs pxs) base ind = base xs pxs
    barInduction xs (later xs pch) base ind =
      ind xs u
      where
      u : (y : A) → Q (y ∷ xs)
      u y with pch y
      ... | now (x ∷ xs) pxxs = base (x ∷ xs) pxxs
      ... | later (x ∷ xs) Pxxxs =
        barInduction (y ∷ xs) (pch y) base ind

data W {ℓ} (S : Type ℓ) (P : S → Type ℓ) : Type ℓ where
  sup : ∀ (s : S) (f : P s → W S P) → W S P

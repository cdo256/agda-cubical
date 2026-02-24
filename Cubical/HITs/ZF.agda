module Cubical.HITs.ZF where

open import Cubical.Data.Empty renaming (rec to absurd)
open import Cubical.Data.Fin
open import Cubical.Data.Nat renaming (iter to iterℕ) hiding (_+_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Prod hiding (swap)
open import Cubical.Data.Sum
open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (Path; _◁_; _∨_; _∧_; comp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport


data Set : Type

data Tm  (n : ℕ) : Type where
  var : Fin n → Tm n
  val : Set → Tm n

data Expr (n : ℕ) : Type where
  _∨_ : Expr n → Expr n → Expr n
  _∧_ : Expr n → Expr n → Expr n
  _⇒_ : Expr n → Expr n → Expr n
  ⊥ᵉ : Expr n
  _∈ᵉ_ : Tm n → Tm n → Expr n
  ∀∈  : Tm n → Expr (suc n) → Expr n   -- bounded ∀
  ∃∈  : Tm n → Expr (suc n) → Expr n   -- bounded ∃ (optional)

data Set where
  ∅ : Set
  ⋃ : Set → Set
  Nat : Set
  [_,_] : Set → Set → Set
  comp : Set → Expr 1 → Set

⟦_⟧ᵗ : ∀ {n} → Tm n → (Fin n → Set) → Set
⟦ var a ⟧ᵗ ρ = ρ a
⟦ val A ⟧ᵗ ρ = A

predAssign : ∀ {n} → (Fin (suc n) → Set) → (Fin n → Set)
predAssign ρ a = ρ (fsuc a)


⟦_⟧ᵉ : ∀ {n} → Expr n → (Fin n → Set) → Type
⟦ e ∨ e' ⟧ᵉ ρ = ⟦ e ⟧ᵉ ρ ⊎ ⟦ e' ⟧ᵉ ρ
⟦ e ∧ e' ⟧ᵉ ρ = ⟦ e ⟧ᵉ ρ × ⟦ e' ⟧ᵉ ρ
⟦ e ⇒ e' ⟧ᵉ ρ = ⟦ e ⟧ᵉ ρ → ⟦ e' ⟧ᵉ ρ
⟦ ⊥ᵉ ⟧ᵉ ρ = ⊥
⟦ x ∈ᵉ Y ⟧ᵉ ρ = {!!}
⟦ ∀∈ x e ⟧ᵉ ρ = (y : Set) → {!⟦ e ⟧ᵉ (predAssign ρ ∘ fsuc) ≡ ?!} 
⟦ ∃∈ x e ⟧ᵉ ρ = {!!}


  

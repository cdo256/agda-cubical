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


module Try1 where
  data Set : Type

  data Tm  (n : ℕ) : Type where
    var : Fin n → Tm n
    val : Set → Tm n

  sucTm : ∀ {n} → Tm n → Tm (suc n)
  sucTm (var a) = var (fsuc a)
  sucTm (val X) = val X

  Assign : ∀ n m → Type
  Assign n m = Fin n → Tm m


  data Expr (n : ℕ) : Type where
    _∨_ : Expr n → Expr n → Expr n
    _∧_ : Expr n → Expr n → Expr n
    _⇒_ : Expr n → Expr n → Expr n
    ⊥ᵉ : Expr n
    _∈ᵉ_ : Tm n → Tm n → Expr n
    ∀∈  : Tm n → Expr (suc n) → Expr n
    ∃∈  : Tm n → Expr (suc n) → Expr n

  data Set where
    ∅ : Set
    ⋃ : Set → Set
    Nat : Set
    [_,_] : Set → Set → Set
    comp : Set → Expr 1 → Set

  infix 30 _[_]ᵗ
  _[_]ᵗ : ∀ {n m} → Tm n → Assign n m → Tm m
  var a [ ρ ]ᵗ = ρ a
  val A [ ρ ]ᵗ = val A

  ⟦_⟧ᵗ : Tm 0 → Set
  ⟦ var a ⟧ᵗ = absurd (¬Fin0 a)
  ⟦ val A ⟧ᵗ = A

  predAssign : ∀ {n} → (Fin (suc n) → Set) → (Fin n → Set)
  predAssign ρ a = ρ (fsuc a)

  sucAssign : ∀ {n m} → Assign n m → Assign (suc n) (suc m)
  sucAssign ρ a with fsplit a
  ... | inl _ = var fzero
  ... | inr (a , _) = sucTm (ρ a)

  infix 30 _[_]ᵉ 
  _[_]ᵉ : ∀ {n m} → Expr n → Assign n m → Expr m
  (e ∨ e') [ ρ ]ᵉ = e [ ρ ]ᵉ ∨ e' [ ρ ]ᵉ
  (e ∧ e') [ ρ ]ᵉ = e [ ρ ]ᵉ ∧ e' [ ρ ]ᵉ
  (e ⇒ e') [ ρ ]ᵉ = e [ ρ ]ᵉ ⇒ e' [ ρ ]ᵉ
  ⊥ᵉ [ ρ ]ᵉ = ⊥ᵉ
  (t ∈ᵉ u) [ ρ ]ᵉ = t [ ρ ]ᵗ ∈ᵉ u [ ρ ]ᵗ
  ∀∈ x e [ ρ ]ᵉ = ∀∈ (x [ ρ ]ᵗ) (e [ sucAssign ρ ]ᵉ)
  ∃∈ x e [ ρ ]ᵉ = ∃∈ (x [ ρ ]ᵗ) (e [ sucAssign ρ ]ᵉ)

  ⟦_∈_⟧ : Set → Set → Type
  ⟦ x ∈ ∅ ⟧ = ⊥
  ⟦ x ∈ ⋃ A ⟧ = Σ Set λ B → ⟦ x ∈ B ⟧ × ⟦ B ∈ A ⟧
  ⟦ x ∈ Nat ⟧ = {!!}
  ⟦ x ∈ [ y , z ] ⟧ = {!!}
  ⟦ x ∈ comp A x₁ ⟧ = {!!}

  ⟦_⟧ᵉ : Expr 0 → Type 
  ⟦ e ∨ e' ⟧ᵉ = ⟦ e ⟧ᵉ ⊎ ⟦ e' ⟧ᵉ
  ⟦ e ∧ e' ⟧ᵉ = ⟦ e ⟧ᵉ × ⟦ e' ⟧ᵉ
  ⟦ e ⇒ e' ⟧ᵉ = ⟦ e ⟧ᵉ → ⟦ e' ⟧ᵉ
  ⟦ ⊥ᵉ ⟧ᵉ = ⊥
  ⟦ t ∈ᵉ var a ⟧ᵉ = absurd (¬Fin0 a)
  ⟦ t ∈ᵉ val A ⟧ᵉ = {!!}
  ⟦ ∀∈ x e ⟧ᵉ = (y : Set) → {!⟦ e ⟧ᵉ (predAssign ρ ∘ fsuc) ≡ ?!} 
  ⟦ ∃∈ x e ⟧ᵉ = {!!}

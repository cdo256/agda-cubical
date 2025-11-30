module Cubical.HITs.Mobile where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat renaming (iter to iterℕ)
import Cubical.HITs.SetQuotients as Quot
open Quot hiding (rec)
open import Cubical.Data.Prod

private
  variable
    ℓ ℓ' : Level

module _ (B : Type) where
  data BTree : Type where
    leaf : BTree
    node : (f : B → BTree) → BTree

  record Setoid ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      Carrier : Type ℓ
      _≈_ : Carrier → Carrier → Type ℓ'

  open Iso
  data _≈_ : BTree → BTree → Type where
    ≈leaf : leaf ≈ leaf
    ≈node : ∀ {f g} → (c : ∀ b → f b ≈ g b)
          → node f ≈ node g
    ≈perm : ∀ {f} → (π : Iso B B)
          → node f ≈ node (f ∘ π .fun)
    ≈trans : ∀ {s t u} → s ≈ t → t ≈ u → s ≈ u

  ≈refl : ∀ {t} → t ≈ t
  ≈refl {leaf} = ≈leaf
  ≈refl {node f} = ≈node λ b → ≈refl {f b}

  ≈sym : ∀ {s t} → s ≈ t → t ≈ s
  ≈sym ≈leaf = ≈leaf
  ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
  ≈sym (≈perm {f} π) =
    subst
      (λ h → node (f ∘ fun π) ≈ node (f ∘ h))
      (funExt (rightInv π))
      (≈perm {f = f ∘ fun π} (invIso π))
  ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

  MobileSetoid : Setoid ℓ-zero ℓ-zero
  MobileSetoid = record { Carrier = BTree ; _≈_ = _≈_ }

record isPreorder {X : Type ℓ} (_≤_ : X → X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

module _ {I : Type ℓ}
         (_≤_ : I → I → Type ℓ')
         (≤preorder : isPreorder _≤_)
         where
  record Diagram : Type {!!} where
    field
      P : ∀ (i : I) → Diagram
      Pp : ∀ {i j} → (p : i ≤ j) → Diagram
      

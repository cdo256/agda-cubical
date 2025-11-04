{-# OPTIONS --safe #-}

-- Bifunctor, aka a Functor from C × D to E
module Cubical.Categories.Functor.Bifunctor where

open import Cubical.Foundations.Prelude
import Cubical.Foundations.Isomorphism as Iso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function hiding (_∘_; flip)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (_+_)
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor.Base


private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ o‴ ℓ‴ e‴ o⁗ ℓ⁗ e⁗ : Level
    C D E A B : Category o ℓ e

Bifunctor : Category o ℓ e → Category o′ ℓ′ e′ → Category o″ ℓ″ e″ → Type _
Bifunctor C D E = Functor (C ×C D) E

module Bifunctor (H : Bifunctor C D E) where
  open Functor H public

  overlap-× : ∀ (F : Functor A C) (G : Functor A D) → Functor A E
  overlap-× F G = H ∘F (F ,F G)

  reduce-× : ∀ (F : Functor A C) (G : Functor B D) → Bifunctor A B E
  reduce-× F G = H ∘F (F ×F G)

  flip : Bifunctor D C E
  flip = H ∘F Swap

  appˡ : Category.Obj C → Functor D E
  appˡ c = H ∘F constˡ c

  appʳ : Category.Obj D → Functor C E
  appʳ d = H ∘F constʳ d

  ₁ˡ : ∀ {A B d} (f : C [ A , B ]) → E [ F₀ (A , d) , F₀ (B , d) ]
  ₁ˡ f = ₁ (f , Category.id D)

  ₁ʳ : ∀ {A B c} (f : D [ A , B ]) → E [ F₀ (c , A) , F₀ (c , B) ]
  ₁ʳ f = ₁ (Category.id C , f)

  homomorphismˡ : ∀ {X Y Z d} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
                     E [ ₁ˡ {d = d} (C [ g ∘ f ]) ≈ E [ ₁ˡ g ∘ ₁ˡ f ] ]
  homomorphismˡ = trans E
      (F-resp-≈ (refl C , sym D (Category.identity² D)))
      homomorphism
    where open Category.Equiv

  homomorphismʳ : ∀ {X Y Z c} {f : D [ X , Y ]} {g : D [ Y , Z ]} →
                     E [ ₁ʳ {c = c} (D [ g ∘ f ]) ≈ E [ ₁ʳ g ∘ ₁ʳ f ] ]
  homomorphismʳ = trans E
      (F-resp-≈ (sym C (Category.identity² C) , refl D))
      homomorphism
    where open Category.Equiv

  resp-≈ˡ : ∀ {A B d} {f g : C [ A , B ]} → C [ f ≈ g ] →
               E [ ₁ˡ {d = d} f ≈ ₁ˡ g ]
  resp-≈ˡ f≈g = F-resp-≈ (f≈g , Category.Equiv.refl D)

  resp-≈ʳ : ∀ {A B c} {f g : D [ A , B ]} → D [ f ≈ g ] →
               E [ ₁ʳ {c = c} f ≈ ₁ʳ g ]
  resp-≈ʳ f≈g = F-resp-≈ (Category.Equiv.refl C , f≈g)

open Bifunctor public using (appˡ; appʳ) renaming (flip to flip-bifunctor)

overlap-× : ∀ (H : Bifunctor C D E) (F : Functor A C) (G : Functor A D) → Functor A E
overlap-× H = Bifunctor.overlap-× H

reduce-× : ∀ (H : Bifunctor C D E) (F : Functor A C) (G : Functor B D) -> Bifunctor A B E
reduce-× H = Bifunctor.reduce-× H

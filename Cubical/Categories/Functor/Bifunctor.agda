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
open import Cubical.Categories.Functor.Properties


private
  variable
    ℓA ℓA' ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
    A : Category ℓA ℓA'
    B : Category ℓB ℓB'
    C : Category ℓC ℓC'
    D : Category ℓD ℓD'
    E : Category ℓE ℓE'

Bifunctor : Category ℓC ℓC' → Category ℓD ℓD' → Category ℓE ℓE'
          → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) (ℓ-max ℓE ℓE'))
Bifunctor C D E = Functor (C ×C D) E

module Bifunctor (H : Bifunctor C D E) where
  open Category
  open Category D using () renaming (_⋆_ to _⋆ᴰ_)
  open Category C using () renaming (_⋆_ to _⋆ᶜ_)
  open Functor H public

  overlap-× : ∀ (F : Functor A C) (G : Functor A D) → Functor A E
  overlap-× F G = H ∘F (F ,F G)

  reduce-× : ∀ (F : Functor A C) (G : Functor B D) → Bifunctor A B E
  reduce-× F G = H ∘F (F ×F G)

  flip : Bifunctor D C E
  flip = H ∘F Swap D C

  appˡ : C .ob → Functor D E
  appˡ c = H ∘F F
    where
    open Functor
    F : Functor D (C ×C D)
    F .F-ob d = c , d
    F .F-hom f = (C .id) , f
    F .F-id = refl
    F .F-seq f g i = (C .⋆IdL (C .id) (~ i)) , (f ⋆ᴰ g)

  appʳ : D .ob → Functor C E
  appʳ d = H ∘F F
    where
    open Functor
    F : Functor C (C ×C D)
    F .F-ob c = c , d
    F .F-hom f = f , D .id
    F .F-id = refl
    F .F-seq f g i = (f ⋆ᶜ g) , D .⋆IdL (D .id) (~ i)

open Bifunctor public using (appˡ; appʳ) renaming (flip to flip-bifunctor)

overlap-× : ∀ (H : Bifunctor C D E) (F : Functor A C) (G : Functor A D) → Functor A E
overlap-× H = Bifunctor.overlap-× H

reduce-× : ∀ (H : Bifunctor C D E) (F : Functor A C) (G : Functor B D) -> Bifunctor A B E
reduce-× H = Bifunctor.reduce-× H


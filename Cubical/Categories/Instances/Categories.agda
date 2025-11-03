-- Category of categories
{-# OPTIONS --safe #-}

module Cubical.Categories.Instances.Categories where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Foundations.Prelude

module _ {ℓ ℓ' : Level} where
  open Category
  open Functor

  -- Note we restric the type of objects of the contained categories
  -- to be sets to ensure that the hom-sets of functors are actual
  -- hSets.
  CatCategory : Category _ _
  CatCategory .ob = Σ[ C ∈ Category ℓ ℓ' ] isSet (C .ob)
  CatCategory .Hom[_,_] (C , _) (D , _) = Functor C D
  CatCategory .id = Id
  CatCategory ._⋆_ F G = G ∘F F
  CatCategory .⋆IdL F = F-lUnit
  CatCategory .⋆IdR F = F-rUnit
  CatCategory .⋆Assoc F G H = F-assoc
  CatCategory .isSetHom {y = D , isSetD} =
    isSetFunctor isSetD

{-# OPTIONS --safe #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Discrete
open import Cubical.Foundations.GroupoidLaws 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit.Properties 


module Cubical.Categories.Instances.Terminal where

TerminalCategory : {ℓ* : Level} → Category ℓ* ℓ*
TerminalCategory = DiscreteCategory (Unit* , isOfHLevelUnit* 3)

open Category
module _ {ℓ ℓ'} where
  TerminalCategory' : Category ℓ ℓ'
  TerminalCategory' .ob = Unit*
  TerminalCategory' .Hom[_,_] _ _ = Unit*
  TerminalCategory' .id = tt*
  TerminalCategory' ._⋆_ _ _ = tt*
  TerminalCategory' .⋆IdL _ i = tt*
  TerminalCategory' .⋆IdR _ i = tt*
  TerminalCategory' .⋆Assoc _ _ _ i = tt*
  TerminalCategory' .isSetHom = isSetUnit*


module _ {ℓC ℓ'C : Level} {C : Category ℓC ℓ'C} where
  private module C = Category C
  open Functor

  FunctorFromTerminal : {ℓ* : Level} → C.ob → Functor (TerminalCategory {ℓ*}) C
  FunctorFromTerminal c .F-ob _ = c
  FunctorFromTerminal c .F-hom _ = C.id
  FunctorFromTerminal c .F-id = refl
  FunctorFromTerminal c .F-seq _ _ = sym $ C.⋆IdL C.id

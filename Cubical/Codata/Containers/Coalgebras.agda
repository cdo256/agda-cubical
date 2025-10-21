{-# OPTIONS --safe --guardedness #-}

module Cubical.Codata.Containers.Coalgebras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

open import Cubical.Codata.M.MRecord
open import Cubical.Data.Unit
open import Cubical.Data.Containers.Algebras
open import Cubical.Data.Containers.WildCat


private
  variable
    ℓ ℓ' : Level

module Coalgs (Cont : Container ℓ ℓ') where
  open Algs Cont
  open Iso
  open M

  private
    S = IContainer.S Cont
    Q = IContainer.P Cont tt

  MAlg : FixedPoint
  MAlg = iso (M S Q) isom
    where
      isom : Iso (⟦ S ◁ Q ⟧¹ob (M S Q)) (M S Q)
      fun isom = uncurry sup-M
      inv isom m = shape m , pos m
      rightInv isom m = ηEqM m
      leftInv isom (s , f) = refl

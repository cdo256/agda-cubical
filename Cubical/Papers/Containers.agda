{-
Please do not move this file. Changes should only be made if
necessary.

This file contains pointers to the code examples and main results from
the paper:

Formalising inductive and coinductive containers
-}

-- The "--safe" flag ensures that there are no postulates or
-- unfinished goals
{-# OPTIONS --safe --cubical --guardedness #-}

module Cubical.Papers.Containers where
-------------------------------------
-------------- IMPORTS --------------
-------------------------------------
-- 2
open import Cubical.Data.Unit                               as UnitType
open import Cubical.Data.Empty                              as EmptyType
open import Cubical.Data.Nat as Nat hiding (isEven)
open import Cubical.Codata.Stream                           as StreamType
open StreamType.Equality≅Bisimulation renaming (bisim to id)
open import Cubical.Foundations.Prelude                     as Foundations

open import Cubical.Data.W.W                                as W-Type
open import Cubical.Codata.M.MRecord                        as M-Type

open import Cubical.Data.Maybe                              as Maybe

open import Cubical.Data.Containers.WildCat                 as Container

-- 3
open import Cubical.Data.Containers.Algebras                as ContAlg
open import Cubical.Codata.Containers.Coalgebras            as ContCoAlg

-- 4
open import Cubical.Data.Containers.InductiveContainers     as IndCon
open import Cubical.Codata.Containers.CoinductiveContainers as CoIndCon

-------------------------------------
------ SUMMARY OF FORMALISATION -----
-------------------------------------

---- 2.1 Agda and Cubical Agda  ----

-- Unit type:
open UnitType renaming (Unit to ⊤)

-- Empty type:
open EmptyType using (⊥)

-- Natural numbers:
open Nat using (ℕ)

-- Σ-type:
-- omitted (we use a primitive version)

-- Streams
open StreamType using (Stream)

-- isEven
isEven : ℕ → Type
isEven zero = ⊤
isEven (suc zero) = ⊥
isEven (suc (suc n)) = isEven n

-- from
open Stream renaming (head to hd ; tail to tl)
from : ℕ → Stream ℕ
hd (from n) = n
tl (from n) = from (suc n)

-- The interval type
open Foundations using (I ; ~_ ; i0 ; i1)

-- The path type
open Foundations using (_≡_)

-- refl and ⁻¹
open Foundations using (refl ; sym)

-- Dependent path type
open Foundations using (PathP)

-- transport
open Foundations using (transport)

-- funExt
open Foundations using (funExt)

-- Bisimulation and identity type of streams
open StreamType.Equality≅Bisimulation
  using (_≈_) renaming (bisim to id)


---- 2.2 The W-type and the M-type ----

-- The W-type
open W-Type using (W)

-- The M-type
open M-Type using (M)

-- ℕ∞
record N∞ : Type where
  coinductive
  field
    pred∞ : Maybe N∞

-- M-R
open M-Type using (M-R)

-- MCoind
open M-Type using (MCoind)


---- 2.3 Containers ----

-- Definition 3
open Container using (Container)

-- Definition 4
open Container using (IContainer)

-- Definition 6
open ⟦_⟧F using (⟦_⟧)

-- Definition 9
open Container using (Alg⟦_⟧)

-- Definition 10
open Container using (isInitialAlg⟦_⟧)

-- Dual definitions (coalgebras)
open Container using (CoAlg⟦_⟧ ; isTerminalCoAlg⟦_⟧)


------ 3 Setting up ------

---- 3.1 Calculation of the initial algebra and terminal coalgebra  ----

-- Fixed points
open ContAlg.Algs using (FixedPoint)

-- WAlg
open ContAlg.Algs using (WAlg)

-- MAlg
open ContCoAlg.Coalgs using (MAlg)

-- Pos
open ContAlg.Algs using (Pos)

-- PosM
module _ (S : Type) (Q : S → Type) where
  open M
  data PosM : M S Q → Type where
    here : {m : M S Q} → Q (shape m) → PosM m
    below : {m : M S Q} (p : Q (shape m)) → PosM ((pos m) p) → PosM m


---- 3.2 Generalised induction principle for Pos  ----

-- Definition 11
-- Omitted (used implicitly)

-- Lemma 12
open ContAlg.Algs using (PosIndFun)


------ 4 Fixed points ------

-- Theorem 13
open IndCon using (into ; α̅ ; α̅Comm ; α̅Unique)

-- Theorem 14
open CoIndCon using (out; β̅Unique)
open CoIndCon.β1.β2 using (β̅ ; β̅Comm)

-- Lemma 15
open CoIndCon.β1.β2 using (β̅)

-- Lemma 16 (fstEq and sndEq)
open CoIndCon using (fstEq ; sndEq)

-- Lemma 17
open CoIndCon using (preFstEqId)

-- Lemma 18
-- Omitted (never used explicitly)

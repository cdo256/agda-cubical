{-# OPTIONS --guardedness #-}
module Cubical.HITs.IndexTree where

open import Cubical.Foundations.Prelude hiding (Path; _◁_)
open import Cubical.Data.Containers.Base
open import Cubical.Data.Containers.Algebras
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat renaming (iter to iterℕ) hiding (_+_)
import Cubical.HITs.SetQuotients as Quot
open Quot hiding (rec)
open import Cubical.Data.Prod hiding (swap)
open import Cubical.Data.Sum
open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Base 
open import Cubical.Categories.Instances.Sets.Base 
open import Cubical.WildCat.Instances.Types
open import Cubical.Data.Containers.WildCat
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor hiding (_$_)


_∪ʳ_ : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
(l1 , u1) ∪ʳ (l2 , u2) = min l1 l2 , max u1 u2 

module RangeUnionTree where
  data IT : ℕ × ℕ → Type where
    l : ∀ n → IT (n , suc n)
    n : ∀ r1 r2 → (s : IT r1) (t : IT r2)
      → IT (r1 ∪ʳ r2)

-- module RangeShiftTree where
--   record ShiftRange : Type where
--     constructor sr
--     field
--       lower : ℕ
--       upper : ℕ
--       shift : ℕ

--   calculateShift : ?
--   data IT : ShiftRange → Type where
--     l : ∀ n → IT 0 (n , suc n)
--     n : ∀ r1 r2 → (s : IT r1) (t : IT r2)
--       → IT (r1 ∪ʳ r2)

module 1Tangle where
  open import Cubical.Data.List hiding ([_])
  -- open import Cubical.Codata.Conat as Coℕ
  open import Cubical.HITs.SetQuotients
  Strand = (ℕ → Unit) → Type
  PStrand = List Unit

  record Tangle : Type (ℓ-suc ℓ-zero) where
    field
      Idx : Type
      fold : Idx → PStrand × PStrand

  data TangleRel (t : Tangle) : Strand → Strand → Type where
    

  ⟦_⟧ : Tangle → Type
  ⟦ T ⟧ = PStrand / λ s t → Σ Idx λ i → (s ≡ proj₁ (fold i)) × (t ≡ proj₂ (fold i))
    where open Tangle T

  module CoNat where
    open Tangle
    open _/_
    tangle : Tangle
    tangle .Idx = ⊥
    tangle .fold ()

    unwrap : ⟦ tangle ⟧ → PStrand
    unwrap [ xs ] = xs 
    unwrap (squash/ xs ys p q i j) = r j i
      where
      r : Square (λ i → unwrap xs) (λ i → unwrap ys) (λ j → unwrap (p j)) (λ j → unwrap (q j))
      r = isSet→SquareP (λ _ _ → isOfHLevelList ℕ.zero isSetUnit) _ _ _ _

    unwrap≡ : ⟦ tangle ⟧ ≡ PStrand
    unwrap≡ = isoToPath (iso unwrap [_] sect retr)
      where
      sect : section unwrap [_]
      sect S = refl
      retr : retract unwrap [_]
      retr [ xs ] = refl
      retr (squash/ S T p q i j) = r j i
        where
        r : SquareP (λ j i → [ unwrap (squash/ S T p q i j) ] ≡ squash/ S T p q i j) (λ j → retr S) (λ j → retr T) (λ i → retr (p i)) λ i → retr (q i)
        r = isSet→SquareP (λ i j → isProp→isSet (squash/ _ _)) (λ j → retr S) (λ j → retr T) (λ i → retr (p i)) λ i → retr (q i)

    PStrand≡ℕ : PStrand ≡ ℕ
    PStrand≡ℕ = isoToPath (iso f g sect retr)
      where
      f : PStrand → ℕ
      f [] = 0
      f (tt ∷ xs) = suc (f xs)
      g : ℕ → PStrand
      g zero = []
      g (suc n) = tt ∷ g n
      sect : section f g
      sect zero = refl
      sect (suc n) = cong suc (sect n)
      retr : retract f g
      retr [] = refl
      retr (tt ∷ xs) = cong (tt ∷_) (retr xs)

    untangled1TangleIsNat : ⟦ tangle ⟧ ≡ ℕ
    untangled1TangleIsNat = unwrap≡ ∙ PStrand≡ℕ

  module Point where
    open Tangle
    open _/_
    T : Tangle
    T .Idx = Unit
    T .fold tt = [] , (tt ∷ [])

    

    isContrTangle : isContr ⟦ T ⟧
    isContrTangle = [ [] ] , prop
      where
      prop : (y : ⟦ T ⟧) → [ [] ] ≡ y
      prop [ a ] = eq/ [] a (tt , ({!!} , {!!}))
      prop (eq/ a b r i) = {!!}
      prop (squash/ y y₁ p q i i₁) = {!!}
  

module Tangle {ℓ} (B : Type ℓ) (_≟ᴮ_ : Discrete B) where
  Strands = (ℕ → B) → hProp ℓ

  record Tangle : Type (ℓ-suc ℓ) where
    field
      strands : Strands
      fold : B
  
  

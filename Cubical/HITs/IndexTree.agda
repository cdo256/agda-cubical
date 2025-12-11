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
-- open import Cubical.Data.Prod hiding (swap)
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Fin hiding (_/_)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Empty as ⊥ renaming (elim to absurd) 
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

  isSetPStrand : isSet PStrand
  isSetPStrand = isOfHLevelList ℕ.zero isSetUnit

  record Tangle : Type (ℓ-suc ℓ-zero) where
    field
      Idx : Type
      fold : Idx → PStrand × PStrand

  module _ {T : Tangle} where
    infix 3 _~_
    data _~_ : PStrand → PStrand → Type ℓ-zero where
      ~fold : ∀ i xs ys → T .Tangle.fold i ≡ (xs , ys) → xs ~ ys
      ~refl : ∀ xs → xs ~ xs
      ~sym : ∀ xs ys → xs ~ ys → ys ~ xs
      ~trans : ∀ xs ys zs → xs ~ ys → ys ~ zs → xs ~ zs
      ~cong : ∀ xs ys x → xs ~ ys → x ∷ xs ~ x ∷ ys

  ⟦_⟧ : Tangle → Type
  ⟦ T ⟧ = PStrand / (_~_ {T = T})

  foldInj : ∀ T i → Path ⟦ T ⟧ [ T .Tangle.fold i .fst ] [ T .Tangle.fold i .snd ]
  foldInj T i =
    let (xs , ys) = T .Tangle.fold i
    in eq/ xs ys (~fold i xs ys refl)

  module OpenChain where
    open Tangle
    open _/_
    tangle : Tangle
    tangle .Idx = ⊥
    tangle .fold ()

    unwrap : ⟦ tangle ⟧ → PStrand
    unwrap = Quot.rec isSetPStrand (λ xs → xs) resp
      where
      resp : ∀ a b → a ~ b → a ≡ b
      resp _ _ (~refl xs) = refl
      resp _ _ (~sym xs ys xs~ys) = sym (resp _ _ xs~ys)
      resp _ _ (~trans xs ys zs xs~ys ys~zs) = resp _ _ xs~ys ∙ resp _ _ ys~zs
      resp _ _ (~cong xs ys x xs~ys) = cong (x ∷_) (resp _ _ xs~ys)
      resp _ _ (~fold () xs ys p)

    unwrap≡ : ⟦ tangle ⟧ ≡ PStrand
    unwrap≡ = isoToPath (iso unwrap [_] sect retr)
      where
      sect : section unwrap [_]
      sect xs = refl
      retr : retract unwrap [_]
      retr = elimProp (λ _ → squash/ _ _) (λ _ → refl)

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
    T .fold tt = [] , tt ∷ []

    isContrT : isContr ⟦ T ⟧
    isContrT = [ [] ] , elimProp (λ x → squash/ _ _) λ xs → eq/ [] xs ([]~xs xs)
      where
      _~'_ = _~_ {T = T}
      []~xs : ∀ xs → [] ~' xs
      []~xs [] = ~refl []
      []~xs (tt ∷ xs) = ~trans [] (tt ∷ []) (tt ∷ xs) (~fold tt [] (tt ∷ []) refl) (~cong [] xs tt ([]~xs xs))

  open import Cubical.Data.Nat.Order

  module Modulo' (k : ℕ) (k>0 : k > 0) where
    open import Cubical.Data.Nat as ℕ
    ℕ→PStrand : ℕ → PStrand
    ℕ→PStrand zero = []
    ℕ→PStrand (suc n) = tt ∷ ℕ→PStrand n

    PStrand→ℕ : PStrand → ℕ
    PStrand→ℕ [] = zero
    PStrand→ℕ (tt ∷ xs) = suc (PStrand→ℕ xs)

    open Tangle
    open _/_
    T : Tangle
    T .Idx = Unit
    T .fold tt = [] , ℕ→PStrand k 

    infix 3 _~'_
    _~'_ = _~_ {T = T}

    [_]ₙ : ℕ → ⟦ T ⟧
    [ n ]ₙ = [ ℕ→PStrand n ]

    ≡→~' : ∀ {xs ys} → xs ≡ ys → xs ~' ys
    ≡→~' {xs} {ys} p = subst (xs ~'_) p (~refl xs)

    ~assoc : ∀ xs ys zs → ((xs ++ ys) ++ zs) ~' (xs ++ ys ++ zs)
    ~assoc xs ys zs = ≡→~' (++-assoc xs ys zs)

    ~cong++ : ∀ xs ys xs' ys' → xs ~' xs' → ys ~' ys' → (xs ++ ys) ~' (xs' ++ ys')
    ~cong++ xs ys xs' ys' (~fold tt xs₁ ys₁ x) ys~ys' = {!!}
    ~cong++ xs ys xs' ys' (~refl xs₁) ys~ys' = {!!}
    ~cong++ xs ys xs' ys' (~sym xs₁ ys₁ xs~xs') ys~ys' = {!!}
    ~cong++ xs ys xs' ys' (~trans xs₁ ys₁ zs xs~xs' xs~xs'') ys~ys' = {!!}
    ~cong++ xs ys xs' ys' (~cong xs₁ ys₁ x xs~xs') ys~ys' = {!!}

    ~comm : ∀ xs ys → (xs ++ ys) ~' (ys ++ xs)
    ~comm [] [] = ~refl []
    ~comm [] (tt ∷ ys) = ~cong _ _ tt (~comm [] ys)
    ~comm (tt ∷ xs) [] = ~cong _ _ tt (~comm xs [])
    ~comm (tt ∷ xs) (tt ∷ ys) = ~cong (xs ++ (tt ∷ [] ++ ys)) (ys ++ (tt ∷ [] ++ xs)) tt p
      where
      p1 : xs ++ (tt ∷ [] ++ ys) ~' (xs ++ tt ∷ []) ++ ys
      p1 = ~sym _ _ (~assoc xs (tt ∷ []) ys)
      p2 : (xs ++ tt ∷ []) ++ ys ~' ys ++ (xs ++ tt ∷ [])
      p2 = ~comm _ ys
      p3 : ys ++ (xs ++ tt ∷ []) ~' ys ++ (tt ∷ [] ++ xs)
      p3 = {!!}
      p : xs ++ tt ∷ [] ++ ys ~' ys ++ tt ∷ [] ++ xs
      p = ~trans _ _ _ p1 (~trans _ _ _ p2 p3)

    _+'_ : ⟦ T ⟧ → ⟦ T ⟧ → ⟦ T ⟧
    _+'_ = Quot.rec2 squash/ (λ xs ys → [ xs ++ ys ]) {!!} {!!}
      where
      resp2 : (xs ys zs : PStrand) → ys ~' zs → (xs ++ ys) ~' (xs ++ zs)
      resp2 [] ys zs r = r
      resp2 (tt ∷ xs) ys zs r = ~cong _ _ tt (resp2 xs ys zs r)
      resp1 : (xs ys zs : PStrand) → xs ~' ys → (xs ++ zs) ~' (ys ++ zs)
      resp1 xs ys zs r = {!!}
    

-- module Tangle {ℓ} (B : Type ℓ) (_≟ᴮ_ : Discrete B) where
--   Strands = (ℕ → B) → hProp ℓ

--   record Tangle : Type (ℓ-suc ℓ) where
--     field
--       strands : Strands
--       fold : B
  
  

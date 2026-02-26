module Cubical.HITs.Graph where

import Cubical.HITs.SetQuotients as Quot
open Quot hiding (rec)
open import Cubical.Categories.Instances.Sets.Base 
open import Cubical.Data.Containers.Algebras
open import Cubical.Data.Containers.Base
open import Cubical.Data.Containers.WildCat
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Data.Fin
open import Cubical.Data.Nat renaming (iter to iterℕ) hiding (_+_)
open import Cubical.Data.Prod hiding (swap)
open import Cubical.Data.Sum
open import Cubical.Data.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (Path; _◁_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Functions.Logic hiding (⊥)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.WildCat.Base
open import Cubical.WildCat.Functor
open import Cubical.WildCat.Instances.Types


data Graph : Type
data Node : Graph → Type
data NodeEdges : Graph →  Type

data Graph where
  ∅ : Graph
  ext : ∀ G → NodeEdges G → Graph

data Node where
  z : ∀ G f → Node (ext G f)
  s : ∀ G f → Node G → Node (ext G f)

data NodeEdges where
  ∅ᵉ : NodeEdges ∅
  0∷_ : ∀ {G f} → NodeEdges G → NodeEdges (ext G f)
  1∷_ : ∀ {G f} → NodeEdges G → NodeEdges (ext G f)
  
G1 : Graph
G1 = ext ∅ ∅ᵉ 

G2 : Graph
G2 = ext G1 (1∷ ∅ᵉ)

G3 : Graph
G3 = ext G2 (0∷ 1∷ ∅ᵉ)

G4 : Graph
G4 = ext G3 (1∷ 0∷ 0∷ ∅ᵉ)

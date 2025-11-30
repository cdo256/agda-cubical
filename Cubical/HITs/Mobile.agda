module Cubical.HITs.Mobile where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat renaming (iter to iterℕ)
import Cubical.HITs.SetQuotients as Quot
open Quot hiding (rec)
open import Cubical.Data.Prod
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open BinaryRelation
open isEquivRel

private
  variable
    ℓ ℓ' : Level

module _ where
  record isSetoid ℓ' (X : Type ℓ) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      _≈_ : X → X → Type ℓ'
      equiv : isEquivRel _≈_
  Setoid : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  Setoid ℓ ℓ' = TypeWithStr ℓ (isSetoid ℓ')

  record ≈Hom[_,_] (S : Setoid ℓ ℓ') (T : Setoid ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    constructor ≈hom
    open isSetoid (str S) hiding (equiv) renaming (_≈_ to _≈ˢ_)
    open isSetoid (str T) hiding (equiv) renaming (_≈_ to _≈ᵀ_)
    field
      fun : ⟨ S ⟩ → ⟨ T ⟩
      resp : ∀ {x y} → x ≈ˢ y → fun x ≈ᵀ fun y

  ≈Id : ∀ (S : Setoid ℓ ℓ') → ≈Hom[ S , S ]
  ≈Id S = record
    { fun = λ z → z
    ; resp = λ {x} {y} z → z
    }

  _≈∘_ : ∀ {S T U : Setoid ℓ ℓ'}
       → (G : ≈Hom[ T , U ]) 
       → (F : ≈Hom[ S , T ]) 
       → ≈Hom[ S , U ]
  _≈∘_ (≈hom g g~) (≈hom f f~) = ≈hom (g ∘ f) (g~ ∘ f~)

  ≈Hom-eq : {S T : Setoid ℓ ℓ'} (f g : ≈Hom[ S , T ]) → Type (ℓ-max ℓ ℓ')
  ≈Hom-eq {S = S} {T = T} (≈hom f _) (≈hom g _) = ∀ x → f x ≈ᵀ g x
    where
    open isSetoid (str S) hiding (equiv) renaming (_≈_ to _≈ˢ_)
    open isSetoid (str T) hiding (equiv) renaming (_≈_ to _≈ᵀ_)

record isPreorder {X : Type ℓ} (_≤_ : X → X → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    ≤refl : ∀ {x} → x ≤ x
    ≤trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z

module _ {I : Type ℓ}
         (_≤_ : I → I → Type ℓ')
         (≤preorder : isPreorder _≤_)
         where
  
  -- Essientially a functor
  record Diagram : Type (ℓ-suc (ℓ-max ℓ' ℓ)) where
    open isPreorder ≤preorder
    field
      D-ob : ∀ (i : I)
           → Setoid ℓ ℓ'
      D-mor : ∀ {i j} → (p : i ≤ j)
            → ≈Hom[ D-ob i , D-ob j ]
      D-id : ∀ {i} → D-mor (≤refl {i}) ≡ ≈Id (D-ob i)
      D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
             → D-mor (≤trans p q) ≡ D-mor q ≈∘ D-mor p

  module Colim (P : Diagram) where
    open Diagram P
    open ≈Hom[_,_]

    Colim₀ : Type ℓ
    Colim₀ = Σ[ i ∈ I ] ⟨ D-ob i ⟩
    data _≈ˡ_ : Colim₀ → Colim₀ → Type (ℓ' ) where
      ≈lstage : ∀ i → (x x' : ⟨ D-ob i ⟩) → (i , x) ≈ˡ (i , x')
      ≈lstep : ∀ {i j} (p : i ≤ j) (x : ⟨ D-ob i ⟩)
             → (i , x) ≈ˡ (j , D-mor p .fun x)
      ≈lsym : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
      ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u 

    equiv : isEquivRel _≈ˡ_
    equiv .reflexive = λ (i , x) → ≈lstage i x x
    equiv .symmetric = λ _ _ P → ≈lsym P
    equiv .transitive = λ _ _ _ P Q → ≈ltrans P Q

    Colim : Setoid ℓ ℓ'
    Colim = Colim₀ , record { _≈_ = _≈ˡ_ ; equiv = equiv }

    -- All cocones for this diagram live in the same (ℓ, ℓ') universe
    record Cocone : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      field
        Apex : Setoid ℓ ℓ'
        inj  : ∀ i → ≈Hom[ D-ob i , Apex ]
    open Cocone

    -- The canonical cocone into the colimit
    LimitCocone : Cocone
    LimitCocone .Apex = {!Colim!}
    LimitCocone .inj i .fun x = i , x
    LimitCocone .inj i .resp {x} {y} x≈y = {!!}
      where
      open isSetoid (str Colim)

    -- Morphisms of cocones
    record ColimMorphism (C C' : Cocone) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      field
        apexHom  : ≈Hom[ C .Apex , C' .Apex ]
        commutes : ∀ i x →
          ≈Hom-eq
            (apexHom ≈∘ C .inj i)
            (C' .inj i)

    -- Universal property (you can fill this later)
    record isLimitingCone (C : Cocone) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      field
        -- map : ∀ C' → Σ[ h ∈ ColimMorphism C' C ]

data BTree (B : Type ℓ) : Type ℓ where
  leaf : BTree B
  node : (f : B → BTree B) → BTree B
    
module ωOrdinal where
  Ord : Type
  Ord = BTree ℕ
  data _<_ : Ord → Ord → Type where
    <child : ∀ f i → f i < node f
    <trans : ∀ {s t u} → s < t → t < u → s < u

  _≤_ : Ord → Ord → Type
  s ≤ t = ∀ u → (p : u < s) → u < t

  data _≈_ : Ord → Ord → Type where
    ≈ext : ∀ {s t} → (le : s ≤ t) (ge : t ≤ s)
         → s ≈ t

  ≈refl : ∀ {t} → t ≈ t
  ≈refl {t} = ≈ext (λ _ p → p) (λ _ p → p)

  ≈sym : ∀ {s t} → s ≈ t → t ≈ s
  ≈sym (≈ext le ge) = ≈ext ge le

  ≈trans : ∀ {s t u} → s ≈ t → t ≈ u → s ≈ u
  ≈trans (≈ext s≤t s≥t) (≈ext t≤u u≥t) =
    ≈ext (λ _ p → t≤u _ (s≤t _ p)) λ _ p → s≥t _ (u≥t _ p)

  OrdinalSetoid : Setoid ℓ-zero ℓ-zero
  OrdinalSetoid = Ord , record
    { _≈_ = _≈_
    ; equiv = equivRel
      (λ t → ≈refl {t})
      (λ _ _ p → ≈sym p)
      (λ _ _ _ p q → ≈trans p q) }

  pattern 𝟘 = leaf
  pattern lim f = node f

  osuc : Ord → Ord
  osuc α = lim (λ _ → α)

  𝟙 : Ord
  𝟙 = osuc 𝟘
  
  ℕ→Ord : ℕ → Ord
  ℕ→Ord zero = 𝟘
  ℕ→Ord (suc ω) = osuc (ℕ→Ord ω)
  ω : Ord
  ω = lim ℕ→Ord
  𝟘<ω : 𝟘 < ω
  𝟘<ω = <child ℕ→Ord zero

  data isChild : (α β : Ord) → Type ℓ-zero where
    ischild : ∀ f i → isChild (node f) (f i) 
  
  -- not decidable.
  isChild? : (α β : Ord) → Dec (isChild α β)
  isChild? 𝟘 β = no (λ ())
  isChild? (lim f) β = {!!}

  -- 𝟘<lim : ∀ f → 𝟘 < lim f
  -- 𝟘<lim f with isChild? (lim f) 𝟘 
  -- ... | yes p = {!!}
  -- ... | no ¬p = <trans {!!} {!!}

  -- Not definable in general since we need arbitrary branching.
  lim' : (f : Ord → Ord) → Ord 
  lim' f = lim λ i → {!!}

  infixl 30  _+ᵒ_ 
  _+ᵒ_ : Ord → Ord → Ord
  α +ᵒ 𝟘 = α
  α +ᵒ lim f = lim λ i → α +ᵒ f i

  _ : (ℕ→Ord 1) +ᵒ (ℕ→Ord 1) ≈ (ℕ→Ord 2)
  _ = ≈ext le ge
    where
    le : (ℕ→Ord 1 +ᵒ ℕ→Ord 1) ≤ ℕ→Ord 2
    le 𝟘 p = {!!}
    le (lim f) p = {!!}
    ge : ℕ→Ord 2 ≤ (ℕ→Ord 1 +ᵒ ℕ→Ord 1)
    ge = {!!}

  1+ω≈ω : 𝟙 +ᵒ ω ≈ ω
  1+ω≈ω = {!!}

  -- Does this bring in an extra successor?
  _∙ᵒ_ : Ord → Ord → Ord
  α ∙ᵒ 𝟘 = 𝟘
  α ∙ᵒ lim f = lim (λ i → α ∙ᵒ f i)
  

module Mobile (B : Type) where
  open Iso
  data _≈_ : BTree B → BTree B → Type where
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
  MobileSetoid = BTree B , record
    { _≈_ = _≈_
    ; equiv = equivRel
      (λ t → ≈refl {t})
      (λ _ _ p → ≈sym p)
      (λ _ _ _ p q → ≈trans p q) }
      

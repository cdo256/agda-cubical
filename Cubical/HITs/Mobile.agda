module Cubical.HITs.Mobile where

open import Cubical.Foundations.Prelude hiding (Path)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat renaming (iter to iterℕ) hiding (_+_)
import Cubical.HITs.SetQuotients as Quot
open Quot hiding (rec)
open import Cubical.Data.Prod hiding (swap)
open import Cubical.Data.Sum
open import Cubical.Data.Empty renaming (elim to absurd)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Base 

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
    open isEquivRel equiv public

  Setoid : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
  Setoid ℓ ℓ' = TypeWithStr ℓ (isSetoid ℓ')

  mkSetoid : (X : Type ℓ) (_≈_ : X → X → Type ℓ')
           → (≈refl : ∀ {x} → x ≈ x)
           → (≈sym : ∀ {x y} → x ≈ y → y ≈ x)
           → (≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z)
           → Setoid ℓ ℓ'
  mkSetoid X _≈_ ≈refl ≈sym ≈trans = X , record
    { _≈_ = _≈_
    ; equiv = equivRel (λ _ → ≈refl) (λ _ _ → ≈sym) (λ _ _ _ → ≈trans)
    }

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


  module _ {S T : Setoid ℓ ℓ'} where
    module S = isSetoid (str S)
    module T = isSetoid (str T)
    open ≈Hom[_,_]
    open isEquivRel

    _≈⃗_ : (F G : ≈Hom[ S , T ]) → Type (ℓ-max ℓ ℓ')
    _≈⃗_ (≈hom f _) (≈hom g _) = ∀ x → f x T.≈ g x

    ≈⃗refl : {F : ≈Hom[ S , T ]} → F ≈⃗ F
    ≈⃗refl {≈hom f _} = λ x → T.reflexive (f x)

    ≈⃗sym : {F G : ≈Hom[ S , T ]} → F ≈⃗ G → G ≈⃗ F
    ≈⃗sym F≈G = λ x → T.symmetric _ _ (F≈G x)

    ≈⃗trans : {F G H : ≈Hom[ S , T ]} → F ≈⃗ G → G ≈⃗ H → F ≈⃗ H
    ≈⃗trans F≈G G≈H = λ x → T.transitive _ _ _ (F≈G x) (G≈H x)

  HomSetoid : (S T : Setoid ℓ ℓ') → Setoid (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  HomSetoid S T = mkSetoid ≈Hom[ S , T ] _≈⃗_ ≈⃗refl ≈⃗sym ≈⃗trans

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
           → Setoid ℓ (ℓ-max ℓ ℓ')
      D-mor : ∀ {i j} → (p : i ≤ j)
            → ≈Hom[ D-ob i , D-ob j ]
      D-id : ∀ {i} → (D-mor (≤refl {i})) ≈⃗ (≈Id (D-ob i))
      D-comp : ∀ {i j k} → (p : i ≤ j) (q : j ≤ k)
             → (D-mor (≤trans p q)) ≈⃗ (D-mor q ≈∘ D-mor p)

  module Colim (P : Diagram) where
    open Diagram P renaming (D-ob to P̂)
    open isSetoid hiding (equiv)

    Pf : ∀ {i j} (p : i ≤ j) → (⟨ P̂ i ⟩ → ⟨ P̂ j ⟩)
    Pf p = D-mor p .≈Hom[_,_].fun

    ≈j : ∀ i → (x y : ⟨ P̂ i ⟩) → Type _
    ≈j i x y = x ≈' y
      where open isSetoid (str (P̂ i)) renaming (_≈_ to _≈'_)
    syntax ≈j i x y = x ≈[ i ] y

    equiv' : ∀ i → isEquivRel (≈j i)
    equiv' i = equiv
      where open isSetoid (str (P̂ i))

    open ≈Hom[_,_]

    Colim₀ : Type ℓ
    Colim₀ = Σ[ i ∈ I ] ⟨ P̂ i ⟩
    data _≈ˡ_ : Colim₀ → Colim₀ → Type (ℓ-max ℓ ℓ') where
      ≈lstage : ∀ i → {x x' : ⟨ P̂ i ⟩} → x ≈[ i ] x' → (i , x) ≈ˡ (i , x')
      ≈lstep : ∀ {i j} (p : i ≤ j) (x : ⟨ P̂ i ⟩)
             → (i , x) ≈ˡ (j , Pf p x)
      ≈lsym : ∀ {s t} → s ≈ˡ t → t ≈ˡ s
      ≈ltrans : ∀ {s t u} → s ≈ˡ t → t ≈ˡ u → s ≈ˡ u 

    equiv : isEquivRel _≈ˡ_
    equiv .reflexive (i , x) = ≈lstage i (reflexive' x)
      where open isEquivRel (equiv' i)
                 renaming (reflexive to reflexive')
    equiv .symmetric = λ _ _ P → ≈lsym P
    equiv .transitive = λ _ _ _ P Q → ≈ltrans P Q

    Colim : Setoid ℓ (ℓ-max ℓ ℓ')
    Colim = Colim₀ , record { _≈_ = _≈ˡ_ ; equiv = equiv }

    -- All cocones for this diagram live in the same (ℓ, ℓ') universe
    record Cocone : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      field
        Apex : Setoid ℓ (ℓ-max ℓ ℓ')
        inj  : ∀ i → ≈Hom[ P̂ i , Apex ]
        commutes : ∀ {i j} (p : i ≤ j) → inj i ≈⃗ (inj j ≈∘ D-mor p) 
    open Cocone

    -- The canonical cocone into the colimit
    LimitCocone : Cocone
    LimitCocone .Apex = Colim
    LimitCocone .inj i .fun x = i , x
    LimitCocone .inj i .resp x≈y = ≈lstage i x≈y
    LimitCocone .commutes {i} {j} p x = ≈lstep p x

    -- Morphisms of cocones
    record ColimMorphism (C C' : Cocone) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      field
        apexHom  : ≈Hom[ C .Apex , C' .Apex ]
        commutes : ∀ i → (apexHom ≈∘ C .inj i)
                       ≈⃗ (C' .inj i)

    open ColimMorphism

    record isLimitingCocone (C : Cocone) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
      field
        mor : ∀ C' → ColimMorphism C C'
        unique : ∀ C' → (F : ColimMorphism C C')
               → (F .apexHom) ≈⃗ (mor C' .apexHom)        
               
    open isLimitingCocone 

    
    module IsLimitingCocone (C' : Cocone) where
      open Cocone C'
      module C' = isSetoid (str (C' .Apex))

      private
        f : ⟨ Colim ⟩ → ⟨ C' .Apex ⟩
        f (i , x) = C' .inj i .fun x

      isRespecting : ∀ {i j x y} → (i , x) ≈ˡ (j , y)
           →    C' .inj i .fun x 
           C'.≈ C' .inj j .fun y 
      isRespecting (≈lstage i x≈y) = C' .inj i .resp x≈y
      isRespecting (≈lstep p x) = C' .commutes p x
      isRespecting (≈lsym r) = C'.symmetric _ _ (isRespecting r)
      isRespecting (≈ltrans r s) = C'.transitive _ _ _ (isRespecting r) (isRespecting s)

      F : ColimMorphism LimitCocone C'
      F .apexHom .fun = f
      F .apexHom .resp = isRespecting
      F .commutes i x = C'.reflexive (f (i , x))

      unq : (G : ColimMorphism LimitCocone C')
          → ∀ x → G .apexHom .fun x C'.≈ f x       
      unq G (i , x) = G .commutes i x

    isLimitingCoconeLimitCocone : isLimitingCocone LimitCocone
    isLimitingCoconeLimitCocone = record
      { mor = F
      ; unique = unq
      }
      where open IsLimitingCocone

data BTree (B : Type ℓ) : Type ℓ where
  leaf : BTree B
  node : (f : B → BTree B) → BTree B
    
module BOrdinal (B : Type) where
  data Ord : Type where
    zero : Ord
    suc : Ord → Ord
    lim : (B → Ord) → Ord

  data _<_ : Ord → Ord → Type where
    <suc : ∀ α → α < suc α
    <lim : ∀ α f i → α < f i → α < lim f
    <trans : ∀ {s t u} → s < t → t < u → s < u

  _≤_ : Ord → Ord → Type
  s ≤ t = ∀ u → (p : u < s) → u < t

  data _≈_ : Ord → Ord → Type where
    ≈ext : ∀ {s t} → (le : s ≤ t) (ge : t ≤ s)
         → s ≈ t

  ⊂_ : Ord → Type
  ⊂ α = Σ[ β ∈ Ord ] β < α

  infixl 30  _+_ 
  _+_ : Ord → Ord → Ord
  α + zero = α
  α + suc β = suc (α + β)
  α + lim f = lim (λ i → α + f i)

module ωOrdinal where
  open BOrdinal ℕ public
  ℕ→Ord : ℕ → Ord 
  ℕ→Ord zero = zero
  ℕ→Ord (suc ω) = suc (ℕ→Ord ω)
  ω : Ord
  ω = lim ℕ→Ord
  0<ω : zero < ω
  0<ω = <lim zero ℕ→Ord 1 (<suc zero)
    

module BoundedOrdinal (Γ : ωOrdinal.Ord) where
  module Γ = ωOrdinal
  open Γ using (⊂_; _+_)
  data Ord : Type where
    zero : Ord
    suc : Ord → Ord
    lim : (ℕ → Ord) → Ord

  data lt : (φ : ⊂ Γ) → Ord → Ord → Type where
    <suc : ∀ φ β → lt φ β (suc β)
    <lim : ∀ φ β {φ<Γ} f i → (p : Γ.suc φ Γ.< Γ) → lt (φ , φ<Γ) β (f i)
         → lt (Γ.suc φ , p) β (lim f)
    <trans : ∀ φ φ' {φ<Γ φ'<Γ} {s t u}
           → (p : φ + φ' Γ.< Γ)
           → lt (φ , φ<Γ) s t
           → lt (φ' , φ'<Γ) t u
           → lt (φ + φ' , p) s u

  _<_ : Ord → Ord → Type
  β < γ = Σ[ φ ∈ ⊂ Γ ] lt φ β γ

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

  ℕ→Ord : ℕ → Ord
  ℕ→Ord zero = zero
  ℕ→Ord (suc ω) = suc (ℕ→Ord ω)
  ω : Ord
  ω = lim ℕ→Ord
  0<ω : zero < ω
  0<ω = {!!} , (<lim Γ.zero zero ℕ→Ord 1 {!!} (<suc (Γ.zero , {!!}) zero))

  -- data isChild : (α β : Ord) → Type ℓ-zero where
  --   ischild : ∀ f i → isChild (node f) (f i) 
  
  -- -- not decidable.
  -- -- isChild? : (α β : Ord) → Dec (isChild α β)

  -- -- Not definable in general since we need arbitrary branching.
  -- -- lim' : (f : Ord → Ord) → Ord 

  -- infixl 30  _+ᵒ_ 
  -- _+ᵒ_ : Ord → Ord → Ord
  -- α +ᵒ 𝟘 = α
  -- α +ᵒ lim f = lim λ i → α +ᵒ f i

  -- _ : (ℕ→Ord 1) +ᵒ (ℕ→Ord 1) ≈ (ℕ→Ord 2)
  -- _ = ≈ext le ge
  --   where
  --   le : (ℕ→Ord 1 +ᵒ ℕ→Ord 1) ≤ ℕ→Ord 2
  --   le 𝟘 p = p
  --   le (lim f) p = p
  --   ge : ℕ→Ord 2 ≤ (ℕ→Ord 1 +ᵒ ℕ→Ord 1)
  --   ge = λ u p → p

  -- -- Probably not decidable
  -- -- 1+ω≈ω : 𝟙 +ᵒ ω ≈ ω

  -- -- Does this bring in an extra successor?
  -- _∙ᵒ_ : Ord → Ord → Ord
  -- α ∙ᵒ 𝟘 = 𝟘
  -- α ∙ᵒ lim f = lim (λ i → α ∙ᵒ f i)

  iterOrd : {A : Type} → Ord → A → (A → A) → ((ℕ → A) → A) → A 
  iterOrd zero z s l = z
  iterOrd (suc α) z s l = s (iterOrd α z s l)
  iterOrd (lim π) z s l = l (λ i → iterOrd (π i) z s l)

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

-- open ωOrdinal ℕ using (Ord; iterOrd)

module PermTree (A : Type) (B : Type) (_≟ᴮ_ : Discrete B)  where
  data Tree : Type where
    leaf : A → Tree
    node : (B → Tree) → Tree

  data Path : (t : Tree) → Type where
    nil : ∀ {t} → Path t
    cons : ∀ {f} i → Path (f i) → Path (node f)

  data isLeafPath : {t : Tree} (p : Path t) → Type where
    lpnil : ∀ {x} → isLeafPath (nil {leaf x})
    lpcons : ∀ {f} i → (p : Path (f i)) → isLeafPath p → isLeafPath (cons {f = f} i p)

  caseB : {X : Type} → B → X → (B → X) → B → X
  caseB i y n j = decRec (λ _ → y) (λ _ → n j) (j ≟ᴮ i)

  get : (t : Tree) → (p : Path t) → Tree
  get t nil = t
  get (node f) (cons i p) = get (f i) p

  set : (t : Tree) → (p : Path t) → Tree → Tree
  set t nil s = s
  set (node f) (cons i p) s = node g
    where
    g : B → Tree
    g = caseB i (set (f i) p s) (λ j → f j)

  swapB : ∀ (i j : B) → (B → B)
  swapB i j = caseB j i (caseB i j (λ k → k))

  -- Subpath
  -- data _≤ᵖ_ : {t : Tree} (p q : Path t) → Type where
  --   ≤nil : ∀ {t} (p : Path t)
  --        → nil {t} ≤ᵖ p
  --   ≤pextend : ∀ {f i} (p q : Path (f i)) → p ≤ᵖ q
  --            → cons {f} i p ≤ᵖ cons {f} i q

  -- bi-reachability
  -- _~ᵖ_ : {t : Tree} (p q : Path t) → Type
  -- p ~ᵖ q = (p ≤ᵖ q) ⊎ (q ≤ᵖ p)
  -- _≁ᵖ_ : {t : Tree} (p q : Path t) → Type
  -- p ≁ᵖ q = ¬ (p ~ᵖ q)

  -- ≤prefl : ∀ {t} → {p : Path t} → p ≤ᵖ p  
  -- ≤prefl {t} {nil} = ≤nil nil
  -- ≤prefl {node f} {cons i p} = ≤pextend p p ≤prefl

  -- ≤ptrans : ∀ {t} → {p q r : Path t} → p ≤ᵖ q → q ≤ᵖ r → p ≤ᵖ r
  -- ≤ptrans (≤nil _) _ = ≤nil _
  -- ≤ptrans (≤pextend p _ t) (≤pextend _ q s) = ≤pextend p q (≤ptrans t s)

  -- ~prefl : ∀ {t} → {p : Path t} → p ~ᵖ p
  -- ~prefl = inl ≤prefl

  -- ~psym : ∀ {t} → {p q : Path t} → p ~ᵖ q → q ~ᵖ p
  -- ~psym (inl r) = inr r
  -- ~psym (inr r) = inl r

  -- -- transitive bi-reachability
  -- data _~ᵖ_ : {t : Tree} (p q : Path t) → Type where
  --   ~pinl : ∀ {p q : Path t} → p ≤ᵖ q → p ~ᵖ q
  --   ~pinr : ∀ {p q : Path t} → q ≤ᵖ p → p ~ᵖ q
  --   ~ptrans : ∀ {t} → {p q r : Path t} → p ~ᵖ q → q ~ᵖ r → p ~ᵖ r 

  -- nil~p : ∀ {t} → (p : Path t) → nil {t} ~ᵖ p
  -- nil~p {t} p = inl (≤nil p)

  -- transPath : {s t : Tree} (p : Path s) 


  swap : (t : Tree) (p q : Path t) → Tree
  swap t p q = {!!}

  snoc : (t : Tree) (p : Path t) (i : B) (f : B → Tree) (n≡get : node f ≡ get t p) → Path t
  snoc t nil i f n≡get = subst Path n≡get (cons {f = f} i (nil {f i}))
  snoc (node g) (cons i p) j f n≡get = cons i (snoc (g i) p j f n≡get)

  get-snoc :
    (t     : Tree)
    (i     : B)
    (f     : B → Tree)
    (p     : Path t)
    (s≡get : node f ≡ get t p)
    → f i ≡ get t (snoc t p i f s≡get)
  get-snoc t i f p s≡get = {!!}
  


  -- perm : (t : Tree) (P : Path t → hProp ℓ) (φ : Iso (Σ[ p ∈ Path t ] ⟨ P p ⟩) (Σ[ p ∈ Path t ] ⟨ P p ⟩)) → Tree
  perm : (t : Tree) (φ : Iso (Path t) (Path t)) → Tree
  perm t φ = r t nil refl
    where
    r : (s : Tree) (p : Path t) (_ : s ≡ get t p) → Tree 
    r (leaf x) p _ = leaf x
    r (node f) p s≡get = node (λ i → r (f i) (snoc t p i f s≡get) {!!})

  -- Finite perm tree (swap tree)
  -- Local
  -- data _≈ꟳ_ : (s t : Tree) → Type where
  --   ≈refl : ∀ t → t ≈ꟳ t
  --   ≈swap : ∀ t → (p q : Path t)
  --               → swap p q p≁q ≈ꟳ t
  --   ≈trans : ∀ {s t u} → s ≈ꟳ t → t ≈ꟳ u → s ≈ꟳ u

  -- -- Indexed Perm tree (aribitrary permutations of leaves allowed)
  -- -- Non-local
  -- module _ {I : Type} where
  --   data _≈ᴾ_  : (s t : Tree) → Type where
  --     ≈refl : ∀ t → t ≈ᴾ t
  --     ≈perm : ∀ t (ps : I → Path t) → (p q : Path t)
  --           → (∀ (i j : I) → ps i ≁ᵖ ps j)
  --           → perm ps ≈ᴾ t
  --     ≈trans : ∀ {s t u} → s ≈ᴾ t → t ≈ᴾ u → s ≈ᴾ u


module HoleyList (A : Type) where
  infixl 30 _∷_
  data HoleyList : Type where
    [] : HoleyList
    ●∷_ : HoleyList → HoleyList
    _∷_ : A → HoleyList → HoleyList

  data _≈_ : HoleyList → HoleyList → Type where
    ≈refl : ∀ xs → xs ≈ xs
    ≈swap : ∀ n x y xs
          → x ∷ iterℕ n ●∷_ (y ∷ xs)
          ≈ y ∷ iterℕ n ●∷_ (x ∷ xs)
    ≈trans : ∀ {s t u} → s ≈ t → t ≈ u → s ≈ u

--   ≈refl : ∀ {t} → t ≈ t
--   ≈refl {leaf} = ≈leaf
--   ≈refl {node f} = ≈node λ b → ≈refl {f b}

--   ≈sym : ∀ {s t} → s ≈ t → t ≈ s
--   ≈sym ≈leaf = ≈leaf
--   ≈sym (≈node c) = ≈node λ b → ≈sym (c b)
--   ≈sym (≈perm {f} π) =
--     subst
--       (λ h → node (f ∘ fun π) ≈ node (f ∘ h))
--       (funExt (rightInv π))
--       (≈perm {f = f ∘ fun π} (invIso π))
--   ≈sym (≈trans s≈t t≈u) = ≈trans (≈sym t≈u) (≈sym s≈t)

--   MobileSetoid : Setoid ℓ-zero ℓ-zero
--   MobileSetoid = BTree B , record
--     { _≈_ = _≈_
--     ; equiv = equivRel
--       (λ t → ≈refl {t})
--       (λ _ _ p → ≈sym p)
--       (λ _ _ _ p q → ≈trans p q) }
      

      
-- module _ (A : Type) (B : Type) (_≟ᴮ_ : Discrete B) where
--   data TreeBag : Type where
--     leaf : A → TreeBag
--     node : A → (B → TreeBag) → TreeBag

--   Bswap : ∀ (i j : B) → (B → B)
--   Bswap i j k with (k ≟ᴮ i) | (k ≟ᴮ j)
--   ... | no ¬k≡i | no ¬k≡j = k
--   ... | yes k≡i | no ¬k≡j = j
--   ... | no ¬k≡i | yes k≡j = i
--   ... | yes k≡i | yes k≡j = k
  
--   data _≈_ : TreeBag → TreeBag → Type where
--     ≈refl : ∀ t → t ≈ t
--     ≈node : ∀ x f i j → node x f ≈ node x (f ∘ Bswap i j)
--     ≈child : ∀ x y f g i j → f i ≈ node y g
--            → {!!} 

Fiore et al. uses IWISC to:
 (a) give a cover for the underlying W type (`W Σ`) 
 (b) give a cover for the equivalence relation `_≈_` over `W Σ`.

We replace this (from Fiore et al. 2022):
> Theorem 5.7 (Cocontinuity). Suppose U is a universe satisfying IWISC
  in a topos with natural numbers object. Given A ∶ U and B ∶ A → U,
  there exists a type of sizes Size ∶ U with the property that for all
  a ∶ A, taking a power by the type B a ∶ U preserves Size-indexed
  colimits.

...and instead construct a size type for `W Σ` and `_≈_`. 

I think in the general QIIT, we just need a cover for every inductive
type. I think it's best to think about general QIITs, or at least IITs
generating QITs.

So we want:
1. A subclass (QW-cons) of QW types for which a cover can be constructed.
2. A procedure to construct the QW types automatically for some subclass (say QW-aut).
3. A syntax where the QW-cons can be specified (similar to well-founded induction)

TODO: Define locality.

Note that I have introduced a term locality, which may be a bad
name. It's about bounding depth of expansion in the patterns.

QW-aut is the class of types that we can determine automatically. We
then need a bound on the construction. The key thing is whether
there's an ordinal bound to all paths in the signature of the
rule.

- Mobiles are 1-local, since permutation occurs within a single
node.
- SwapTrees ≅ FinPermTrees are ω-local.
- PermTrees & Ord are non-local.
- Bags are 3-local
- CoBags non-local.

I don't think that we can require strict well-foundedness in the general case.
We instead have to have an accessability predicate to prove
well-foundedness, otherwise a large class of desired QITs are not
representable. For example, 'Elasticℕ' which is ⟨ 0 , +1 , +0 ⟩ / ⟨ (∀
n → n +0 ≡ n) ⟩ is strictly non-well-founded. This is a refinement of the more general
'SumList': lists of ℕ, equating any two lists that have the same sum. 
Ordinals the way that they're normally defined aren't
well-founded, since `lim (λ i → zero) ≈ zero`. You have to ensure each operator adds to the height in
the quotient and that there is some accessibility relation. In general
for most non-trivial cases it'll probably be preferable for the user
defines a relation and proves that it's WF on the quotient type.

Fiore et al. define it as below. So the most direct thing to do

-- Definition 5.1 (Size)
record SizeStructure {l : Level} (Size : Set l) : Set (lsuc l) where
  field
    _<_   : Size → Size → Prop l
    <<    : ∀{i j k} → j < k → i < j → i < k
    <iswf : wf.iswf _<_
    Oˢ    : Size
    _∨ˢ_  : Size → Size → Size
    <∨ˢl  : ∀{i} j  → i < i ∨ˢ j
    <∨ˢr  : ∀ i {j} → j < i ∨ˢ j

This is,
  Sig→Fam : Sig {l} → Fam l
  Sig→Fam (mkSig op ar) = mkFam op ar

  CoverSubTypeFam : (Σ : Sig {l}) → WISC-Cover (Sig→Fam Σ) → Fam l
  CoverSubTypeFam Σ U = mkFam (∑ (c , a) ∶ C × (Op Σ) , (F c → Ar Σ a)) λ{(_ , f) → ker f}
    where open WISC-Cover U

  data WISC-CoveringRecord (Σ : Sig {l}) : Prop (lsuc l) where
    mkWISC-CoveringRecord
      : (U : WISC-Cover (Sig→Fam Σ))
      → (V : WISC-Cover (CoverSubTypeFam Σ U))
      → WISC-CoveringRecord Σ

  IWISC→WISC-CoveringRecord : ∀ Σ → WISC-CoveringRecord Σ
  IWISC→WISC-CoveringRecord Σ
    with IWISC (mkFam (Op Σ) (Ar Σ))
  ... | ∃i (mkFam C F) w
    with IWISC (mkFam (∑ (c , a) ∶ C × (Op Σ) , (F c → Ar Σ a)) λ{(_ , f) → ker f})
  ... | ∃i (mkFam C' F') w' = mkWISC-CoveringRecord (mkWISC-Cover C F w) (mkWISC-Cover C' F' w')

where we have
  IWISC :
    {l : Level}
    (F : Fam l)
    → ------------------------------------
    ∃ W ∶ Fam l , ∀ c → wisc (fiber F c) W

record WISC-Cover {l : Level} (F' : Fam l) : Set (lsuc l) where
  constructor mkWISC-Cover
  field
    C : Set l
    F : C → Set l
    w : ∀ c → wisc (fiber F' c) (mkFam C F)

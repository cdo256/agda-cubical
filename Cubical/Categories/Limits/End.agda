{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Limits.End where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Cospan
open import Cubical.Categories.Limits.Limits
open import Cubical.Categories.Functor.Bifunctor
open import Cubical.Categories.NaturalTransformation.Dinatural
open import Cubical.Categories.Functors.Constant 
open import Cubical.Categories.Constructions.BinProduct 
open import Cubical.Categories.Limits.Wedge

private
  variable
    ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (F : Bifunctor (C ^op) C D) where
  open DinaturalTrans
  private
    module C = Category C
    module D = Category D
    module F = Functor F
    Wedge' = Wedge {C = C} F
    Cowedge' = Cowedge {C = C} F
    Const = Constant (C ^op ×C C) D
    -- open Wedge renaming (E to E₁)
    open Wedge
    -- open Wedge renaming (E to E₁)

  End' : Type _
  End' = {!!}

  Triangle : (W W' : Wedge') → (f : D [ W' .E , W .E ])
           → Type _
  Triangle W W' f = ∀ {A} → f D.⋆ W .dinatural .α A ≡ W' .dinatural .α A

  record End : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
    field
      W : Wedge'
      factor : (W' : Wedge') → D [ W' .E , W .E ]
      universal : ∀ {W' : Wedge'} {A}
                → factor W' D.⋆ W .α A ≡ W' .dinatural .α A
                → Triangle W W' (factor W')
      unique : ∀ {W' : Wedge'} {g : D [ W' .E , W .E ]}
             → Triangle W W' g → factor W' ≡ g  

  -- CoTriangle : (W W' : Cowedge') → (f : D [ W .E , W' .E ])
  --           → Type _
  -- CoTriangle W W' f = ∀ {A} → (W .dinatural .α A) D.⋆ {!!} ≡ {!W' .dinatural .α A!}

  -- record Cowedge : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD')) where
  --   field
  --     E         : D.ob
  --     dinatural : DinaturalTrans {C = C} F (Const E)

    

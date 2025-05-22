open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf 
open import Cubical.Categories.Constructions.Elements 
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Functor

open import TCategory -- Categories with a terminal object
open import TyStr
open import DepPoly

open Category
open Contravariant

module CwF where

  open Category
  open Contravariant
  open Functor
  

  record CwF {ℓ ℓ' : Level} (Ctxt : (Category ℓ ℓ')) (T : TCategory Ctxt) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) ℓ) ℓ') where -- one would want a TCategory here, then one would need to redefine Presehaf 
    field

      TyP : Presheaf Ctxt ℓ-zero

      TmP : Presheaf (∫ᴾ TyP) ℓ-zero 

      TmCtxt : {Γ : Category.ob Ctxt} (Ty : (fst (F-ob TyP Γ)) ) → (Presheaf (SliceCat Ctxt Γ)  ℓ-zero)

  open CwF

      -- (fst (F-ob TyP Γ)) we use fst since the result comes as a sigma type

        -- [_]ty : (Γ Δ : Ob) (σ : Hom Γ Δ) → 𝕋y Δ → 𝕋y Γ

      -- Ext : (Γ : Ob) → 𝕋y Γ → Ob 

      -- 𝟙 : Ob we dont nee this, this is handled by TCategory
{-
  postulate

    CwF-slice : (C : CwF) → Ob C → CwF

  CwFToTyStr : (C : CwF) → TyStr
  CwFToTyStr C .Ty = 𝕋y C (𝟙 C)
  CwFToTyStr C ._//_ T = CwFToTyStr (CwF-slice C (Ext C (𝟙 C) T))

  postulate
  
    CwFToDepPoly : (C : CwF) → DepPoly (CwFToTyStr C) (CwFToTyStr C) -- this should somehow work using substitions: This works since Subst in DepPoly is apllying a depndent polynomial, so we somehow want to turn substitution, given by CwF into a DepPoly
-}
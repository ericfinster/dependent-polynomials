{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude 

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Presheaf 
open import Cubical.Categories.Constructions.Elements 
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Functor
open import Cubical.Data.Bool

open import TCategory -- Categories with a terminal object
open import TyStr
open import DepPoly
open import CwFH

module CwFHToDepPoly where

    -- Returns a TyStr from a CwF by slicing over the terminal object extended with the given Type
    CwFHToTyStr : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) → TyStr
    CwFHToTyStr {T = T} CwF .Ty = CwFH.TyP CwF (TCategory.TerObj T)
    CwFHToTyStr {T = T} CwF // x = CwFHToTyStr (CwFHslice CwF x)

    DropCtxLvl : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T)
            → (A : (CwFH.TyP CwF (TCategory.TerObj T))) → (Γ : (Ctx (CwFHToTyStr (CwFHslice CwF A))))
            → (Ctx (CwFHToTyStr CwF))
    DropCtxLvl {ℓ} {ℓ'} {Ctxt} {T} CwF A ϵ = ?
    DropCtxLvl {ℓ} {ℓ'} {Ctxt} {T} CwF A (T₁ ► Γ) = ?

    -- TyStr Ctxts are Ctxt Obj
    ContextToObj : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T) 
            → (Γ : (Ctx(CwFHToTyStr CwF))) → (Ctxt .ob)
    ContextToObj {T = Ter} CwF ϵ = TCategory.TerObj Ter
    ContextToObj {T = Ter} CwF (T ► Γ) = S-ob (ContextToObj (CwFHslice CwF T) Γ)

    ContextToObjArr : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T) 
            → (Γ : (Ctx(CwFHToTyStr CwF))) → (Ctxt [ (ContextToObj CwF Γ) , (TCategory.TerObj T) ])
    ContextToObjArr {Ctxt = Ctxt} CwF ϵ = id Ctxt
    ContextToObjArr {Ctxt = Ctxt} {T = T} CwF (T' ► Γ) = Ctxt ._⋆_ (S-hom (ContextToObjArr (CwFHslice CwF T') Γ)) (TCategory.TermPr T {CwFH.cextOb CwF (TCategory.TerObj T) T'})

    TyToCtxt : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T)
            → (A : CwFH.TyP CwF (TCategory.TerObj T)) → (Ctx (CwFHToTyStr CwF))
    TyToCtxt CwF A = A ► ϵ

    ObjToCtxt : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T)
            → (A : CwFH.TyP CwF (TCategory.TerObj T)) → (Γ : Ctx (CwFHToTyStr (CwFHslice CwF A)))
            → (Ctx (CwFHToTyStr CwF))
    ObjToCtxt CwF A Γ = A ► Γ

    -- This could be simplified by TmToSubst
    SubstToSubst : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) → (Γ : Ctx (CwFHToTyStr CwF))
          {M : DepPoly (CwFHToTyStr CwF) (CwFHToTyStr CwF)} → (A : CwFH.TyP CwF (TCategory.TerObj T))
          (t : Tm M Γ A) → (Subst M Γ (A ► ϵ))
    SubstToSubst {ℓ} {Ctxt} {T} CwF Γ {M} A t = subst (λ Γ → Subst M Γ (A ► ϵ)) (++-unit-left Γ) (cns Γ A t ϵ ϵ (● ϵ))

    ContextToSliceOb : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) → (Γ : Ctx (CwFHToTyStr CwF))
        → (A : CwFH.TyP CwF (TCategory.TerObj T)) → (t : CwFH.TmP CwF (CwFH.TyPm CwF (TCategory.TermPr T) A)) →  (Category.ob (SliceCat Ctxt (CwFH.cextOb CwF (TCategory.TerObj T) A)))
    ContextToSliceOb {T = T} CwF Γ A t = sliceob (CwFH.cextHomM CwF (TCategory.TermPr T {ContextToObj CwF Γ}) t)

    nextPr : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} (CwF : CwFH Ctxt T)
                → (Γ : Ctxt .ob) → (A B : (CwFH.TyP CwF Γ)) 
                → (Ctxt [ (CwFH.cextOb CwF (CwFH.cextOb CwF Γ A) ((CwFH.TyPm CwF (CwFH.cextHom1 CwF A)) B)) , (CwFH.cextOb CwF Γ B) ])
    nextPr {ℓ} {Ctxt} {T} CwF Γ A B = WeakeningTy CwF (CwFH.cextHom1 CwF A) B

    
{-
    WeakeningCtxt : {ℓ : Level} {Ctxt Ctxt' : Category ℓ ℓ} {T : TCategory Ctxt} {T' : TCategory Ctxt'} (CwF : CwFH Ctxt T) → (CwF' : CwFH Ctxt' T') → (Γ : (Ctx (CwFHToTyStr CwF)))
                → (A : (CwFH.TyP CwF' (TCategory.TerObj T'))) → (g : Ctxt [ (CwFH.cextOb CwF' (TCategory.TerObj T') A) ,  ]) → (Ctx (CwFHToTyStr (CwFHslice CwF A)))
    WeakeningCtxt {ℓ} {Ctxt} {T} CwF ϵ A = ϵ
    WeakeningCtxt {ℓ} {Ctxt} {T} CwF (B ► Γ) A = {! Γ  !} ► {!   !}
-}
    CtxtMove : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) 
                → (A : CwFH.TyP CwF (TCategory.TerObj T)) → (Γ : (Ctx (CwFHToTyStr CwF))) → (f : Ctxt [ (ContextToObj CwF Γ) , (CwFH.cextOb CwF (TCategory.TerObj T) A) ])
                → (Ctx (CwFHToTyStr CwF))
    CtxtMove {ℓ} {Ctxt} {T} CwF A ϵ f = A ► ϵ 
    CtxtMove {ℓ} {Ctxt} {T} CwF A (B ► Γ) f = A ► ({! S-ob Γ  !} ► {! CtxtMove   !}) 
    
    postulate

        NeededCtx : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) 
            → (A : CwFH.TyP CwF (TCategory.TerObj T)) → (Γ : (Ctx (CwFHToTyStr CwF))) → (t : CwFH.TmP CwF (CwFH.TyPm CwF (TCategory.TermPr T {ContextToObj CwF Γ}) A))
            → (Ctx (CwFHToTyStr (CwFH.CwFHslice CwF A))) 

    {-# TERMINATING #-}
    CwFHToDepPoly : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} (CwF : CwFH Ctxt T)
                 → (DepPoly (CwFHToTyStr CwF) (CwFHToTyStr CwF))
    CwFHToDepPoly {T = T} CwF .Tm Γ A = CwFH.TmP CwF {Γ = ContextToObj CwF Γ} (CwFH.TyPm CwF (TCategory.TermPr T) A) 
    CwFHToDepPoly {Ctxt = Ctxt} {T} CwF .⇑ {Γ} {A} t = CwFHToDepPoly (CwFHslice CwF A)
    
    -- ⌈_⌉s (SubstToSubst CwF Γ {M = CwFHToDepPoly CwF} A t) seems to be the right idea but agda kills itself trying to check if it terminates
    -- which turns into a problem when trying to prove Monad properties, since then the proof assistant features break

    -- SubstToSubst (CwFHslice CwF A) {M = (CwFHToDepPoly (CwFHslice CwF A))} (CwFH.TyPm CwF (CwFH.cextHom1 CwF A) A)
    -- (CwFH.TmPm CwF (S-hom (TCategory.TermPr (CwFHTerminal CwF A))) (CwFH.TyPm CwF (CwFH.cextHom1 CwF A) A) t)
      -- ⌈_⌉s {CwFHToTyStr (CwFHslice CwF A)} {CwFHToTyStr (CwFHslice CwF A)} {have} 
  -- ⌈_⌉s : {𝕊 𝕋 : TyStr} {M : DepPoly 𝕊 𝕋}
  --   → {Γ : Ctx 𝕊} {Δ : Ctx 𝕋}
  --   → Subst M Γ Δ
  --   → DepPoly ⌈ Γ ⌉ ⌈ Δ ⌉

      where

        Γobj : Ctxt .ob
        Γobj = ContextToObj CwF Γ

        Γobj→A : Ctxt [ Γobj , CwFH.cextOb CwF (TCategory.TerObj T) A ]
        Γobj→A = CwFH.cextHomM CwF (TCategory.TermPr T) t

        ΓAobj : (SliceCat Ctxt (CwFH.cextOb CwF (TCategory.TerObj T) A)) .ob
        ΓAobj = ContextToSliceOb CwF Γ A t

        have : DepPoly (CwFHToTyStr (CwFHslice CwF A)) (CwFHToTyStr (CwFHslice CwF A))
        have = CwFHToDepPoly (CwFHslice CwF A)


      -- ⇑ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm Γ T)
      --   → DepPoly ⌈ Γ ⌉ (𝕋 // T)

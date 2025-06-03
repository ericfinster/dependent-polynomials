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

    -- TyStr Ctxts are Ctxt Obj
    ContextToObj : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T) 
            → (Γ : (Ctx(CwFHToTyStr CwF))) → (Ctxt .ob)
    ContextToObj {T = Ter} CwF ϵ = TCategory.TerObj Ter
    ContextToObj {T = Ter} CwF (T ► Γ) = S-ob (ContextToObj (CwFHslice CwF T) Γ)

    -- returns the level of the objects resulting from recusively slicing over Types in a ctxt
    SliceLevel : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T) 
                → (Γ : (Ctx(CwFHToTyStr CwF))) → (Level)
    SliceLevel {ℓ} CwF ϵ = ℓ
    SliceLevel CwF (T ► Γ) = SliceLevel (CwFHslice CwF T) Γ

    -- allows me to alter the return Type of SliceAlongContext depending on if the Ctxt is empty
    CatOr : {ℓ ℓ' : Level} {Ctxt1 : Category ℓ ℓ'} {T : TCategory Ctxt1} → (CwF : CwFH Ctxt1 T) 
              → (Γ : (Ctx(CwFHToTyStr CwF))) → (Ctxt2 : Category (SliceLevel CwF Γ) ℓ') → (Category (SliceLevel CwF Γ) ℓ')
    CatOr {Ctxt1 = Ctxt1} CwF ϵ Ctxt2 = Ctxt1
    CatOr CwF (T ► Γ) Ctxt2 = Ctxt2

    -- Same as CatOr but for the added Terminal object structure
    TCatOr : {ℓ ℓ' : Level} {Ctxt1 : Category ℓ ℓ'} {T1 : TCategory Ctxt1} → (CwF : CwFH Ctxt1 T1) 
             → (Γ : (Ctx(CwFHToTyStr CwF))) → {Ctxt2 : Category (SliceLevel CwF Γ) ℓ'} → (T2 : TCategory Ctxt2)
             → (TCategory (CatOr CwF Γ Ctxt2))
    TCatOr {T1 = T1} CwF ϵ T2 = T1
    TCatOr CwF (T ► Γ) T2 = T2
  
    -- Given some TyStr Ctxt I want to repeatedly slice over the Obj build up by extending with the types in the Ctxt
    -- The idea is to be able to handle ⌈ Γ ⌉ better, since I want to use it's inherent CwF structure but can't at the moment
    SliceAlongContext : {ℓ ℓ' : Level} {Ctxt1 : Category ℓ ℓ'} {T1 : TCategory Ctxt1} → (CwF : CwFH Ctxt1 T1) 
                → (Ctx : (Ctx(CwFHToTyStr CwF))) → {Ctxt2 : Category (SliceLevel CwF Ctx) ℓ'} → {T2 : TCategory Ctxt2} 
                → (CwFH (CatOr CwF Ctx Ctxt2) (TCatOr CwF Ctx T2))
    SliceAlongContext CwF ϵ = CwF
    SliceAlongContext CwF (T ► ϵ) = {! CwFHslice CwF T !}
    SliceAlongContext CwF (T ► (T₁ ► Ctx₁)) = SliceAlongContext (CwFHslice CwF T) ((T₁ ► Ctx₁))

    -- SliceAlongContext (CwFHslice CwF T) (T₁ ► Ctx₁)
    -- Ctxt2
    -- SliceAlongContext (CwFHslice CwF T) Γ

    -- I want to be able to treat a context in ⌈ Γ ⌉ like an Object in my CwF 
    -- to be able to use the CwF properties in helpCwFToDepPoly
    ContextToObj2 : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T) -- we can probably do this way easier by just appending the two contexts which is ++ in TyStr 
            → {Γ : (Ctx(CwFHToTyStr CwF))} → (Ct : (Ctx ⌈ Γ ⌉)) → (Ctxt .ob)
    ContextToObj2 {ℓ} {ℓ'} {Ctxt} {T} CwF {Γ} ϵ = ContextToObj CwF Γ
    ContextToObj2 {ℓ} {ℓ'} {Ctxt} {T} CwF {Γ} (T₁ ► Ct) = {!  SliceAlongContext CwF Γ  !}

    ContextToObj3 : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} → (CwF : CwFH Ctxt T) 
            → {Γ : (Ctx(CwFHToTyStr CwF))} → (Ct : (Ctx ⌈ Γ ⌉)) → (Ctxt .ob)
    ContextToObj3 {ℓ} {ℓ'} {Ctxt} {T} CwF {Γ} ϵ = ContextToObj CwF Γ
    ContextToObj3 {ℓ} {ℓ'} {Ctxt} {T} CwF {Γ} (T₁ ► Ct) = ContextToObj CwF (Γ ++ (T₁ ► Ct))
 
  {-
  Probably not needed at least not for my current train of thought
  seems like a more crude version of what is now helpCwFHToDepPoly
    CwFHToDepPolyAscend : {ℓ ℓ' ℓ'' ℓ''' : Level} {Ctxt1 : Category ℓ ℓ'} {Ctxt2 : Category ℓ'' ℓ'''} 
      {T1 : TCategory Ctxt1} {T2 : TCategory Ctxt2} (CwF1 : CwFH Ctxt1 T1) → (CwF2 : CwFH Ctxt2 T2) 
      → (DepPoly (CwFHToTyStr CwF1) (CwFHToTyStr CwF2))  
    CwFHToDepPolyAscend CwF1 CwF2 .Tm x x₁ = {!   !}
    CwFHToDepPolyAscend CwF1 CwF2 .⇑ = {!   !}
  -}


    -- helper function to be able to substitute in the resulting Ty we pass to the function, 
    -- according to it's dependency on the level below
    -- right now the problem is that I can't relly use a Ctxt in ⌈ Γ ⌉ since I don't know how to access it's CwF structure
    -- which it retains since it comes from CwF to TyStr
    helpCwFHToDepPoly : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt}
         {CwF : CwFH Ctxt T} {Γ : Ctx (CwFHToTyStr CwF)}
         {T = T₁ : CwFH.TyP CwF (TCategory.TerObj T)} →
       Hom[ Ctxt , ContextToObj CwF Γ ]
       (CwFH.cextOb CwF (T .TCategory.TerObj) T₁) →
       DepPoly ⌈ Γ ⌉ (CwFHToTyStr (CwFHslice CwF T₁))
    helpCwFHToDepPoly {T = T₁} {CwF} {Γ} {T = T₂} x .Tm x₁ x₂ = CwFH.TmP CwF {(ContextToObj CwF Γ)} ((CwFH.TyPm CwF x) x₂)
    helpCwFHToDepPoly {T = T₁} {CwF} {Γ} {T = T₂} x .⇑ {Γ₁} {T} t = {! CwFH.TmPm CwF (TCategory.TermPr T₁ {(ContextToObj2 CwF Γ)})  !}

        -- cextHomM (CwFHslice CwF T₂) 
    -- (TyPm CwF x) x₂ 
    -- TmP CwF {(ContextToObj CwF Γ)}
    -- CwFH.cextHomM CwF (TCategory.TermPr T₁ {(ContextToObj2 CwF Γ)}
    -- CwFH.TmPm CwF (TCategory.TermPr T₁ {(ContextToObj2 CwF Γ)}) wants a term in the terminal of T1 
    -- ((CwFH.TyPm CwF x) T) is a Type in CtxtToObj
    

    CwFHToDepPoly : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T)
                 → (DepPoly (CwFHToTyStr CwF) (CwFHToTyStr CwF))
    CwFHToDepPoly CwF .Tm x x₁ = CwFH.TmP CwF x₁ 
        -- since we have a substitution into the empty ctxt we just return the terms
    CwFHToDepPoly CwF .⇑ t = {!   !} 
    
    -- here I'm thinking I want to use helpCwFHToDepPoly the idea is to pass the extended substitution along 
    -- and substitute in the new Terms in the resulting polynomial

    -- I'm thinking there could be a way to build up substitutions like one builds up contexts, so we start on the term level with the 
    -- empty substitution. And then like we build up the domain context, we build up substitutions into it
    -- See the substitution defined below

-- (cextHomM CwF (TCategory.TermPr T {(ContextToObj CwF Γ)}) ((TmPm CwF (TCategory.TermPr T {(ContextToObj CwF Γ)}) T₁) t)) 
-- {T₁ = T₁}
-- (TmPm (TCategory.TermPr T {(ContextToObj CwF Γ)})

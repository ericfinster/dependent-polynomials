

open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import BSystems

module BSystemToDepPoly where


    BSystemToTyStr : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → TyStr
    BSystemToTyStr {B} BS .Ty = TyTmStr.Typ B
    BSystemToTyStr {B} BS // x = BSystemToTyStr (BSystem.BSlc BS x)

    -- -- -- Converting Contexts

    CtxPToCtxB : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (Ctxt B)
    CtxPToCtxB BS ϵ = ε
    CtxPToCtxB BS (T ► Γ) = T ⊳ (CtxPToCtxB (BSystem.BSlc BS T) Γ)

    CtxBToCtxP : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctxt B) → (Ctx (BSystemToTyStr BS))
    CtxBToCtxP BS ε = ϵ
    CtxBToCtxP BS (T ⊳ Γ) = T ► (CtxBToCtxP (BSystem.BSlc BS T) Γ)

    rInv : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctxt B) → (CtxPToCtxB BS (CtxBToCtxP BS Γ)) ≡ Γ
    rInv BS ε = refl
    rInv BS (T ⊳ Γ) = cong (λ x → T ⊳ x) (rInv (BSystem.BSlc BS T) Γ)

    lInv : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (CtxBToCtxP BS (CtxPToCtxB BS Γ)) ≡ Γ
    lInv BS ϵ = refl
    lInv BS (T ► Γ) = cong (λ x → T ► x) (lInv (BSystem.BSlc BS T) Γ)

    -- -- --

    CtxToTyTmStr : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (TyTmStr)
    CtxToTyTmStr {B} BS ϵ = B
    CtxToTyTmStr BS (T ► Γ) = CtxToTyTmStr (BSystem.BSlc BS T) Γ

    CtxToPreSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (PreBSystem (CtxToTyTmStr BS Γ))
    CtxToPreSys {Bᵇ = Bᵇ} BS ϵ = Bᵇ
    CtxToPreSys BS (T ► Γ) = CtxToPreSys (BSystem.BSlc BS T) Γ

    CtxToBSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (BSystem (CtxToTyTmStr BS Γ) (CtxToPreSys BS Γ))
    CtxToBSys BS ϵ = BS
    CtxToBSys BS (T ► Γ) = CtxToBSys (BSystem.BSlc BS T) Γ

    NewCtx : {A B : TyTmStr} {Bᵇ : PreBSystem B} {Aᵇ : PreBSystem A} (BS : BSystem B Bᵇ) (AS : BSystem A Aᵇ) (Γ : Ctx (BSystemToTyStr BS)) (f : B ↝ A)
            → (Ctx (BSystemToTyStr AS))
    NewCtx BS AS ϵ f = ϵ
    NewCtx BS AS (T ► Γ) f = (_↝_.Ty↝ f T) ► NewCtx (BSystem.BSlc BS T) (BSystem.BSlc AS (_↝_.Ty↝ f T)) Γ (_↝_.Slc↝ f T)

    DropCtx : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) → (Γ : (Ctx (BSystemToTyStr (BSystem.BSlc BS T))))
            → (Ctx (BSystemToTyStr BS))
    DropCtx BS T Γ = T ► Γ

    CtxSliceBSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) → (Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
    CtxSliceBSys {Bᵇ = Bᵇ} BS Γ T = NewCtx BS (BSystem.BSlc BS T) Γ (PreBSystem.wk Bᵇ T)

    ⌈_⌉BSysEqual : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
            → ⌈ Γ ⌉ ≡ (BSystemToTyStr (CtxToBSys BS Γ))
    ⌈_⌉BSysEqual BS ϵ = refl
    ⌈_⌉BSysEqual BS (T₁ ► Γ) = ⌈_⌉BSysEqual (BSystem.BSlc BS T₁) Γ

    EqHelp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ' : Ctx (BSystemToTyStr BS))
            → Γ' ≡ (transport (λ i → Ctx (BSystemToTyStr BS)) Γ')
    EqHelp BS Γ' = sym (transportRefl Γ')

    -- maybe needed for BSystemToMonad
    TyTmStr++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → (CtxToTyTmStr BS (Γ ++ Γ')) ≡ (CtxToTyTmStr (CtxToBSys BS Γ) (transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i))) Γ'))
    TyTmStr++Eq BS ϵ Γ' = cong (λ x → CtxToTyTmStr BS x) (EqHelp BS Γ')
    TyTmStr++Eq BS (T ► Γ) Γ' = TyTmStr++Eq (BSystem.BSlc BS T) Γ Γ'

--     BSys++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
--                  → (TopTyTm (CtxPToCtxB (CtxToBSys BS Γ₁) (Γ ++ Γ'))) ≡ (TopTyTm (CtxPToCtxB (CtxToBSys (CtxToBSys BS Γ₁) Γ) Γ'))
--     BSys++Eq = ?

    TerminalProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → B ↝ (CtxToTyTmStr BS Γ)
    TerminalProj {B} BS ϵ = idStr B
    TerminalProj {Bᵇ = Bᵇ} BS (T ► Γ) = (TerminalProj (BSystem.BSlc BS T) Γ) ○ (PreBSystem.wk Bᵇ T)


    TerminalProjComp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → PathP  (λ i → (B ↝ (TyTmStr++Eq BS Γ Γ' i))) (TerminalProj BS (Γ ++ Γ')) 
            ((TerminalProj (CtxToBSys BS Γ) (transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i))) Γ')) ○ (TerminalProj BS Γ))
    TerminalProjComp BS ϵ Γ' = cong (λ x → TerminalProj BS x) (EqHelp BS Γ') ▷ (sym (IdStrRN (TerminalProj BS (transport (λ i → Ctx (BSystemToTyStr BS)) Γ'))))
    TerminalProjComp {Bᵇ = Bᵇ} BS (T ► Γ) Γ' = congP (λ i → (λ x → x ○ (PreBSystem.wk Bᵇ T))) (TerminalProjComp (BSystem.BSlc BS T) Γ Γ') 
               ▷ (○-assoc (TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) (transport (λ i → Ctx (⌈ BSystem.BSlc BS T ⌉BSysEqual Γ i)) Γ')) 
                (TerminalProj (BSystem.BSlc BS T) Γ) (PreBSystem.wk Bᵇ T))


    EqStep : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
            → ⌈ (CtxSliceBSys BS Γ T) ⌉ ≡ ⌈ (DropCtx BS T (CtxSliceBSys BS Γ T)) ⌉
    EqStep BS Γ T = refl

    NeededSubstGen : {A B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
            (f : B ↝ (CtxToTyTmStr AS Γ)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T))
            → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ))
    NeededSubstGen AS BS Γ f T t = (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ (_↝_.Slc↝ f T)

    NeededSubst : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
                → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr BS Γ))
    NeededSubst BS Γ T t = NeededSubstGen BS BS Γ (TerminalProj BS Γ) T t
    

    {-# TERMINATING #-}
    BSystemToDepPolyHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
                (T : TyTmStr.Typ B) (f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ)) 
                → (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr (BSystem.BSlc BS T)))
    BSystemToDepPolyHelp AS BS Γ T f .Tm x x₁ = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) 
        x) (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) x ○ f) x₁)
    BSystemToDepPolyHelp {Aᵇ = Aᵇ} AS BS Γ T f .⇑ {x} {T'} t = transport (λ i → DepPoly (⌈_⌉BSysEqual (CtxToBSys AS Γ) x (~ i)) (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T')))
        (BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T) x T'
        (NeededSubstGen (CtxToBSys AS Γ) (BSystem.BSlc BS T) x ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T' t))

        {-
        (BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T) x T'
        (NeededSubstGen (CtxToBSys AS Γ) (BSystem.BSlc BS T) x ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T' t))
        -}

    
    BSystemToDepPoly : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (DepPoly (BSystemToTyStr BS) (BSystemToTyStr BS))
    BSystemToDepPoly BS .Tm Γ T = TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T)
    BSystemToDepPoly BS .⇑ {Γ} {T} t = transport (λ i → DepPoly (⌈_⌉BSysEqual BS Γ (~ i)) (BSystemToTyStr (BSystem.BSlc BS T)))
        (BSystemToDepPolyHelp BS BS Γ T (NeededSubst BS Γ T t))

    {-
    (BSystemToDepPolyHelp BS BS Γ T (NeededSubst BS Γ T t))
    -}
{-
    -- -- -- Converting Substitutions

    SubstToHomHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                {T : TyTmStr.Typ B} {f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ)}
                {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T))}
                (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ T f) Γ' Δ')
                → (TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ')) ↝ (TopTyTm (CtxPToCtxB (CtxToBSys AS Γ) Γ'))
    SubstToHomHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● _) = (wkCtxt (CtxToPreSys AS Γ) (CtxPToCtxB (CtxToBSys AS Γ) Γ')) ○ f
    SubstToHomHelp (cns Γ T t Γ' Δ' ɣ) = {!   !}


        -- someting like NeededSubst but iteratively is what needs to be done here

    SubstToHom : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
                (Δ : Ctx (BSystemToTyStr BS)) (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                → (TopTyTm (CtxPToCtxB BS Δ)) ↝ (TopTyTm (CtxPToCtxB BS Γ))
    SubstToHom {Bᵇ = Bᵇ} BS Γ Δ (● .Γ) = wkCtxt Bᵇ (CtxPToCtxB BS Γ)
    SubstToHom {Bᵇ = Bᵇ} BS Γ Δ (cns Γ₁ T t Γ' Δ' ɣ) = {!   !}

--     SubstToList : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
--                 (Δ : Ctx (BSystemToTyStr BS)) (ɣ : Subst (BSystemToDepPoly BS) Γ Δ) 
--                 → (ListOfTerms Bᵇ (CtxPToCtxB BS Γ))
--     SubstToList BS Γ Δ (● .Γ) = {!   !}
--     SubstToList BS Γ Δ (cns Γ₁ T t Γ' Δ' ɣ) = {!   !}

--     ListToSubst : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctxt B) (L : ListOfTerms Bᵇ Γ) 
--                 → (Subst (BSystemToDepPoly BS) (CtxBToCtxP BS Γ) (CtxBToCtxP BS (SubstCtxt Bᵇ Γ L)))
--     ListToSubst {B} {Bᵇ} BS Γ e = ● ϵ
--     ListToSubst {B} {Bᵇ} BS Γ (cnsTy T Γ' L) = {!   !}
--     ListToSubst {B} {Bᵇ} BS Γ (cnsTm T t Γ' L) = {!   !}
 
   
--     BSystemToSubst : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ)
--         → (Γ : Ctxt B)
--         → (ListOfTerms Bᵇ Γ) ≡ Subst (BSystemToDepPoly BS) (CtxBToCtxP BS Γ) _ 
--     BSystemToSubst BS ε i = {!   !}
--     BSystemToSubst BS (T ⊳ Γ) i = {!   !}

-}


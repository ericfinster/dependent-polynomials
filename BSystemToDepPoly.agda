{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import BSystems

module BSystemToDepPoly where

    BSystemToTyStr : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → TyStr
    BSystemToTyStr {B} BS .Ty = TyTmStr.Typ B
    BSystemToTyStr {B} BS // x = BSystemToTyStr (BSystem.BSlc BS x)

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
            → (CtxToTyTmStr BS (Γ ++ Γ')) ≡ (CtxToTyTmStr (CtxToBSys BS Γ) ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i)))) Γ'))
    TyTmStr++Eq BS ϵ Γ' = cong (λ x → CtxToTyTmStr BS x) (EqHelp BS Γ')
    TyTmStr++Eq BS (T ► Γ) Γ' = TyTmStr++Eq (BSystem.BSlc BS T) Γ Γ'

    TerminalProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → B ↝ (CtxToTyTmStr BS Γ)
    TerminalProj {B} BS ϵ = idStr B
    TerminalProj {Bᵇ = Bᵇ} BS (T ► Γ) = (TerminalProj (BSystem.BSlc BS T) Γ) ○ (PreBSystem.wk Bᵇ T)

    TerminalProjComp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → transport (λ i → (B ↝ (TyTmStr++Eq BS Γ Γ' i))) (TerminalProj BS (Γ ++ Γ')) ≡
                (TerminalProj (CtxToBSys BS Γ) ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i)))) Γ')) ○ (TerminalProj BS Γ)
    TerminalProjComp BS ϵ Γ' = {!   !}
    TerminalProjComp BS (T ► Γ) Γ' = {! TerminalProjComp (BSystem.BSlc BS T) Γ Γ'  !}

    -- transport (λ i → (B ↝ (TyTmStr++Eq BS Γ Γ' i))) (TerminalProj BS (Γ ++ Γ')) ≡


    -- cong (λ x → (CtxToTyTmStr BS x)) (++-unit-left Γ)

    EqStep : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
            → ⌈ (CtxSliceBSys BS Γ T) ⌉ ≡ ⌈ (DropCtx BS T (CtxSliceBSys BS Γ T)) ⌉
    EqStep BS Γ T = refl
{-
    ActualEq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
            → ⌈ Γ ⌉ ≡ ⌈ (CtxSliceBSys BS Γ T) ⌉
    ActualEq {B} {Bᵇ} BS ϵ T t = {!   !} -- filling this hole is impossible for an arbitrary BSystem, otherwise they would all be stationary
    ActualEq {B} {Bᵇ} BS (T₁ ► Γ) T t = {!   !}
-}
    -- the fact that the equality above is impossible tells us that CtxSliceBSys is the wrong context


    postulate
        -- doesn't exist
        NeededEqSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
                → ⌈ Γ ⌉ ≡ ⌈ (CtxSliceBSys BS Γ T) ⌉ 

    NeededSubst : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
                → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr BS Γ))
    NeededSubst BS Γ T t = (PreBSystem.sub (CtxToPreSys BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T) t) ○ _↝_.Slc↝ (TerminalProj BS Γ) T

    NeededSubstGen : {A B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
            (f : B ↝ (CtxToTyTmStr AS Γ)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T))
            → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ))
    NeededSubstGen AS BS Γ f T t = (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ (_↝_.Slc↝ f T)
{-
        -- this is enough because of ⌈_⌉BSysEqual
    MorphismFix : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr BS Γ))
                → (P : (DepPoly (BSystemToTyStr (BSystem.BSlc BS T)) (BSystemToTyStr (BSystem.BSlc BS T))))
                → ((DepPoly (BSystemToTyStr (CtxToBSys BS Γ)) (BSystemToTyStr (BSystem.BSlc BS T))))
    MorphismFix BS Γ T f P .Tm x x₁ = {! NeededSubst BS Γ T t  !}
    MorphismFix BS Γ T f P .⇑ {x} {T'} t = {!    !}
-}

        -- TerminalProj (CtxToBSys BS Γ) x 
        -- transport (λ i → (DepPoly (⌈ _⌉BSysEqual (CtxToBSys BS Γ) x (~ i)) (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))))
    -- (MorphismFix (CtxToBSys BS Γ) x (_↝_.Ty↝ (NeededSubst BS Γ T t) T') t₁)
    -- _↝_.Ty↝ (NeededSubst BS Γ T t) x₁ 
    

    -- If I have time I could turn the function used in the lift into a seperate agda function for readablity
    {-# TERMINATING #-}
    BSystemToDepPolyHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
                (T : TyTmStr.Typ B) (f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ)) 
                → (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr (BSystem.BSlc BS T)))
    BSystemToDepPolyHelp AS BS Γ T f .Tm x x₁ = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) 
        x) (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) x ○ f) x₁)
    BSystemToDepPolyHelp {Aᵇ = Aᵇ} AS BS Γ T f .⇑ {x} {T'} t = transport (λ i → DepPoly (⌈_⌉BSysEqual (CtxToBSys AS Γ) x (~ i)) 
        (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T')))
        (BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T) x T'
        ((PreBSystem.sub (CtxToPreSys (CtxToBSys AS Γ) x) 
        (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) x)
        (_↝_.Ty↝ f T')) t)
        ○ (_↝_.Slc↝ ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T')))
    
    BSystemToDepPoly : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (DepPoly (BSystemToTyStr BS) (BSystemToTyStr BS))
    BSystemToDepPoly BS .Tm Γ x₁ = TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) x₁)
    BSystemToDepPoly BS .⇑ {Γ} {T} t = transport (λ i → (DepPoly (⌈_⌉BSysEqual BS Γ (~ i)) (BSystemToTyStr (BSystem.BSlc BS T)))) (BSystemToDepPolyHelp BS BS Γ T (NeededSubst BS Γ T t))
    

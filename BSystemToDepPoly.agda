

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

    TerminalProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → B ↝ (CtxToTyTmStr BS Γ)
    TerminalProj {B} BS ϵ = idStr B
    TerminalProj {Bᵇ = Bᵇ} BS (T ► Γ) = (TerminalProj (BSystem.BSlc BS T) Γ) ○ (PreBSystem.wk Bᵇ T)

    ⌈_⌉BSysEqual : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
            → ⌈ Γ ⌉ ≡ (BSystemToTyStr (CtxToBSys BS Γ))
    ⌈_⌉BSysEqual BS ϵ = refl
    ⌈_⌉BSysEqual BS (T₁ ► Γ) = ⌈_⌉BSysEqual (BSystem.BSlc BS T₁) Γ

    EqStep : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
            → ⌈ (CtxSliceBSys BS Γ T) ⌉ ≡ ⌈ (DropCtx BS T (CtxSliceBSys BS Γ T)) ⌉
    EqStep BS Γ T = refl

    ActualEq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
            → ⌈ Γ ⌉ ≡ ⌈ (CtxSliceBSys BS Γ T) ⌉
    ActualEq {B} {Bᵇ} BS ϵ T t = {!   !} -- filling this hole is impossible for an arbitrary BSystem, otherwise they would all be stationary
    ActualEq {B} {Bᵇ} BS (T₁ ► Γ) T t = {!   !}

    -- the fact that the equality above is impossible tells us that CtxSliceBSys is the wrong context


    postulate
        -- doesn't exist
        NeededEqSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
                → ⌈ Γ ⌉ ≡ ⌈ (CtxSliceBSys BS Γ T) ⌉ 

    NeededSubst : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
                → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr BS Γ))
    NeededSubst BS Γ T t = (PreBSystem.sub (CtxToPreSys BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T) t) ○ _↝_.Slc↝ (TerminalProj BS Γ) T

        -- this is enough because of ⌈_⌉BSysEqual
    MorphismFix : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr BS Γ))
                → (P : (DepPoly (BSystemToTyStr (BSystem.BSlc BS T)) (BSystemToTyStr (BSystem.BSlc BS T))))
                → ((DepPoly (BSystemToTyStr (CtxToBSys BS Γ)) (BSystemToTyStr (BSystem.BSlc BS T))))
    MorphismFix BS Γ T f P .Tm x x₁ = {! NeededSubst BS Γ T t  !}
    MorphismFix BS Γ T f P .⇑ {x} {T'} t = {!    !}

        -- TerminalProj (CtxToBSys BS Γ) x 
        -- transport (λ i → (DepPoly (⌈ _⌉BSysEqual (CtxToBSys BS Γ) x (~ i)) (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))))
    -- (MorphismFix (CtxToBSys BS Γ) x (_↝_.Ty↝ (NeededSubst BS Γ T t) T') t₁)
    -- _↝_.Ty↝ (NeededSubst BS Γ T t) x₁ 

    {-# TERMINATING #-}
    BSystemToDepPoly : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (DepPoly (BSystemToTyStr BS) (BSystemToTyStr BS))
    BSystemToDepPoly {B} BS .Tm Γ x₁ = TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) x₁) -- im not sure that this is correct
    BSystemToDepPoly {B} BS .⇑ {Γ} {T} t .Tm x x₁ = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys BS Γ) ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i)))) x)) 
                (_↝_.Ty↝ ((TerminalProj (CtxToBSys BS Γ) ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i)))) x)) ○ (NeededSubst BS Γ T t)) x₁)
    BSystemToDepPoly BS .⇑ {Γ} {T} t .⇑ = {!   !}

        --  (_↝_.Ty↝ ((TerminalProj (CtxToBSys BS Γ) ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i)))) x)) ○ (NeededSubst BS Γ T t)) x₁)
    -- (TerminalProj (CtxToBSys BS Γ) x) ○ (NeededSubst BS Γ T t)

  --   TyTmStr.Tm↝ (TyTmStr.Tm B x₁)
  -- transport (λ i → (DepPoly (NeededEqSys BS Γ T t (~ i)) (BSystemToTyStr (BSystem.BSlc BS T)))) (⌈_⌉s {M = (BSystemToDepPoly (BSystem.BSlc BS T))} (● (CtxSliceBSys BS Γ T)))
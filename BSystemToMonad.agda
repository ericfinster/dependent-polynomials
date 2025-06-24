open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import TyStr
open import DepPoly
open import Monad
open import BSystems
open import BSystemToDepPoly

module BSystemToMonad where
    postulate

        AppSubst : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
                (T : TyTmStr.Typ B) (f : B ↝ (CtxToTyTmStr AS Γ))
                (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))) (Δ' :  Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
                (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T))
                (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ T (NeededSubstGen AS BS Γ f T t)) Γ' Δ')
                → TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ ((TerminalProj (CtxToBSys AS Γ) Γ') ○ f) T)
    -- TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ')

    AppSubst2 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
        (fst₁ : Ctx (BSystemToTyStr BS)) (fst₂ : Subst (BSystemToDepPoly BS) Γ fst₁) 
        (snd₁ : TyTmStr.Tm (CtxToTyTmStr BS fst₁) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
        → (TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
    AppSubst2 {B} {Bᵇ} BS Γ T fst₁ (● .Γ) snd₁ = {! _↝_.Tm↝ (TerminalProj BS Γ) T snd₁ !}
    AppSubst2 {B} {Bᵇ} BS Γ T fst₁ (cns Γ₁ T₁ t Γ' Δ' fst₂) snd₁ = {! 
       transport (TerminalProjComp BS Γ₁ Γ') (TerminalProj BS (Γ₁ ++ Γ')) !}

    -- AppSubst (CtxToBSys BS Γ₁) BS ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ') T₁
    -- ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ')

    BSystemToMonad-μ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (BSystemToDepPoly BS ⊚ BSystemToDepPoly BS ⇒ BSystemToDepPoly BS)
    BSystemToMonad-μ BS .Tm⇒ (fst₁ , fst₂ , snd₁) = {!   !}
    BSystemToMonad-μ BS .⇑⇒ = {!   !}
{-
    NeededSubstVar : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ)
            (T : TyTmStr.Typ B) (T' : (TyTmStr.Typ (TyTmStr.Slc B T)))
            → (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T') ≡ T'
    NeededSubstVar BS T T' = {!  (λ i → ((_↝_.Ty↝ (BSystem.sub-of-wk-Typ BS T i)) T')) !}

    BSystemToMonad-ηHelp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ)
            (T : TyTmStr.Typ B)  
            → IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
                (BSystemToDepPolyHelp BS BS (T ► ϵ) T
                (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
    BSystemToMonad-ηHelp {Bᵇ = Bᵇ} BS T .Tm⇒ {Γ'} {T'} (idT _) = {! PreBSystem.var (PreBSystem.slc Bᵇ T) T' !}
    BSystemToMonad-ηHelp BS T .⇑⇒ {Γ} {T'} (idT _) = {! BSystemToMonad-ηHelp (BSystem.BSlc BS T) T'  !}
-}
    -- transport
    --            (λ i →
    --            DepPoly (BSystemToTyStr (BSystem.BSlc BS T))
    --            (BSystemToTyStr (BSystem.BSlc BS T)))

    -- PreBSystem.var (PreBSystem.slc Bᵇ T) T' 

    EqTestSub : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (T' T'' : (TyTmStr.Typ (TyTmStr.Slc B T)))
            → (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) ≡ idStr (TyTmStr.Slc B T)
    EqTestSub BS T T' T'' = {! BSystem.sub-of-wk-Typ BS T  !} -- this is the right solution but I don't know hoe to reduce it

    EqTestTM : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (T' T'' : (TyTmStr.Typ (TyTmStr.Slc B T)))
        → (DepPoly.Tm ((BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))) (T' ► ϵ) T'')
            ≡ (DepPoly.Tm (BSystemToDepPoly (BSystem.BSlc BS T)) (T' ► ϵ) T'')
    EqTestTM BS T T' T'' = {!   !} -- this could be transported along EqTestSub and be done but I don't know how to project the morphism parts out of the path

    EqTest⇑ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (T' T'' : (TyTmStr.Typ (TyTmStr.Slc B T)))
        (t : (DepPoly.Tm ((BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))) (T' ► ϵ) T''))
        → (DepPoly.⇑ (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))) {T' ► ϵ} {T''} t
            ≡ DepPoly.⇑ (BSystemToDepPoly (BSystem.BSlc BS T)) {T' ► ϵ} (Iso.fun (pathToIso (EqTestTM BS T T' T'')) t))
    EqTest⇑ BS T T' T'' t = {!   !} -- looking at the goal type this should work by using that IdStr is neutal and using EqTestSub
  
    EqTest : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → ((BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))))
                ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    EqTest BS T = {!   !} -- this should be buildable by the structure above 

    BSystemToMonad-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) 
        → IdPoly (BSystemToTyStr BS) ⇒ BSystemToDepPoly BS
    BSystemToMonad-η {Bᵇ = Bᵇ} BS .Tm⇒ {Γ} {T} (idT .T) = PreBSystem.var Bᵇ T
    BSystemToMonad-η BS .⇑⇒ {Γ} {T} (idT _) = {! transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (EqTest BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T))  !} 
 -- transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (EqTest BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)) 
 -- should work for eta, but there is a constant transport in the goal type confusing me
    -- (BSystemToMonad-η (BSystem.BSlc BS T))
    

    BSystemToMonad : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (Monad (BSystemToTyStr BS))
    BSystemToMonad BS .Monad.P = BSystemToDepPoly BS
    BSystemToMonad BS .Monad.μ = {!   !}
    BSystemToMonad {Bᵇ = Bᵇ} BS .Monad.η = BSystemToMonad-η BS

     -- _↝_.Tm↝ (TerminalProj BS Γ) T snd₁
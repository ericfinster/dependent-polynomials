{-# OPTIONS --verbose=term:5 #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import TyStr
open import DepPoly
open import Monad
open import BSystems
open import BSystemToDepPoly
open import ConvertingSubstitutions

module BSystemToMonad where

    -- Eq3Help : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ)(T : TyTmStr.Typ B) (fst₁ : Ctx (BSystemToTyStr BS)) (Γ : Ctx (BSystemToTyStr BS)) 
    --      (fst₂ : Subst (BSystemToDepPoly BS) Γ fst₁)
    --      → {! (CtxToBSys BS fst₁) () (SubstToHom fst₂)   !}

        -- this should be justified by the naturality of sub
    Eq3 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (fst₁ : Ctx (BSystemToTyStr BS)) (Γ : Ctx (BSystemToTyStr BS)) 
         (fst₂ : Subst (BSystemToDepPoly BS) Γ fst₁)
         → ((SubstToHom fst₂) ○ (TerminalProj BS fst₁)) ≡ (TerminalProj BS Γ) 
    Eq3 {Bᵇ = Bᵇ} BS fst₁ Γ (● .Γ) = IdStrRN (wkCtxt Bᵇ (CtxPToCtxB BS Γ))
    Eq3 BS fst₁ Γ (cns Γ₁ T t Γ' Δ' fst₂) = {!   !}
        

    -- BSystemToMonad-μHelp : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} ()

    BSystemToMonad-μ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (BSystemToDepPoly BS ⊚ BSystemToDepPoly BS ⇒ BSystemToDepPoly BS)
    BSystemToMonad-μ BS .Tm⇒ {Γ} {T} (fst₁ , fst₂ , snd₁) = transport (λ i → (TyTmStr.Tm (TopTyTm (CtxPToCtxB BS Γ)) (_↝_.Ty↝ (Eq3 BS fst₁ Γ fst₂ i) T))) (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)
    BSystemToMonad-μ BS .⇑⇒ (fst₁ , fst₂ , snd₁) = {!   !}
    -- needs Basically BSystemToMonad for two BSystemToDepPolyHelp with codomain1 matching domain2
    -- it seems like agda wont reduce ⌈ fst₂ ⌉s to something which basically equals a repeated application of BSystemToDepPolyHelp which would make the help function kind of more involved


    --  (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)
    -- _↝_.Tm↝ (SubstToHom fst₂) (transport (λ i → TyTmStr.Typ (Eq1 BS fst₁ i)) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
    -- (transport (λ i → TyTmStr.Typ (Eq1 BS fst₁ i)) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
    -- transport (λ i → Ctxt (Eq1 BS fst₁ i))
    -- (_↝_.Ty↝ (TerminalProj BS fst₁) T)
{-

    this is all written to work without the rewrite

    !!! The η definition needs to be reworked since I simplified BSystemToDepPolyHelp to take the already sliced BSystem and not the original BSystem and a type !!!
    !!! This hopeully simplifies μ but probably implies one needs to rework some of the equalities !!!

    -- -- -- Definition of η

    EqTerProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → (TerminalProj BS (T ► ϵ)) ≡ (PreBSystem.wk Bᵇ T)
    EqTerProj {B} {Bᵇ} BS T = IdStrLN (PreBSystem.wk Bᵇ T)
 
    -- This needs one of the BSystem equalities, so we need BSystems to arrive at Monads

    NeededSubstIsID : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))
            ≡ (idStr (TyTmStr.Slc B T))
    NeededSubstIsID {B} {Bᵇ} BS T = 
            (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))
        ≡⟨ refl ⟩
            PreBSystem.sub (CtxToPreSys BS (T ► ϵ))
            (_↝_.Ty↝ (TerminalProj BS (T ► ϵ)) T) (PreBSystem.var Bᵇ T)
            ○ _↝_.Slc↝ (TerminalProj BS (T ► ϵ)) T
        ≡⟨ cong (λ x → 
                (PreBSystem.sub (CtxToPreSys BS (T ► ϵ)) 
                (_↝_.Ty↝ (TerminalProj BS (T ► ϵ)) T) (PreBSystem.var Bᵇ T) 
                ○ x)) 
                (proj-slc (TerminalProj BS (T ► ϵ)) (PreBSystem.wk Bᵇ T) (EqTerProj BS T) T) ⟩
            PreBSystem.sub (CtxToPreSys BS (T ► ϵ))
            (_↝_.Ty↝ (TerminalProj BS (T ► ϵ)) T) (PreBSystem.var Bᵇ T)
            ○ _↝_.Slc↝ (PreBSystem.wk Bᵇ T) T
        ≡⟨ cong (λ x → 
                PreBSystem.sub (CtxToPreSys BS (T ► ϵ))
                (_↝_.Ty↝ (TerminalProj BS (T ► ϵ)) T) (PreBSystem.var Bᵇ T)
                ○ _↝_.Slc↝ (PreBSystem.wk Bᵇ T) T) (EqTerProj BS T) ⟩
            PreBSystem.sub (CtxToPreSys BS (T ► ϵ))
            (_↝_.Ty↝ (PreBSystem.wk Bᵇ T) T) (PreBSystem.var Bᵇ T)
            ○ _↝_.Slc↝ (PreBSystem.wk Bᵇ T) T
        ≡⟨ BSystem.sub-of-wk-Typ BS T ⟩
            idStr (TyTmStr.Slc B T)
        ∎ 

    -- in DepPolyHelpIsTrivialStep, when lifiting the polynomials we get on both sides a ToDepPolyHelp so it suffices to show that the morphism is equal 
    -- since all other parameters are allready equal, so DepPolyHelpIsTrivialHom completes that proof

    DepPolyHelpIsTrivialHom : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (Γ : Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
                (T' : TyTmStr.Typ (TyTmStr.Slc B T)) (t : (TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T')))
            → (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t
            ○ (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T' ○ idStr (TyTmStr.Slc (TyTmStr.Slc B T) T')))
            ≡ (NeededSubst (BSystem.BSlc BS T) Γ T' t)
    DepPolyHelpIsTrivialHom {B} {Bᵇ} BS T Γ T' t = (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t
            ○ (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T' ○ idStr (TyTmStr.Slc (TyTmStr.Slc B T) T')))
        ≡⟨ cong (λ x → (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t ○ x))
            (IdStrRN (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T')) ⟩
            (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t
            ○ (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T'))
        ≡⟨ refl ⟩
            (NeededSubst (BSystem.BSlc BS T) Γ T' t)
        ∎
   
    -- needed since the difference in function used (ToDepPolyHelp vs ToDepPoly) needs to show an actual equality between polynomials 
    -- and can't just be handled by cong or something simillar
    -- IdStr can be used since we have NeededSubstIsId
    DepPolyHelpIsTrivialStep : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → (BSystemToDepPolyHelp BS BS (T ► ϵ) T (idStr (TyTmStr.Slc B T)))
            ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    DepPolyHelpIsTrivialStep BS T i .Tm x x₁ = refl {x = TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) x) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) x) x₁)} i
    DepPolyHelpIsTrivialStep BS T i .⇑ {Γ} {T'} t = cong (λ x → transport (λ i₁ →
            DepPoly (⌈ BSystem.BSlc BS T ⌉BSysEqual Γ (~ i₁)) (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T')))
            (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T) Γ T' x)) (DepPolyHelpIsTrivialHom BS T Γ T' t ) i


    -- This is the central equality since we can then reduce DepPolyHelp to BSystemToDepPoly BS and recursively apply BSystemToMonad-η

    DepPolyHelpIsTrivial : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
                ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    DepPolyHelpIsTrivial {B} {Bᵇ} BS T = (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
        ≡⟨ cong (λ x → BSystemToDepPolyHelp BS BS (T ► ϵ) T x) (NeededSubstIsID BS T) ⟩
            (BSystemToDepPolyHelp BS BS (T ► ϵ) T (idStr (TyTmStr.Slc B T)))
        ≡⟨ DepPolyHelpIsTrivialStep BS T ⟩      
            BSystemToDepPoly (BSystem.BSlc BS T)
        ∎ 


    -- needed to get rid of the constant transport introduced by BSystemToDepPolyHelp
    Eq-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
            transport (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc BS T)) (BSystemToTyStr (BSystem.BSlc BS T)))
            (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
        ≡ IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
            BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))
    Eq-η {Bᵇ = Bᵇ} BS T = cong (λ x → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒ x)) 
        (transportRefl (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))))


    {-# TERMINATING #-}
    BSystemToMonad-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) 
        → IdPoly (BSystemToTyStr BS) ⇒ BSystemToDepPoly BS
    BSystemToMonad-η {Bᵇ = Bᵇ} BS .Tm⇒ {Γ} {T} (idT .T) = PreBSystem.var Bᵇ T
    BSystemToMonad-η BS .⇑⇒ {Γ} {T} (idT _) = (Iso.fun (pathToIso (sym (Eq-η BS T))))     
        (transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (DepPolyHelpIsTrivial BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)))
-}

    BSystemToMonad : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (Monad (BSystemToTyStr BS))
    BSystemToMonad BS .Monad.P = BSystemToDepPoly BS
    BSystemToMonad BS .Monad.μ = BSystemToMonad-μ BS
    BSystemToMonad {Bᵇ = Bᵇ} BS .Monad.η = {!   !}

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
{-
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
    AppSubst2 {B} {Bᵇ} BS Γ T fst₁ (cns Γ₁ T₁ t Γ' Δ' fst₂) snd₁ = {!    !}

    -- AppSubst (CtxToBSys BS Γ₁) BS ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ') T₁
    -- ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ')

    BSystemToMonad-μHelp : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C}
       (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ)
       (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))) 
       (Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS t)))
       (t : TyTmStr.Tm somewhere)
       (P : DepPoly i dont know where) 
       (ɣ : Subst (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr (BSystem.BSlc BS t))) Γ' Δ')
       → (⌈ ɣ ⌉s ⊚ DepPoly.⇑ P t)
    BSystemToMonad-μHelp = ?


    BSystemToMonad-μ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (BSystemToDepPoly BS ⊚ BSystemToDepPoly BS ⇒ BSystemToDepPoly BS)
    BSystemToMonad-μ BS .Tm⇒ (fst₁ , fst₂ , snd₁) = {!  !}
    BSystemToMonad-μ BS .⇑⇒ = {!   !}
-}

    EqTerProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → (TerminalProj BS (T ► ϵ)) ≡ (PreBSystem.wk Bᵇ T)
    EqTerProj {B} {Bᵇ} BS T = IdStrLN (PreBSystem.wk Bᵇ T)

    EqSub : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))
            ≡ (idStr (TyTmStr.Slc B T))
    EqSub {B} {Bᵇ} BS T = 
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

    EqTestTM : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (Γ : Ctx (BSystemToTyStr (BSystem.BSlc BS T))) (T' : (TyTmStr.Typ (TyTmStr.Slc B T)))
        → (DepPoly.Tm ((BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))) Γ T')
            ≡ (DepPoly.Tm (BSystemToDepPoly (BSystem.BSlc BS T)) Γ T')
    EqTestTM {B} {Bᵇ} BS T Γ T' = TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) Γ)
            (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ)
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T'))
        ≡⟨ cong (λ x → 
                TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) Γ)
                (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ)
                (_↝_.Ty↝ x T'))) 
                (EqSub BS T)⟩
            TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) Γ)
            (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T')
        ∎
       
    EqTest⇑ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (Γ : Ctx (BSystemToTyStr (BSystem.BSlc BS T))) (T' : (TyTmStr.Typ (TyTmStr.Slc B T)))
        → PathP (λ i → (EqTestTM BS T Γ T' i) → DepPoly ⌈ Γ ⌉ (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T')))
            (DepPoly.⇑ (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))) 
            (DepPoly.⇑ (BSystemToDepPoly (BSystem.BSlc BS T))) 
    EqTest⇑ BS T Γ T' i x .Tm x₁ x₂ = {! DepPoly.⇑ (BSystemToDepPoly (BSystem.BSlc BS T)) x  !}
    EqTest⇑ BS T Γ T' i x .⇑ t = {!   !}

    -- PathP (λ i → (EqTestTM BS T Γ T' i) → DepPoly ⌈ Γ ⌉ (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))
    -- (DepPoly.⇑ (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))))

{-
    -- This needs to be a PathP itself
    EqTest⇑ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (T' T'' : (TyTmStr.Typ (TyTmStr.Slc B T)))
        (t : (DepPoly.Tm ((BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))) (T' ► ϵ) T''))
        → (DepPoly.⇑ (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))) {T' ► ϵ} {T''} t
            ≡ DepPoly.⇑ (BSystemToDepPoly (BSystem.BSlc BS T)) {T' ► ϵ} (Iso.fun (pathToIso (EqTestTM BS T T' T'')) t))
    EqTest⇑ {B} {Bᵇ} BS T T' T'' t = {! 
            DepPoly.⇑ (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))) {T' ► ϵ} {T''} t
        ≡⟨ refl ⟩
            transport
            (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))
            (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'')))
            (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T)
            (T' ► ϵ) T''
            (PreBSystem.sub (PreBSystem.slc (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T''))
            t
            ○
            ((idStr
            (TyTmStr.Slc (TyTmStr.Slc (TyTmStr.Slc B T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T'')))
            ○
            _↝_.Slc↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T''))
            ○ _↝_.Slc↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T'')))
        ≡⟨ cong (λ x → transport
            (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))
            (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'')))
            (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T)
            (T' ► ϵ) T''
            (PreBSystem.sub (PreBSystem.slc (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T''))
            t
            ○ x))) (IdStrLN ((_↝_.Slc↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T''))
            ○ _↝_.Slc↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T'')) ⟩ -- can be done using idLN
            transport
            (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))
            (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'')))
            (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T)
            (T' ► ϵ) T''
            (PreBSystem.sub (PreBSystem.slc (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T''))
            t
            ○
            ((_↝_.Slc↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T''))
            ○ _↝_.Slc↝ (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)) T'')))
        ≡⟨ ? ⟩
            transport
            (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))
            (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'')))
            (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T)
            (T' ► ϵ) T''
            (PreBSystem.sub (PreBSystem.slc (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (idStr (TyTmStr.Slc B T)) T''))
            (Iso.fun (pathToIso (EqTestTM BS T T' T'')) t)
            ○
            ((_↝_.Slc↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (idStr (TyTmStr.Slc B T)) T''))
            ○ _↝_.Slc↝ (idStr (TyTmStr.Slc B T)) T'')))
        ≡⟨ ? ⟩
            transport
            (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'))
            (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T'')))
            (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T)
            (T' ► ϵ) T''
            (PreBSystem.sub (PreBSystem.slc (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (idStr (TyTmStr.Slc B T)) T''))
            (Iso.fun (pathToIso (EqTestTM BS T T' T'')) t)
            ○
            ((idStr
            (TyTmStr.Slc (TyTmStr.Slc (TyTmStr.Slc B T) T')
            (_↝_.Ty↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (idStr (TyTmStr.Slc B T)) T'')))
            ○
            _↝_.Slc↝ (PreBSystem.wk (PreBSystem.slc Bᵇ T) T')
            (_↝_.Ty↝ (idStr (TyTmStr.Slc B T)) T''))
            ○ _↝_.Slc↝ (idStr (TyTmStr.Slc B T)) T'')))
            ∎
           !} -- looking at the goal type this should work by using that IdStr is neutal and using EqTestSub
  
-} 

    EqTest : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → ((BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))))
                ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    EqTest BS T = DepPoly-≡-intro (EqTestTM BS T) (EqTest⇑ BS T) 

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
         (transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (EqTest BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)))
    
    -- (transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (EqTest BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T))) 
 -- transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (EqTest BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)) 
 -- should work for eta, but there is a constant transport in the goal type confusing me
    

    BSystemToMonad : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (Monad (BSystemToTyStr BS))
    BSystemToMonad BS .Monad.P = BSystemToDepPoly BS
    BSystemToMonad BS .Monad.μ = {!   !}
    BSystemToMonad {Bᵇ = Bᵇ} BS .Monad.η = BSystemToMonad-η BS

     -- _↝_.Tm↝ (TerminalProj BS Γ) T snd₁
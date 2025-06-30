open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import TyStr
open import DepPoly
open import Monad
open import BSystems
open import BSystemToDepPoly

module BSystemToMonad where

{-
    -- this probably needs to be a PathP
    checkEq2 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS))
            (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
            (Γ' : (Ctx ⌈ Γ ⌉)) (Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
            → PathP (λ i → )
            (Subst (BSystemToDepPolyHelp BS BS Γ T
            (NeededSubst BS Γ T t))
            (transport (λ i → Ctx (⌈ BS ⌉BSysEqual Γ i)) Γ') Δ')
            (Subst (transport (λ i → DepPoly (⌈ BS ⌉BSysEqual Γ (~ i)))
           (BSystemToTyStr (BSystem.BSlc BS T))) (BSystemToDepPolyHelp BS BS Γ T (NeededSubst BS Γ T t))) Γ' Δ'
    checkEq2 BS Γ T t Γ' Δ' = {!   !}
-}

    CheckEq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS))
            (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
            (Γ' : (Ctx ⌈ Γ ⌉)) (Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
            → (Subst
            (BSystemToDepPolyHelp BS BS Γ T (NeededSubstGen BS BS Γ (TerminalProj BS Γ) T t))
            (transport (λ i → Ctx (⌈ BS ⌉BSysEqual Γ i)) Γ') Δ')
            ≡ Subst (transport (λ i → DepPoly (⌈ BS ⌉BSysEqual Γ (~ i))
           (BSystemToTyStr (BSystem.BSlc BS T))) (BSystemToDepPolyHelp BS BS Γ T (NeededSubst BS Γ T t))) Γ' Δ'
    CheckEq BS Γ T t Γ' Δ' = {! 
            Subst (BSystemToDepPolyHelp BS BS Γ T
            (NeededSubstGen BS BS Γ (TerminalProj BS Γ) T t))
            (transport (λ i → Ctx (⌈ BS ⌉BSysEqual Γ i)) Γ') Δ'
        ≡⟨ refl ⟩
            Subst (BSystemToDepPolyHelp BS BS Γ T
            (NeededSubst BS Γ T t))
            (transport (λ i → Ctx (⌈ BS ⌉BSysEqual Γ i)) Γ') Δ'
        ∎
          !}

    AppSubst : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
            (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
            (T : TyTmStr.Typ B) (f : B ↝ (CtxToTyTmStr AS Γ))
            (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))) (Δ' :  Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
            (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T))
            (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ T (NeededSubstGen AS BS Γ f T t)) Γ' Δ')
            → TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ ((TerminalProj (CtxToBSys AS Γ) Γ') ○ f) T)
    AppSubst AS BS Γ T f Γ' Δ' t (● .Γ') = _↝_.Tm↝ (TerminalProj (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ f T) t
    AppSubst AS BS Γ T f Γ' Δ' t (cns Γ₁ T₁ t₁ Γ'' Δ'' ɣ) = {! AppSubst (CtxToBSys AS Γ) (BSystem.BSlc BS T) Γ₁ T₁ 
        ((TerminalProj (CtxToBSys AS Γ) Γ₁) ○ (NeededSubstGen AS BS Γ f T t)) Γ'' Δ'' t₁ ɣ  !}
        -- this probably needs a bit more transport in the end 
        -- these both (AppSubst and AppSubst2) have the same problem, the substitutions are typed wrong, should be solvable by transporting in the right way
 
    -- TerminalProj (CtxToBSys AS Γ)
    --  ○ (NeededSubstGen AS BS Γ f T t)
    -- AppSubst (CtxToBSys AS Γ) (BSystem.BSlc BS T) Γ₁ T₁-
    -- NeededSubstGen AS BS Γ f

    AppSubst2Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
        (Γ' : Ctx (BSystemToTyStr (CtxToBSys BS Γ))) (Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
        → TyTmStr.Tm (CtxToTyTmStr BS (Γ ++ Γ')) (_↝_.Ty↝ (TerminalProj BS (Γ ++ Γ')) T)
        ≡ TyTmStr.Tm (CtxToTyTmStr (CtxToBSys BS Γ) Γ') (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Γ) Γ') (_↝_.Ty↝ (TerminalProj BS Γ) T))
    AppSubst2Eq BS Γ T Γ' Δ' = {! 
            TyTmStr.Tm (CtxToTyTmStr BS (Γ ++ Γ')) (_↝_.Ty↝ (TerminalProj BS (Γ ++ Γ')) T)
        ≡⟨ ? ⟩
            TyTmStr.Tm (CtxToTyTmStr (CtxToBSys BS Γ) Γ') (_↝_.Ty↝ (TerminalProj BS (Γ ++ Γ')) T) 
        ∎     !}

    AppSubst2 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
        (fst₁ : Ctx (BSystemToTyStr BS)) (fst₂ : Subst (BSystemToDepPoly BS) Γ fst₁) 
        (snd₁ : TyTmStr.Tm (CtxToTyTmStr BS fst₁) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
        → (TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
    AppSubst2 {B} {Bᵇ} BS Γ T fst₁ (● .Γ) snd₁ = _↝_.Tm↝ (TerminalProj BS Γ) T snd₁
    AppSubst2 {B} {Bᵇ} BS Γ T fst₁ (cns Γ₁ T₁ t Γ' Δ' fst₂) snd₁ = {! AppSubst BS BS Γ₁ T₁ (TerminalProj BS Γ₁) Γ' Δ' t fst₂ !}
    
    -- AppSubst BS BS Γ₁ T₁ (TerminalProj BS Γ₁) ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ') Δ' t 
    -- AppSubst (CtxToBSys BS Γ₁) BS ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ') T₁
    -- ((transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ₁ i)))) Γ')
{-
    BSystemToMonad-μHelp : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C}
       (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ)
       (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))) 
       (Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS t)))
       (t : TyTmStr.Tm somewhere)
       (P : DepPoly i dont know where) 
       (ɣ : Subst (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr (BSystem.BSlc BS t))) Γ' Δ')
       → (⌈ ɣ ⌉s ⊚ DepPoly.⇑ P t)
    BSystemToMonad-μHelp = ?

-}


    BSystemToMonad-μ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (BSystemToDepPoly BS ⊚ BSystemToDepPoly BS ⇒ BSystemToDepPoly BS)
    BSystemToMonad-μ BS .Tm⇒ {Γ} {T} (fst₁ , fst₂ , snd₁) = AppSubst2 BS Γ T fst₁ fst₂ snd₁
    BSystemToMonad-μ BS .⇑⇒ (fst₁ , fst₂ , snd₁) = {!   !}

    -- Definition of η
    EqTerProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → (TerminalProj BS (T ► ϵ)) ≡ (PreBSystem.wk Bᵇ T)
    EqTerProj {B} {Bᵇ} BS T = IdStrLN (PreBSystem.wk Bᵇ T)

    -- This needs actual BSystems
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

    EqTest5 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (Γ : Ctx (BSystemToTyStr (BSystem.BSlc BS T)))
                (T' : TyTmStr.Typ (TyTmStr.Slc B T)) (t : (TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T')))
            → (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t
            ○ (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T' ○ idStr (TyTmStr.Slc (TyTmStr.Slc B T) T')))
            ≡ (NeededSubst (BSystem.BSlc BS T) Γ T' t)
    EqTest5 {B} {Bᵇ} BS T Γ T' t = (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t
            ○ (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T' ○ idStr (TyTmStr.Slc (TyTmStr.Slc B T) T')))
        ≡⟨ cong (λ x → (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t ○ x))
            (IdStrRN (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T')) ⟩
            (PreBSystem.sub (CtxToPreSys (BSystem.BSlc BS T) Γ) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) Γ) T') t
            ○ (_↝_.Slc↝ (TerminalProj (BSystem.BSlc BS T) Γ) T'))
        ≡⟨ refl ⟩
            (NeededSubst (BSystem.BSlc BS T) Γ T' t)
        ∎

    EqTest2 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → (BSystemToDepPolyHelp BS BS (T ► ϵ) T (idStr (TyTmStr.Slc B T)))
                ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    EqTest2 BS T i .Tm x x₁ = refl {x = TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) x) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) x) x₁)} i
    EqTest2 BS T i .⇑ {Γ} {T'} t = cong (λ x →  (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc BS T) Γ T' x)) (EqTest5 BS T Γ T' t ) i

    EqTest4 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
                ≡ (BSystemToDepPolyHelp BS BS (T ► ϵ) T (idStr (TyTmStr.Slc B T)))
    EqTest4 BS T = cong (λ x → BSystemToDepPolyHelp BS BS (T ► ϵ) T x) (EqSub BS T) 

    EqTest : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
                ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    EqTest {B} {Bᵇ} BS T = (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
        ≡⟨ EqTest4 BS T ⟩
            (BSystemToDepPolyHelp BS BS (T ► ϵ) T (idStr (TyTmStr.Slc B T)))
        ≡⟨ EqTest2 BS T ⟩      
            BSystemToDepPoly (BSystem.BSlc BS T)
        ∎ 
{-
    Eq-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
            transport (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc BS T)) (BSystemToTyStr (BSystem.BSlc BS T)))
            (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
        ≡ IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
            BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))
    Eq-η {Bᵇ = Bᵇ} BS T = cong (λ x → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒ x)) 
        (transportRefl (BSystemToDepPolyHelp BS BS (T ► ϵ) T (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))))
-}

    {-# TERMINATING #-}
    BSystemToMonad-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) 
        → IdPoly (BSystemToTyStr BS) ⇒ BSystemToDepPoly BS
    BSystemToMonad-η {Bᵇ = Bᵇ} BS .Tm⇒ {Γ} {T} (idT .T) = PreBSystem.var Bᵇ T
    BSystemToMonad-η BS .⇑⇒ {Γ} {T} (idT _) = (transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (EqTest BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)))

    BSystemToMonad : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (Monad (BSystemToTyStr BS))
    BSystemToMonad BS .Monad.P = BSystemToDepPoly BS
    BSystemToMonad BS .Monad.μ = {!  BS !}
    BSystemToMonad {Bᵇ = Bᵇ} BS .Monad.η = {!  BSystemToMonad-η BS !}
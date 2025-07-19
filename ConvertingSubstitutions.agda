open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import BSystems
open import BSystemToDepPoly

module ConvertingSubstitutions where

        -- -- -- Converting Substitutions
     
    -- gets way more complex without the rewrite
    SubstToHomHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                    {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                    {f : B ↝ (CtxToTyTmStr AS Γ)}
                    {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                    (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                    → (TopTyTm (CtxPToCtxB BS Δ')) ↝ (TopTyTm (CtxPToCtxB (CtxToBSys AS Γ) Γ'))
    SubstToHomHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● _) = (wkCtxt (CtxToPreSys AS Γ) (CtxPToCtxB (CtxToBSys AS Γ) Γ')) ○ f
    SubstToHomHelp {AS = AS} {BS = BS} {Γ = Γ} (cns Γ' T' t Γ'' Δ' ɣ) = transport (λ i → (TopTyTm (CtxPToCtxB (BSystem.BSlc BS T') Δ') ↝ (TopTyTm++BSys (CtxToBSys AS Γ) Γ' Γ'' i)))
                    (SubstToHomHelp ɣ)


    SubstToHom : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                    {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                    → (TopTyTm (CtxPToCtxB BS Δ)) ↝ (TopTyTm (CtxPToCtxB BS Γ))
    SubstToHom {Bᵇ = Bᵇ} {BS = BS} {Γ = Γ} (● Γ) = wkCtxt Bᵇ (CtxPToCtxB BS Γ)
    SubstToHom {BS = BS} (cns Γ T t Γ' Δ' ɣ) = transport (λ i → (TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ')) ↝ (TopTyTm++BSys BS Γ Γ' i)) (SubstToHomHelp ɣ)

    SubstToHomEqTm : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) 
                        (f : B ↝ A)
                        (Γ' : Ctx (BSystemToTyStr AS))
                        (x : Ctx (BSystemToTyStr (CtxToBSys AS Γ')))
                        (T : TyTmStr.Typ B)
                        → PathP (λ i → (TyTmStr.Tm (TyTmStr++Eq AS Γ' x i) (_↝_.Ty↝ (TerminalProjCompf AS Γ' x f i) T)) → (TyTmStr.Slc B T) ↝ (TyTmStr++Eq AS Γ' x i)) 
                            (λ t → ((NeededSubstGen AS BS (Γ' ++ x) (TerminalProj AS (Γ' ++ x) ○ f) T t))) 
                            (λ t → ((NeededSubstGen (CtxToBSys AS Γ') BS x (TerminalProj (CtxToBSys AS Γ') x ○ (wkCtxt Aᵇ (CtxPToCtxB AS Γ') ○ f)) T t)))
    SubstToHomEqTm AS BS f Γ' x T i x₁ = (PreBSystem.sub (PreSys++Eq AS Γ' x i) (_↝_.Ty↝ (TerminalProjCompf AS Γ' x f i) T) x₁) ○
                        (_↝_.Slc↝ (TerminalProjCompf AS Γ' x f i) T) 

    NeededSubstGenEq : {A B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) 
                (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx ⌈ Γ ⌉) (T : TyTmStr.Typ B)
                (T' : TyTmStr.Typ (TyTmStr.Slc B T))
                → PathP (λ i → (φ : (Ctx (++-ceil Γ Γ' i))) → (g : ((TyTmStr.Slc B T) ↝ (CtxToTyBSys++Eq AS Γ Γ' i φ))) 
                → (t' : TyTmStr.Tm (CtxToTyBSys++Eq AS Γ Γ' i φ) (_↝_.Ty↝ g T'))
                → ((TyTmStr.Slc (TyTmStr.Slc B T) T') ↝ (CtxToTyBSys++Eq AS Γ Γ' i φ))) 
                (λ φ g t' → (NeededSubstGen (CtxToBSys AS (Γ ++ Γ')) (BSystem.BSlc BS T) φ g T' t')) 
                λ φ g t' → NeededSubstGen (CtxToBSys (CtxToBSys AS Γ) Γ') (BSystem.BSlc BS T) φ g T' t'
    NeededSubstGenEq AS BS ϵ Γ' T T' = refl
    NeededSubstGenEq AS BS (T₁ ► Γ) Γ' T T' = NeededSubstGenEq (BSystem.BSlc AS T₁) BS Γ Γ' T T'

    SubstToHomEqHelpPoly :{A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ)  
                        (f : B ↝ A)
                        (Γ' : Ctx (BSystemToTyStr AS))
                        (x : Ctx (BSystemToTyStr (CtxToBSys AS Γ')))
                        (T : TyTmStr.Typ B)
                        → PathP (λ i → (TyTmStr.Tm (TyTmStr++Eq AS Γ' x i) (_↝_.Ty↝ (TerminalProjCompf AS Γ' x f i) T)) → DepPoly (++-ceil Γ' x i) (BSystemToTyStr (BSystem.BSlc BS T))) 
                            (λ t → (BSystemToDepPolyHelp AS (BSystem.BSlc BS T) (Γ' ++ x) (NeededSubstGen AS BS (Γ' ++ x) (TerminalProj AS(Γ' ++ x) ○ f) T t)))
                            λ t → (BSystemToDepPolyHelp (CtxToBSys AS Γ') (BSystem.BSlc BS T) x (NeededSubstGen (CtxToBSys AS Γ') BS x 
                            (TerminalProj (CtxToBSys AS Γ') x ○ (wkCtxt Aᵇ (CtxPToCtxB AS Γ') ○ f))T t))
    SubstToHomEqHelpPoly AS BS f Γ' x T i x₁ .Tm Γ'' T' = TyTmStr.Tm ((CtxToTyBSys++Eq AS Γ' x i) Γ'')
                        (_↝_.Ty↝ ((TerminalProjCeil AS Γ' x i Γ'') ○ (SubstToHomEqTm AS BS f Γ' x T i x₁)) T')
    SubstToHomEqHelpPoly AS BS f Γ' x T i x₁ .⇑ {Γ''} {T'} t = BSystemToDepPolyHelpEq AS (BSystem.BSlc (BSystem.BSlc BS T) T') Γ' x i Γ'' 
            (NeededSubstGenEq AS BS Γ' x T T' i Γ'' ((TerminalProjCeil AS Γ' x i Γ'') ○ (SubstToHomEqTm AS BS f Γ' x T i x₁)) t)

    -- (NeededSubstGenEq (CtxToBSys AS Γ) BS Γ' x T T' i Γ'' ((TerminalProjCeil (CtxToBSys AS Γ) Γ' x i Γ'') ○ (SubstToHomEqTm AS BS Γ f Γ' x T i x₁)) t) 
    -- ((TerminalProjCeil (CtxToBSys AS Γ) Γ' x i Γ'') ○ (SubstToHomEqTm AS BS Γ f Γ' x T i x₁))
    -- (SubstToHomEqTm AS BS Γ f Γ' x T i x₁)
    -- BSystemToDepPolyHelpEq (CtxToBSys AS Γ) (BSystem.BSlc (BSystem.BSlc BS T) T') Γ' x i Γ''
    -- (_↝_.Ty↝ (TerminalProjCeil (CtxToBSys AS Γ) Γ' x i Γ''))
    -- TyTmStr.Tm ((CtxToTyBSys++Eq (CtxToBSys AS Γ) Γ' x i) Γ'')
    -- TerminalProj (BSys++Eq (CtxToBSys AS Γ) Γ' x i)
    -- _↝_.Ty↝ (SubstToHomEqTm AS BS Γ f Γ' x T i x₁) T'

    -- NeededSubstGen (CtxToBSys AS Γ) BS (Γ' ++ x) ((TerminalProj (CtxToBSys AS Γ) (Γ' ++ x)) ○ f) T

    -- SubstToHomEqHelpPoly (CtxToBSys AS Γ) (BSystem.BSlc BS T) (Γ' ++ x)


    SubstToHomEqHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                        {f : B ↝ (CtxToTyTmStr AS Γ)}
                        {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                        (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp (CtxToBSys AS Γ) (CtxToBSys BS Δ') Γ' (SubstToHomHelp ɣ)) 
    SubstToHomEqHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') i .Tm x T = TyTmStr.Tm (TyTmStr++Eq (CtxToBSys AS Γ) Γ' x i) (_↝_.Ty↝ (TerminalProjCompf (CtxToBSys AS Γ) Γ' x f i) T) 
    SubstToHomEqHelp {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') i .⇑ {x} {T} t = {!  SubstToHomEqHelpPoly (CtxToBSys AS Γ) BS f Γ' x T i t   !}  
    SubstToHomEqHelp {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} (cns Γ'' T t Γ''' Δ' ɣ) = {! (symP (transport-filler
                (λ i → DepPoly (++-ceil Γ'' Γ''' (~ i)) (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T) Δ'))) ⌈ ɣ ⌉s)) 
                ▷ (SubstToHomEqHelp ɣ)  !}

 -- ▷
        -- (symP (transport-filler
        --         (λ i → DepPoly (++-ceil Γ'' Γ''' (~ i)) (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T) Δ'))) ⌈ ɣ ⌉s))

        -- transport-filler (λ i₁ → (DepPoly (++-ceil Γ' x i₁) (BSystemToTyStr (BSystem.BSlc BS T))))
        -- SubstToHomEqHelpPoly AS BS Γ f Γ' x T i t 

        -- somethings wrong in SubstToHomEqHelpPoly with the typing of f
    SubstToHomEq1 : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                        {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp BS (CtxToBSys BS Δ) Γ (SubstToHom ɣ))
    SubstToHomEq1 {BS = BS} {Γ = Γ} (● Γ) i .Tm x x₁ = TyTmStr.Tm (TyTmStr++Eq BS Γ x i) (_↝_.Ty↝ (TerminalProjComp BS Γ x i) x₁) -- TyTmStr.Tm (TyTmStr++Eq BS Γ x i)
    SubstToHomEq1 {BS = BS} {Γ = Γ} (● Γ) i .⇑ {Γ'} {T} t = {! SubstToHomEqHelpPoly BS (BSystem.BSlc BS T)   !} -- SubstToHomEqHelpPoly BS (BSystem.BSlc BS T)
    SubstToHomEq1 (cns Γ T t Γ' Δ' ɣ) = {!  SubstToHomEqHelp ɣ !}
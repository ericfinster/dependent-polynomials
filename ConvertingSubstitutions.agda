{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

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

    SubstToHomHelpIsHomomorphism : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                    {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                    {f : B ↝ (CtxToTyTmStr AS Γ)}
                    {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                    (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                    → is-homomorphism (CtxToPreSys BS Δ') (CtxToPreSys (CtxToBSys AS Γ) Γ') (SubstToHomHelp ɣ)
    SubstToHomHelpIsHomomorphism (● _) = {!   !}
    SubstToHomHelpIsHomomorphism (cns Γ T t Γ' Δ' ɣ) = {! SubstToHomHelpIsHomomorphism ɣ  !}


    SubstToHom : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                    {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                    → (TopTyTm (CtxPToCtxB BS Δ)) ↝ (TopTyTm (CtxPToCtxB BS Γ))
    SubstToHom {Bᵇ = Bᵇ} {BS = BS} {Γ = Γ} (● Γ) = wkCtxt Bᵇ (CtxPToCtxB BS Γ)
    SubstToHom {BS = BS} (cns Γ T t Γ' Δ' ɣ) = transport (λ i → (TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ')) ↝ (TopTyTm++BSys BS Γ Γ' i)) (SubstToHomHelp ɣ)

    SubstToHomHomomorphism : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                    {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                    → is-homomorphism (CtxToPreSys BS Δ) (CtxToPreSys BS Γ) (SubstToHom ɣ)
    SubstToHomHomomorphism {BS = BS} {Γ = Γ} (● _) = wkCtxtIsHomomorphism BS (CtxPToCtxB BS Γ)
    SubstToHomHomomorphism (cns Γ T t Γ' Δ' ɣ) = {! SubstToHomHelpIsHomomorphism ɣ  !}

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


    SubstToHomEqHelpPoly :{A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ)  
                        (f : B ↝ A)
                        (Γ' : Ctx (BSystemToTyStr AS))
                        (x : Ctx (BSystemToTyStr (CtxToBSys AS Γ')))
                        (T : TyTmStr.Typ B)
                        → PathP (λ i → (TyTmStr.Tm (TyTmStr++Eq AS Γ' x i) (_↝_.Ty↝ (TerminalProjCompf AS Γ' x f i) T)) → DepPoly (++-ceil Γ' x i) (BSystemToTyStr (BSystem.BSlc BS T))) 
                            (λ t → (BSystemToDepPolyHelp AS (BSystem.BSlc BS T) (Γ' ++ x) (NeededSubstGen AS BS (Γ' ++ x) (TerminalProj AS(Γ' ++ x) ○ f) T t)))
                            λ t → (BSystemToDepPolyHelp (CtxToBSys AS Γ') (BSystem.BSlc BS T) x (NeededSubstGen (CtxToBSys AS Γ') BS x 
                            (TerminalProj (CtxToBSys AS Γ') x ○ (wkCtxt Aᵇ (CtxPToCtxB AS Γ') ○ f)) T t))
    SubstToHomEqHelpPoly AS BS f Γ' x T i x₁ .Tm Γ'' T' = TyTmStr.Tm ((CtxToTyBSys++Eq AS Γ' x i) Γ'')
                        (_↝_.Ty↝ ((TerminalProjCeil AS Γ' x i Γ'') ○ (SubstToHomEqTm AS BS f Γ' x T i x₁)) T')
    SubstToHomEqHelpPoly AS BS f Γ' x T i x₁ .⇑ {Γ''} {T'} t = BSystemToDepPolyHelpEq AS (BSystem.BSlc (BSystem.BSlc BS T) T') Γ' x i Γ'' 
            (NeededSubstGenEq AS BS Γ' x T T' i Γ'' ((TerminalProjCeil AS Γ' x i Γ'') ○ (SubstToHomEqTm AS BS f Γ' x T i x₁)) t)

    TestHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) 
                        (f : B ↝ A) {T : TyTmStr.Typ B}
                        (TA : TyTmStr.Typ A)
                        {Γ' : Ctx (BSystemToTyStr AS)} {Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T))}
                        (Γ'' : Ctx (BSystemToTyStr (BSystem.BSlc AS TA))) (Γ''' : Ctx (BSystemToTyStr (CtxToBSys AS (TA ► Γ''))))
                        (t : TyTmStr.Tm (CtxToTyTmStr AS (TA ► Γ'')) (_↝_.Ty↝ (TerminalProj AS (TA ► Γ'')) (_↝_.Ty↝ f T)))
                        (ɣ : Subst (BSystemToDepPolyHelp AS (BSystem.BSlc BS T) (TA ► Γ'') 
                            (NeededSubstGen AS BS (TA ► Γ'') (TerminalProj AS(TA ► Γ'') ○ f) T t)) Γ''' Δ')
                        → Subst (BSystemToDepPolyHelp (BSystem.BSlc AS TA) (BSystem.BSlc BS T)  Γ'' 
                            (NeededSubstGen (BSystem.BSlc AS TA) BS  Γ'' ((TerminalProj (BSystem.BSlc AS TA) Γ'' ○ (PreBSystem.wk Aᵇ TA)) ○ f) T t)) Γ''' Δ'
    TestHelp AS BS f TA Γ'' Γ''' t (● .Γ''') = ● Γ'''
    TestHelp AS BS f {T = T'} TA Γ'' Γ''' t (cns Γ T t₁ Γ' Δ' ɣ) = cns Γ T t₁ Γ' Δ' ɣ


    Test : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) 
                        (f : B ↝ A) {T : TyTmStr.Typ B}
                        {Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T))}
                        (Γ'' : Ctx (BSystemToTyStr AS)) (Γ''' : Ctx (BSystemToTyStr (CtxToBSys AS Γ'')))
                        (t : TyTmStr.Tm (CtxToTyTmStr AS Γ'') (_↝_.Ty↝ (TerminalProj AS Γ'') (_↝_.Ty↝ f T)))
                        (ɣ : Subst (BSystemToDepPolyHelp AS (BSystem.BSlc BS T) Γ'' 
                            (NeededSubstGen AS BS Γ'' (TerminalProj AS Γ'' ○ f) T t)) Γ''' Δ') 
                        → transport (λ i → DepPoly (++-ceil Γ'' Γ''' (~ i)) (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T) Δ'))) 
                        (BSystemToDepPolyHelp (CtxToBSys AS Γ'') (CtxToBSys (BSystem.BSlc BS T) Δ') Γ''' (SubstToHomHelp ɣ))
                        ≡ BSystemToDepPolyHelp AS (CtxToBSys (BSystem.BSlc BS T) Δ') (Γ'' ++ Γ''')
                        (transport (λ i → TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ') ↝ TopTyTm++BSys AS Γ'' Γ''' i) (SubstToHomHelp ɣ)) 
    Test AS BS f ϵ Γ''' t ɣ = {!   !}
    Test {Aᵇ = Aᵇ} AS BS f {T = T'} (T ► Γ'') Γ''' t ɣ = {! cong (λ x → (NeededSubstGen (BSystem.BSlc AS T) BS  Γ'' x T' ?)) 
            (○-assoc (TerminalProj (BSystem.BSlc AS T) Γ'') (PreBSystem.wk Aᵇ T) f) !} -- (TestHelp AS BS f T Γ'' Γ''' t ɣ)    Test (BSystem.BSlc AS T) BS Γ'' Γ''' t


    SubstToHomEqHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                        {f : B ↝ (CtxToTyTmStr AS Γ)}
                        {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                        (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp (CtxToBSys AS Γ) (CtxToBSys BS Δ') Γ' (SubstToHomHelp ɣ)) 
    SubstToHomEqHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') i .Tm x T = TyTmStr.Tm (TyTmStr++Eq (CtxToBSys AS Γ) Γ' x i) (_↝_.Ty↝ (TerminalProjCompf (CtxToBSys AS Γ) Γ' x f i) T)
    SubstToHomEqHelp {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') i .⇑ {x} {T} t = transport-fillerExt⁻ (λ i₁ → DepPoly (++-ceil Γ' x i₁) (BSystemToTyStr (BSystem.BSlc BS T))) i 
            ((SubstToHomEqHelpPoly (CtxToBSys AS Γ) BS f Γ' x T) i t)   
    SubstToHomEqHelp {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} (cns Γ'' T t Γ''' Δ' ɣ) = cong (λ x → (transport (λ i → DepPoly (++-ceil Γ'' Γ''' (~ i))
         (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T) Δ'))) x)) (SubstToHomEqHelp ɣ) ∙ (Test (CtxToBSys AS Γ) BS f Γ'' Γ''' t ɣ)

    SubstToHomEq1Hom : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
                    (Γ' : Ctx (BSystemToTyStr (CtxToBSys BS Γ))) (T : TyTmStr.Typ B)
                    → PathP (λ i → (t : TyTmStr.Tm (TyTmStr++Eq BS Γ Γ' i) (_↝_.Ty↝ (TerminalProjComp BS Γ Γ' i) T)) → (TyTmStr.Slc B T) ↝ TyTmStr++Eq BS Γ Γ' i) 
                    (λ t → (NeededSubst BS (Γ ++ Γ') T t)) 
                    λ t → (NeededSubstGen (CtxToBSys BS Γ) BS Γ' (TerminalProj (CtxToBSys BS Γ) Γ' ○ wkCtxt Bᵇ (CtxPToCtxB BS Γ)) T t)
    SubstToHomEq1Hom BS Γ Γ' T i t = (PreBSystem.sub (PreSys++Eq BS Γ Γ' i) (_↝_.Ty↝ (TerminalProjComp BS Γ Γ' i) T) t) ○ (_↝_.Slc↝ (TerminalProjComp BS Γ Γ' i) T)


    SubstToHomEq1Poly : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
                    (Γ' : Ctx (BSystemToTyStr (CtxToBSys BS Γ))) (T : TyTmStr.Typ B)
                    → PathP (λ i → (t : TyTmStr.Tm (TyTmStr++Eq BS Γ Γ' i) (_↝_.Ty↝ (TerminalProjComp BS Γ Γ' i) T)) 
                    → DepPoly (++-ceil Γ Γ' i) ((BSystemToTyStr (BSystem.BSlc BS T)))) 
                    (λ t → (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (Γ ++ Γ') (NeededSubst BS (Γ ++ Γ') T t))) 
                    λ t → BSystemToDepPolyHelp (CtxToBSys BS Γ) (BSystem.BSlc BS T) Γ' 
                        (NeededSubstGen (CtxToBSys BS Γ) BS Γ' (TerminalProj (CtxToBSys BS Γ) Γ' ○ wkCtxt Bᵇ (CtxPToCtxB BS Γ)) T t)
    SubstToHomEq1Poly BS Γ Γ' T i t = BSystemToDepPolyHelpEqFirstStep BS Γ Γ' T i (SubstToHomEq1Hom BS Γ Γ' T i t)

    SubstToHomEq1 : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                        {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp BS (CtxToBSys BS Δ) Γ (SubstToHom ɣ))
    SubstToHomEq1 {BS = BS} {Γ = Γ} (● Γ) i .Tm x x₁ = TyTmStr.Tm (TyTmStr++Eq BS Γ x i) (_↝_.Ty↝ (TerminalProjComp BS Γ x i) x₁) -- TyTmStr.Tm (TyTmStr++Eq BS Γ x i)
    SubstToHomEq1 {B} {BS = BS} {Γ = Γ} (● Γ) i .⇑ {Γ'} {T} t = (transport-fillerExt⁻ (λ i₁ → DepPoly (++-ceil Γ Γ' i₁) (BSystemToTyStr (BSystem.BSlc BS T))) i) (SubstToHomEq1Poly BS Γ Γ' T i t) -- (SubstToHomEq1Poly BS Γ Γ' T i t)
    SubstToHomEq1 {BS = BS} (cns Γ T t Γ' Δ' ɣ) = {! cong (λ x → (transport (λ i → DepPoly (++-ceil Γ Γ' (~ i)) (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T) Δ'))) x)) 
             (SubstToHomEqHelp ɣ)  !} 

    -- cong (λ x → (transport (λ i → DepPoly (++-ceil Γ Γ' (~ i)) (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T) Δ'))) x)) 
    --         (SubstToHomEqHelp ɣ) ∙      
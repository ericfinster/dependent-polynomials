

open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import BSystems

module BSystemToDepPoly where

    {-# BUILTIN REWRITE _≡_ #-}


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

    -- -- -- Lifting BSystem Structure along a Context

    -- I should make this consistent if I have time and use the tooling from Ctxt in BSystem
    CtxToTyTmStr : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (TyTmStr)
    CtxToTyTmStr BS Γ = TopTyTm (CtxPToCtxB BS Γ)

    CtxToPreSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (PreBSystem (CtxToTyTmStr BS Γ))
    CtxToPreSys {Bᵇ = Bᵇ} BS ϵ = Bᵇ
    CtxToPreSys BS (T ► Γ) = CtxToPreSys (BSystem.BSlc BS T) Γ

    CtxToBSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → (BSystem (CtxToTyTmStr BS Γ) (CtxToPreSys BS Γ))
    CtxToBSys BS ϵ = BS
    CtxToBSys BS (T ► Γ) = CtxToBSys (BSystem.BSlc BS T) Γ

    -- -- --

    
        -- needed Equality to use Contexts in the lifted BSystem
    ⌈_⌉BSysEqual : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
            → ⌈ Γ ⌉ ≡ (BSystemToTyStr (CtxToBSys BS Γ))
    ⌈_⌉BSysEqual BS ϵ = refl
    ⌈_⌉BSysEqual BS (T₁ ► Γ) = ⌈_⌉BSysEqual (BSystem.BSlc BS T₁) Γ
    {-# REWRITE ⌈_⌉BSysEqual #-}

    -- -- -- some equalities which may be helpfull for mu

    EqHelp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ' : Ctx (BSystemToTyStr BS))
            → Γ' ≡ (transport (λ i → Ctx (BSystemToTyStr BS)) Γ')
    EqHelp BS Γ' = sym (transportRefl Γ')

    -- maybe needed for BSystemToMonad
    TyTmStr++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → (CtxToTyTmStr BS (Γ ++ Γ')) ≡ (CtxToTyTmStr (CtxToBSys BS Γ) Γ')
    TyTmStr++Eq BS ϵ Γ' = refl
    TyTmStr++Eq BS (T ► Γ) Γ' = TyTmStr++Eq (BSystem.BSlc BS T) Γ Γ'

    {-
    solution without rewrite

    (transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i))) Γ')

    cong (λ x → CtxToTyTmStr BS x) (EqHelp BS Γ')
    -}

    BSys++Eq : {A : TyTmStr} {Aᵇ : PreBSystem A} (AS : BSystem A Aᵇ) (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))) 
                → (TopTyTm (CtxPToCtxB (CtxToBSys AS Γ) Γ')) ≡ (TopTyTm (CtxPToCtxB AS (Γ ++ Γ')))
    BSys++Eq AS ϵ Γ' = refl
    BSys++Eq AS (T ► Γ) Γ' = BSys++Eq (BSystem.BSlc AS T) Γ Γ'

    TerminalProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → B ↝ (CtxToTyTmStr BS Γ)
    TerminalProj {Bᵇ = Bᵇ} BS Γ = wkCtxt Bᵇ (CtxPToCtxB BS Γ)

    -- TerminalProj {B} BS ϵ = idStr B
    -- TerminalProj {Bᵇ = Bᵇ} BS (T ► Γ) = (TerminalProj (BSystem.BSlc BS T) Γ) ○ (PreBSystem.wk Bᵇ T)


    TerminalProjComp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → PathP  (λ i → (B ↝ (TyTmStr++Eq BS Γ Γ' i))) (TerminalProj BS (Γ ++ Γ')) 
            ((TerminalProj (CtxToBSys BS Γ) Γ') ○ (TerminalProj BS Γ))
    TerminalProjComp BS ϵ Γ' = sym (IdStrRN (TerminalProj BS Γ'))
    TerminalProjComp {Bᵇ = Bᵇ} BS (T ► Γ) Γ' = congP (λ i → (λ x → x ○ (PreBSystem.wk Bᵇ T))) (TerminalProjComp (BSystem.BSlc BS T) Γ Γ') 
                ▷ (○-assoc (TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) Γ') (TerminalProj (BSystem.BSlc BS T) Γ) (PreBSystem.wk Bᵇ T)) 


                {-
                solutions without rewrite
                cong (λ x → TerminalProj BS x) (EqHelp BS Γ') ▷ (sym (IdStrRN (TerminalProj BS (transport (λ i → Ctx (BSystemToTyStr BS)) Γ'))))


                congP (λ i → (λ x → x ○ (PreBSystem.wk Bᵇ T))) (TerminalProjComp (BSystem.BSlc BS T) Γ Γ') 
               ▷ (○-assoc (TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) (transport (λ i → Ctx (⌈ BSystem.BSlc BS T ⌉BSysEqual Γ i)) Γ')) 
                (TerminalProj (BSystem.BSlc BS T) Γ) (PreBSystem.wk Bᵇ T))


                -}

    -- -- --

    -- -- -- Converting BSystems (technically PreBSystems are enough) to DepPolys 

    -- When lifting a BSystem Polynomial, one needs to first substitute the term along the old data, from the level below
    -- this is what NeededSubst does, Gen does it for the Help case, where the TyTmStr diverge
    NeededSubstGen : {A B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
            (f : B ↝ (CtxToTyTmStr AS Γ)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T))
            → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ))
    NeededSubstGen AS BS Γ f T t = (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ (_↝_.Slc↝ f T)

    NeededSubst : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T))
                → ((TyTmStr.Slc B T) ↝ (CtxToTyTmStr BS Γ))
    NeededSubst BS Γ T t = NeededSubstGen BS BS Γ (TerminalProj BS Γ) T t
    
    -- Needed since when lifitng the domain and codomain BSystems diverge 

    {-# TERMINATING #-}
    BSystemToDepPolyHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
                (f : B ↝ (CtxToTyTmStr AS Γ)) 
                → (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr BS))
    BSystemToDepPolyHelp AS BS Γ f .Tm x x₁ = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) 
        x) (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) x ○ f) x₁)
    BSystemToDepPolyHelp {Aᵇ = Aᵇ} AS BS Γ f .⇑ {x} {T'} t = BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T') x
        (NeededSubstGen (CtxToBSys AS Γ) BS x ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T' t)


        {-
            wont work exactly like this, since we now hand the already sliced BSystem to the function
        
        without rewrite
            transport (λ i → DepPoly (⌈_⌉BSysEqual (CtxToBSys AS Γ) x (~ i)) (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T')))
        (BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T) x T'
        (NeededSubstGen (CtxToBSys AS Γ) (BSystem.BSlc BS T) x ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T' t))
        -}

    
    BSystemToDepPoly : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (DepPoly (BSystemToTyStr BS) (BSystemToTyStr BS))
    BSystemToDepPoly BS .Tm Γ T = TyTmStr.Tm (CtxToTyTmStr BS Γ) (_↝_.Ty↝ (TerminalProj BS Γ) T)
    BSystemToDepPoly BS .⇑ {Γ} {T} t = (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) Γ (NeededSubst BS Γ T t))


        {-
        without Rewrite

        transport (λ i → DepPoly (⌈_⌉BSysEqual BS Γ (~ i)) (BSystemToTyStr (BSystem.BSlc BS T)))
        (BSystemToDepPolyHelp BS BS Γ T (NeededSubst BS Γ T t))
        -}

    -- -- --

    -- -- -- Converting Substitutions
     
    -- gets way more complex without the rewrite
    SubstToHomHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                    {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                    {f : B ↝ (CtxToTyTmStr AS Γ)}
                    {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                    (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                    → (TopTyTm (CtxPToCtxB BS Δ')) ↝ (TopTyTm (CtxPToCtxB (CtxToBSys AS Γ) Γ'))
    SubstToHomHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● _) = (wkCtxt (CtxToPreSys AS Γ) (CtxPToCtxB (CtxToBSys AS Γ) Γ')) ○ f
    SubstToHomHelp {AS = AS} {BS = BS} {Γ = Γ} (cns Γ' T' t Γ'' Δ' ɣ) = transport (λ i → (TopTyTm (CtxPToCtxB (BSystem.BSlc BS T') Δ') ↝ (BSys++Eq (CtxToBSys AS Γ) Γ' Γ'' i)))
                    (SubstToHomHelp ɣ)


    SubstToHom : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                    {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                    → (TopTyTm (CtxPToCtxB BS Δ)) ↝ (TopTyTm (CtxPToCtxB BS Γ))
    SubstToHom {Bᵇ = Bᵇ} {BS = BS} {Γ = Γ} (● Γ) = wkCtxt Bᵇ (CtxPToCtxB BS Γ)
    SubstToHom {BS = BS} (cns Γ T t Γ' Δ' ɣ) = transport (λ i → (TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ')) ↝ (BSys++Eq BS Γ Γ' i)) (SubstToHomHelp ɣ)
    
    postulate

        -- SubstToHomEq1 : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
        --                 {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
        --                 → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp BS (CtxToBSys BS Δ) Γ (SubstToHom ɣ))
        
        -- SubstToHomEqHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
        --                 {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
        --                 {f : B ↝ (CtxToTyTmStr AS Γ)}
        --                 {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
        --                 (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
        --                 → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp (CtxToBSys AS Γ) (CtxToBSys BS Δ') Γ' (SubstToHomHelp ɣ)) 
    

    SubstToHomEqHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                        {f : B ↝ (CtxToTyTmStr AS Γ)}
                        {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                        (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp (CtxToBSys AS Γ) (CtxToBSys BS Δ') Γ' (SubstToHomHelp ɣ)) 
    SubstToHomEqHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') i .Tm x x₁ = TyTmStr.Tm  (TyTmStr++Eq (CtxToBSys AS Γ) Γ' x i) (_↝_.Ty↝ (TerminalProjComp (CtxToBSys AS Γ) Γ' x i) (_↝_.Ty↝ f x₁)) 
    SubstToHomEqHelp {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') i .⇑ {x} {T} t = {!   !} -- (TerminalProjComp (CtxToBSys AS Γ) Γ' x) 
    SubstToHomEqHelp (cns Γ T t Γ' Δ' ɣ) = {! SubstToHomEqHelp ɣ  !}

 
    SubstToHomEq1 : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                        {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp BS (CtxToBSys BS Δ) Γ (SubstToHom ɣ))
    SubstToHomEq1 (● _) i .Tm x x₁ = {!   !}
    SubstToHomEq1 (● _) i .⇑ t = {!   !}
    SubstToHomEq1 (cns Γ T t Γ' Δ' ɣ) = {!  SubstToHomEqHelp ɣ !}



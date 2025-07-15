

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

    -- BSystemToDepPolyHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
    --             (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
    --             (T : TyTmStr.Typ B) (f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ)) 
    --             → (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr (BSystem.BSlc BS T)))
    -- BSystemToDepPolyHelp AS BS Γ T f .Tm x x₁ = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) 
    --     x) (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) x ○ f) x₁)
    -- BSystemToDepPolyHelp {Aᵇ = Aᵇ} AS BS Γ T f .⇑ {x} {T'} t = (BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T) x T'
    --     (NeededSubstGen (CtxToBSys AS Γ) (BSystem.BSlc BS T) x ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T' t))

        {-
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

    WeirdHelper : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B) (Γ : Ctx (BSystemToTyStr (BSystem.BSlc BS T))) → TyTmStr
    WeirdHelper {B} BS T ϵ = TyTmStr.Slc B T
    WeirdHelper BS T (T' ► Γ) = WeirdHelper (BSystem.BSlc BS T) T' Γ 
    
    postulate

        NeededEq : {A : TyTmStr} {Aᵇ : PreBSystem A} (AS : BSystem A Aᵇ) (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ)))
                (Γ'' : Ctx (BSystemToTyStr (CtxToBSys (CtxToBSys AS Γ) Γ')))
                → (BSystemToTyStr (CtxToBSys (CtxToBSys (CtxToBSys AS Γ) Γ') Γ'')) ≡ (BSystemToTyStr (CtxToBSys (CtxToBSys AS Γ) (Γ' ++ Γ'')))
    -- NeededEq AS Γ Γ' Γ'' i .Ty = {!   !}
    -- NeededEq AS Γ Γ' Γ'' i // x = {!   !}

    SubstToHomPoly : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                {f : B ↝ (CtxToTyTmStr AS Γ)}
                {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                → DepPoly (BSystemToTyStr (CtxToBSys (CtxToBSys AS Γ) Γ')) (BSystemToTyStr (CtxToBSys BS Δ'))
    SubstToHomPoly {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') .Tm Γ'' T' = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys (CtxToBSys AS Γ) Γ') Γ'') 
            (_↝_.Ty↝ ((TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ') Γ'') ○ ((TerminalProj (CtxToBSys AS Γ) Γ') ○ f)) T') 
    SubstToHomPoly {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} (● Γ') .⇑ {Γ''} {T'} t = BSystemToDepPolyHelp (CtxToBSys (CtxToBSys AS Γ) Γ') (BSystem.BSlc BS T') Γ''
            (NeededSubstGen (CtxToBSys (CtxToBSys AS Γ) Γ') BS Γ'' ((TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ') Γ'') ○ ((TerminalProj (CtxToBSys AS Γ) Γ') ○ f)) T' t) 
    SubstToHomPoly {AS = AS} {BS = BS} {Γ = Γ} (cns Γ' T' t Γ'' Δ' ɣ) = transport (λ i → DepPoly (NeededEq AS Γ Γ' Γ'' i) (BSystemToTyStr (CtxToBSys (BSystem.BSlc BS T') Δ'))) (SubstToHomPoly ɣ) 

    -- the idea is to show that ⌈ ɣ ⌉s equals some expression of the form ToDepPolyHelp, to be able to construct a morphism from a substitution
    postulate

        SubstToHomEq : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                        {f : B ↝ (CtxToTyTmStr AS Γ)}
                        {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                        (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                        → ⌈ ɣ ⌉s ≡ (SubstToHomPoly ɣ)
--     SubstToHomEq (● _) i .Tm x x₁ = {!   !}
--     SubstToHomEq (● _) i .⇑ = {!   !}
--     SubstToHomEq (cns Γ T t Γ' Δ' ɣ) = {!   !}

    -- won't work because the lift has no repeating pattern
        -- could maybe work by extending gamma in each step by the lower portion of gamma'
    postulate

        SubstToHomEq1 : {B : TyTmStr} {Bᵇ : PreBSystem B} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr BS)} 
                        {Δ : Ctx (BSystemToTyStr BS)} (ɣ : Subst (BSystemToDepPoly BS) Γ Δ)
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp BS (CtxToBSys BS Δ) Γ (SubstToHom ɣ))
        
        SubstToHomEqHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                        {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                        {f : B ↝ (CtxToTyTmStr AS Γ)}
                        {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
                        (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                        → ⌈ ɣ ⌉s ≡ (BSystemToDepPolyHelp (CtxToBSys AS Γ) (CtxToBSys BS Δ') Γ' (SubstToHomHelp ɣ)) 

        -- DepPoly (BSystemToTyStr (CtxToBSys (CtxToBSys AS Γ) Γ')) (BSystemToTyStr (CtxToBSys BS Δ'))

        -- SubstToHomSubst : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
        --                 {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
        --                 {f : B ↝ (CtxToTyTmStr AS Γ)}
        --                 {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))} {Δ' : Ctx (BSystemToTyStr BS)}
        --                 (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
        --                 (Γ1 : Ctx (BSystemToTyStr (CtxToBSys (CtxToBSys AS Γ) Γ')))
        --                 (Δ1 : Ctx (BSystemToTyStr (CtxToBSys BS Δ')))
        --                 (ɣ' : Subst (SubstToHomPoly ɣ) Γ1 Δ1)
        --                 → (TopTyTm (CtxPToCtxB (CtxToBSys BS Δ') Δ1)) ↝ TopTyTm (CtxPToCtxB (CtxToBSys (CtxToBSys AS Γ) Γ') Γ1)
--     SubstToHomSubst {AS = AS} {Γ = Γ} {Γ' = Γ'} ɣ Γ1 Δ1 (● .Γ1) = (TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ') Γ1) ○ (SubstToHomHelp ɣ) 
--     SubstToHomSubst {Γ' = Γ'} ɣ Γ1 Δ1 (cns Γ'' T t Γ''' Δ' ɣ') = {! cns    !}


    --  ⌈ ɣ ⌉s 
    -- (_↝_.Ty↝  (wkCtxt Bᵇ  (T ⊳ (CtxPToCtxB (BSystem.BSlc BS T) Δ'))) T)
    -- BSystemToDepPolyHelp (CtxToBSys AS Γ) (CtxToBSys BS (CtxBToCtxP BS (T ⊳ (CtxPToCtxB (BSystem.BSlc BS T) Δ')))) Γ'

    -- BSystemToDepPolyHelp : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
    --             (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
    --             (T : TyTmStr.Typ B) (f : (TyTmStr.Slc B T) ↝ (CtxToTyTmStr AS Γ)) 
    --             → (DepPoly (BSystemToTyStr (CtxToBSys AS Γ)) (BSystemToTyStr (BSystem.BSlc BS T)))
    -- BSystemToDepPolyHelp AS BS Γ T f .Tm x x₁ = TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) 
    --     x) (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) x ○ f) x₁)
    -- BSystemToDepPolyHelp {Aᵇ = Aᵇ} AS BS Γ T f .⇑ {x} {T'} t = (BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc BS T) x T'
    --     (NeededSubstGen (CtxToBSys AS Γ) (BSystem.BSlc BS T) x ((TerminalProj (CtxToBSys AS Γ) x) ○ f) T' t))



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




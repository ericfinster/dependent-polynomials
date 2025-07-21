{-# OPTIONS --no-termination-check --no-positivity-check #-}

-- {-# OPTIONS --allow-unsolved-metas #-}

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

    AppCtx : {B C : TyTmStr} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ) (Γ : Ctx (BSystemToTyStr BS))
                → (f : B ↝ C) → (Ctx (BSystemToTyStr CS))
    AppCtx BS CS Γ f = CtxBToCtxP CS (AppCtxt (CtxPToCtxB BS Γ) f)
    -- -- --

    
        -- needed Equality to use Contexts in the lifted BSystem
    ⌈_⌉BSysEqual : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
            → ⌈ Γ ⌉ ≡ (BSystemToTyStr (CtxToBSys BS Γ))
    ⌈_⌉BSysEqual BS ϵ = refl
    ⌈_⌉BSysEqual BS (T₁ ► Γ) = ⌈_⌉BSysEqual (BSystem.BSlc BS T₁) Γ
    {-# REWRITE ⌈_⌉BSysEqual #-}


    -- without rewrite, this needs to be a PathP
    CtxToTyTmStrSlcEq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : Ty ⌈ Γ ⌉)
                → (TyTmStr.Slc (CtxToTyTmStr BS Γ) T) ≡ (CtxToTyTmStr BS (Γ ++ (T ► ϵ)))
    CtxToTyTmStrSlcEq BS ϵ T = refl
    CtxToTyTmStrSlcEq BS (T' ► Γ) T = CtxToTyTmStrSlcEq (BSystem.BSlc BS T') Γ T  

    -- -- -- some equalities which may be helpfull for mu

    EqHelp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ' : Ctx (BSystemToTyStr BS))
            → Γ' ≡ (transport (λ i → Ctx (BSystemToTyStr BS)) Γ')
    EqHelp BS Γ' = sym (transportRefl Γ')

    -- maybe needed for BSystemToMonad
    TyTmStr++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → (CtxToTyTmStr BS (Γ ++ Γ')) ≡ (CtxToTyTmStr (CtxToBSys BS Γ) Γ')
    TyTmStr++Eq BS ϵ Γ' = refl
    TyTmStr++Eq BS (T ► Γ) Γ' = TyTmStr++Eq (BSystem.BSlc BS T) Γ Γ'

    PreSys++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → PathP (λ i → PreBSystem (TyTmStr++Eq BS Γ Γ' i)) (CtxToPreSys BS (Γ ++ Γ')) (CtxToPreSys (CtxToBSys BS Γ) Γ')
    PreSys++Eq BS ϵ Γ' = refl
    PreSys++Eq BS (T ► Γ) Γ' = PreSys++Eq (BSystem.BSlc BS T) Γ Γ'

    BSys++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → PathP (λ i → BSystem (TyTmStr++Eq BS Γ Γ' i) (PreSys++Eq BS Γ Γ' i)) (CtxToBSys BS (Γ ++ Γ')) (CtxToBSys (CtxToBSys BS Γ) Γ')
    BSys++Eq BS ϵ Γ' = refl
    BSys++Eq BS (T ► Γ) Γ' = BSys++Eq (BSystem.BSlc BS T) Γ Γ'


    {-
    solution without rewrite

    (transport (λ i → (Ctx (⌈_⌉BSysEqual BS Γ i))) Γ')

    cong (λ x → CtxToTyTmStr BS x) (EqHelp BS Γ')
    -}

    TopTyTm++BSys : {A : TyTmStr} {Aᵇ : PreBSystem A} (AS : BSystem A Aᵇ) (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))) 
                → (TopTyTm (CtxPToCtxB (CtxToBSys AS Γ) Γ')) ≡ (TopTyTm (CtxPToCtxB AS (Γ ++ Γ')))
    TopTyTm++BSys AS ϵ Γ' = refl
    TopTyTm++BSys AS (T ► Γ) Γ' = TopTyTm++BSys (BSystem.BSlc AS T) Γ Γ'

    -- this was needed since BSys++Eq is a different Path to ++-ceil so we cant then apply the TyStr resulting from that BSys to a Context along ++-ceil
    CtxToTyBSys++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉) 
            → PathP (λ i → Ctx (++-ceil Γ Γ' i) → TyTmStr) (λ t → (CtxToTyTmStr (CtxToBSys BS (Γ ++ Γ')) t)) λ t → (CtxToTyTmStr (CtxToBSys (CtxToBSys BS Γ) Γ') t)
    CtxToTyBSys++Eq BS ϵ Γ' = refl
    CtxToTyBSys++Eq BS (T ► Γ) Γ' = CtxToTyBSys++Eq (BSystem.BSlc BS T) Γ Γ'


    TerminalProj : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) → B ↝ (CtxToTyTmStr BS Γ)
    TerminalProj {Bᵇ = Bᵇ} BS Γ = wkCtxt Bᵇ (CtxPToCtxB BS Γ)

    AppTerminalProj : {B C : TyTmStr} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
                (f : B ↝ C) → C ↝ CtxToTyTmStr CS (AppCtx  BS CS Γ f)
    AppTerminalProj BS CS Γ f = TerminalProj CS (AppCtx BS CS Γ f)

    HelperEq : {B C : TyTmStr} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
                (f : B ↝ C)
                → PathP (λ i → ((cong (λ x → (B ↝ TopTyTm x)) (rInv CS (AppCtxt (CtxPToCtxB BS Γ) f))) i)) (AppTerminalProj BS CS Γ f ○ f) ((wkCtxt Cᵇ (AppCtxt (CtxPToCtxB BS Γ) f) ○ f))
    HelperEq {Cᵇ = Cᵇ} BS CS Γ f i = wkCtxt Cᵇ (rInv CS (AppCtxt (CtxPToCtxB BS Γ) f) i) ○ f

    TerminalProjCommutes : {B C : TyTmStr} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ) (Γ : Ctx (BSystemToTyStr BS)) 
                (f : B ↝ C) (H : is-homomorphism Bᵇ Cᵇ f)
                → PathP (λ i → ((cong (λ x → (B ↝ TopTyTm x)) (rInv CS (AppCtxt (CtxPToCtxB BS Γ) f))) i)) ((AppTerminalProj BS CS Γ f) ○ f) 
                        (((SlcHomCtxt Bᵇ Cᵇ (CtxPToCtxB BS Γ) f) ○ TerminalProj BS Γ))  
    TerminalProjCommutes {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} BS CS Γ f H = (HelperEq BS CS Γ f) ▷ (sym (wkCtxtCommutes Bᵇ Cᵇ (CtxPToCtxB BS Γ) f H)) 
        

    TerminalProjCeil : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → PathP (λ i → (φ : Ctx (++-ceil Γ Γ' i)) → (TyTmStr++Eq BS Γ Γ' i) ↝ (CtxToTyBSys++Eq BS Γ Γ' i φ)) (λ φ → (TerminalProj (CtxToBSys BS (Γ ++ Γ')) φ)) λ φ → (TerminalProj (CtxToBSys (CtxToBSys BS Γ) Γ') φ)
    TerminalProjCeil BS ϵ Γ' = refl
    TerminalProjCeil BS (T ► Γ) Γ' = TerminalProjCeil (BSystem.BSlc BS T) Γ Γ'

    TerminalProjComp : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉)
            → PathP  (λ i → (B ↝ (TyTmStr++Eq BS Γ Γ' i))) (TerminalProj BS (Γ ++ Γ')) 
            ((TerminalProj (CtxToBSys BS Γ) Γ') ○ (TerminalProj BS Γ))
    TerminalProjComp BS ϵ Γ' = sym (IdStrRN (TerminalProj BS Γ'))
    TerminalProjComp {Bᵇ = Bᵇ} BS (T ► Γ) Γ' = congP (λ i → (λ x → x ○ (PreBSystem.wk Bᵇ T))) (TerminalProjComp (BSystem.BSlc BS T) Γ Γ') 
                ▷ (○-assoc (TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) Γ') (TerminalProj (BSystem.BSlc BS T) Γ) (PreBSystem.wk Bᵇ T)) 

    TerminalProjCompf : {A : TyTmStr} {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉) (f : A ↝ B)
            → PathP  (λ i → (A ↝ (TyTmStr++Eq BS Γ Γ' i))) 
                ((TerminalProj BS (Γ ++ Γ')) ○ f)
                ((TerminalProj (CtxToBSys BS Γ) Γ') ○ ((TerminalProj BS Γ) ○ f))
    TerminalProjCompf BS ϵ Γ' f = cong (λ x → (TerminalProj BS Γ' ○ x)) (sym (IdStrLN f))
    TerminalProjCompf {Bᵇ = Bᵇ} BS (T ► Γ) Γ' f = ((((○-assoc (TerminalProj (BSystem.BSlc BS T) (Γ ++ Γ')) (PreBSystem.wk Bᵇ T) f)
            ◁ (congP (λ i → (λ x → x ○ ((PreBSystem.wk Bᵇ T) ○ f))) (TerminalProjComp (BSystem.BSlc BS T) Γ Γ')))
            ▷ (sym (○-assoc ((TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) Γ') ○ (TerminalProj (BSystem.BSlc BS T) Γ)) (PreBSystem.wk Bᵇ T) f)))
            ▷ (cong (λ x → (x ○ f)) (○-assoc (TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) Γ') (TerminalProj (BSystem.BSlc BS T) Γ) (PreBSystem.wk Bᵇ T))))
            ▷ (○-assoc (TerminalProj (CtxToBSys (BSystem.BSlc BS T) Γ) Γ') ((TerminalProj (BSystem.BSlc BS T) Γ) ○ (PreBSystem.wk Bᵇ T)) f)


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

    NeededSubstGenTriv : {A B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
            (f : B ↝ (CtxToTyTmStr AS Γ)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T)) (H : is-homomorphism Bᵇ (CtxToPreSys AS Γ) f)
            → (NeededSubstGen AS BS Γ f T t) ○ (PreBSystem.wk Bᵇ T) ≡ f
    NeededSubstGenTriv {Bᵇ = Bᵇ} AS BS Γ f T t H = ((PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ (_↝_.Slc↝ f T)) ○ (PreBSystem.wk Bᵇ T)
        ≡⟨ ○-assoc (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) (_↝_.Slc↝ f T) (PreBSystem.wk Bᵇ T) ⟩
                (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ ((_↝_.Slc↝ f T) ○ (PreBSystem.wk Bᵇ T))
        ≡⟨ cong (λ x → (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ x) (is-homomorphism.wk≡ H T) ⟩
                (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ ((PreBSystem.wk (CtxToPreSys AS Γ) (_↝_.Ty↝ f T)) ○ f)
        ≡⟨ sym (○-assoc (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) (PreBSystem.wk (CtxToPreSys AS Γ) (_↝_.Ty↝ f T)) f) ⟩ 
                ((PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t) ○ (PreBSystem.wk (CtxToPreSys AS Γ) (_↝_.Ty↝ f T))) ○ f
        ≡⟨ cong (λ x → x ○ f) (BSystem.sub-of-wk-Tm (CtxToBSys AS Γ) t) ⟩
                (idStr (CtxToTyTmStr AS Γ)) ○ f
        ≡⟨ IdStrLN f ⟩
                f      
        ∎

--                  ≡⟨ sym (○-assoc (wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T))) (wk Cᵇ (Ty↝ f T)) f) ⟩
--         ((wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T)) ○ wk Cᵇ (Ty↝ f T)) ○ f)
--       ∎ 
  

--     NeededSubstGenEqBSys : {A B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) 
--             (f : B ↝ (CtxToTyTmStr AS Γ)) (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr AS Γ) (_↝_.Ty↝ f T)) (H : (is-homomorphism Bᵇ (CtxToPreSys AS Γ) f))
--             → {! (PreBSystem.sub (CtxToPreSys AS Γ) (_↝_.Ty↝ f T) t)   !} 

        -- this needs basically the same as BSystemToDepPolyHelpEq but I also need to handle the term in NeededSubstGen

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


    BSystemToDepPolyHelpEq : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr AS)) (Γ' : Ctx ⌈ Γ ⌉)
                → PathP (λ i → (φ : (Ctx (++-ceil Γ Γ' i))) → (g : (B ↝ (CtxToTyBSys++Eq AS Γ Γ' i φ))) → DepPoly ⌈ φ ⌉ (BSystemToTyStr BS)) 
                (λ φ g → BSystemToDepPolyHelp (CtxToBSys AS (Γ ++ Γ')) BS φ g) 
                λ φ g → BSystemToDepPolyHelp (CtxToBSys (CtxToBSys AS Γ) Γ') BS φ g
    BSystemToDepPolyHelpEq AS BS ϵ Γ' = refl
    BSystemToDepPolyHelpEq AS BS (T ► Γ) Γ' = BSystemToDepPolyHelpEq (BSystem.BSlc AS T) BS Γ Γ'

--     CtxToTyBSys++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉) 
--             → PathP (λ i → Ctx (++-ceil Γ Γ' i) → TyTmStr) (λ t → (CtxToTyTmStr (CtxToBSys BS (Γ ++ Γ')) t)) λ t → (CtxToTyTmStr (CtxToBSys (CtxToBSys BS Γ) Γ') t)
--     CtxToTyBSys++Eq BS ϵ Γ' = refl
--     CtxToTyBSys++Eq BS (T ► Γ) Γ' = CtxToTyBSys++Eq (BSystem.BSlc BS T) Γ Γ'


--     CtxToTyBSys++Eq : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (Γ' : Ctx ⌈ Γ ⌉) 
--             → PathP (λ i → Ctx (++-ceil Γ Γ' i) → TyTmStr) (λ t → (CtxToTyTmStr (CtxToBSys BS (Γ ++ Γ')) t)) λ t → (CtxToTyTmStr (CtxToBSys (CtxToBSys BS Γ) Γ') t)
--     CtxToTyBSys++Eq BS ϵ Γ' = refl
--     CtxToTyBSys++Eq BS (T ► Γ) Γ' = CtxToTyBSys++Eq (BSystem.BSlc BS T) Γ Γ'


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





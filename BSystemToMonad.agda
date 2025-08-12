

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import TyStr
open import DepPoly
open import Monad
open import BSystems
open import BSystemToDepPoly
open import ConvertingSubstitutions

module BSystemToMonad where

    TransportEq : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                (AS : BSystem A Aᵇ) 
                (BS : BSystem B Bᵇ)  
                {f : B ↝ A}
                {Γ₁ : Ctx (BSystemToTyStr AS)} 
                {Γ'' : Ctx (BSystemToTyStr (CtxToBSys AS Γ₁))}
                {T : TyTmStr.Typ B} {Δ'' : Ctx (BSystemToTyStr (BSystem.BSlc BS T))}
                {t : TyTmStr.Tm (CtxToTyTmStr AS Γ₁) (_↝_.Ty↝ (TerminalProj AS Γ₁) (_↝_.Ty↝ f T))}
                (ɣ : Subst (BSystemToDepPolyHelp AS (BSystem.BSlc BS T) Γ₁ (NeededSubstGen AS BS Γ₁
                    (TerminalProj AS Γ₁ ○ f) T t)) Γ'' Δ'')  
                → transport (λ i → B ↝ TopTyTm++BSys AS Γ₁ Γ'' i) ((SubstToHomHelp ɣ) ○ (TerminalProj BS (T ► Δ''))) 
                    ≡ transport (λ i → TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ'') ↝ TopTyTm++BSys AS Γ₁ Γ'' i)
                      (SubstToHomHelp ɣ) ○ (TerminalProj BS (T ► Δ'')) 
    TransportEq {B = B} AS BS {Γ₁ = Γ₁} {Γ'' = Γ''} {T = T} {Δ'' = Δ''} ɣ = transportSplit (TopTyTm++BSys AS Γ₁ Γ'') (TerminalProj BS (T ► Δ'')) (SubstToHomHelp ɣ)

    -- this needs sub-of-wk-Tm via NeededSubstGenTriv
    Eq3Diverge : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                {f : B ↝ (CtxToTyTmStr AS Γ)} {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))}
                {Δ' : Ctx (BSystemToTyStr BS)} (H : is-homomorphism Bᵇ (CtxToPreSys AS Γ) f)
                (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ')
                → (SubstToHomHelp ɣ) ○ (TerminalProj BS Δ') ≡ ((TerminalProj (CtxToBSys AS Γ) Γ') ○ f)
    Eq3Diverge {AS = AS} {Γ = Γ} {f = f} {Γ' = Γ'} H (● .Γ') = IdStrRN (TerminalProj (CtxToBSys AS Γ) Γ' ○ f)
    Eq3Diverge {B = B} {Bᵇ = Bᵇ} {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'}  H (cns Γ₁ T t Γ'' Δ'' ɣ) = (sym (TransportEq (CtxToBSys AS Γ) BS {f} ɣ)) 
                ∙
            (cong (λ x → (transport (λ i → B ↝ TopTyTm++BSys (CtxToBSys AS Γ) Γ₁ Γ'' i) x))
                ((SubstToHomHelp ɣ) ○ (TerminalProj BS (T ► Δ'')) 
            ≡⟨ refl ⟩ 
                SubstToHomHelp ɣ ○ (TerminalProj (BSystem.BSlc BS T) Δ'' ○ PreBSystem.wk Bᵇ T)
            ≡⟨ sym (○-assoc  (SubstToHomHelp ɣ) (TerminalProj (BSystem.BSlc BS T) Δ'') (PreBSystem.wk Bᵇ T))⟩    
                ((SubstToHomHelp ɣ ○ TerminalProj (BSystem.BSlc BS T) Δ'') ○ PreBSystem.wk Bᵇ T)
            ≡⟨ cong (λ x → x ○ (PreBSystem.wk Bᵇ T)) (Eq3Diverge (NeededSubstGenIsHomomorphism (CtxToBSys AS Γ) BS Γ₁ (TerminalProj (CtxToBSys AS Γ) Γ₁ ○ f) T t 
                        (○-homomorphism H (TerProjIsHomomorphism (CtxToBSys AS Γ) Γ₁))) ɣ)  ⟩
                ((TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'' ○ 
                    NeededSubstGen (CtxToBSys AS Γ) BS Γ₁ (TerminalProj (CtxToBSys AS Γ) Γ₁ ○ f) T t) ○ PreBSystem.wk Bᵇ T)
            ≡⟨ ○-assoc (TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'') (NeededSubstGen (CtxToBSys AS Γ) BS Γ₁ (TerminalProj (CtxToBSys AS Γ) Γ₁ ○ f) T t) (PreBSystem.wk Bᵇ T) ⟩
                TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'' ○ 
                    (NeededSubstGen (CtxToBSys AS Γ) BS Γ₁ (TerminalProj (CtxToBSys AS Γ) Γ₁ ○ f) T t ○ PreBSystem.wk Bᵇ T)
            ≡⟨ cong (λ x → (TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'' ○ x)) (NeededSubstGenTriv (CtxToBSys AS Γ) BS Γ₁ (TerminalProj (CtxToBSys AS Γ) Γ₁ ○ f) T t (○-homomorphism H (TerProjIsHomomorphism (CtxToBSys AS Γ) Γ₁))) ⟩
                TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'' ○ (TerminalProj (CtxToBSys AS Γ) Γ₁ ○ f)
            ≡⟨ sym (○-assoc (TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'') (TerminalProj (CtxToBSys AS Γ) Γ₁) f) ⟩
                (TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'' ○ TerminalProj (CtxToBSys AS Γ) Γ₁) ○ f                 
            ∎))
            ∙ 
            (cong (λ x → (transport (λ i → B ↝ TopTyTm++BSys (CtxToBSys AS Γ) Γ₁ Γ'' i) x)) (○-assoc (TerminalProj (CtxToBSys (CtxToBSys AS Γ) Γ₁) Γ'') (TerminalProj (CtxToBSys AS Γ) Γ₁) f))
            ∙  
            (fromPathP (symP (TerminalProjCompf (CtxToBSys AS Γ) Γ₁ Γ'' f)))

    Eq3DivergeTerm : {A : TyTmStr} {B : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} 
                {AS : BSystem A Aᵇ} {BS : BSystem B Bᵇ} {Γ : Ctx (BSystemToTyStr AS)} 
                {f : B ↝ (CtxToTyTmStr AS Γ)} {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))}
                {Δ' : Ctx (BSystemToTyStr BS)} (H : is-homomorphism Bᵇ (CtxToPreSys AS Γ) f)
                (ɣ : Subst (BSystemToDepPolyHelp AS BS Γ f) Γ' Δ') (T : TyTmStr.Typ B)
                → PathP (λ i → TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ')  (_↝_.Ty↝ (Eq3Diverge H ɣ i) T) → (TyTmStr.Slc B T) ↝ ((CtxToTyTmStr (CtxToBSys AS Γ) Γ'))) 
                (λ t → NeededSubstGen (CtxToBSys AS Γ) BS Γ' (SubstToHomHelp ɣ ○ (TerminalProj BS Δ')) T t) 
                λ t → NeededSubstGen (CtxToBSys AS Γ) BS Γ' (TerminalProj (CtxToBSys AS Γ) Γ' ○ f) T t
    Eq3DivergeTerm {AS = AS} {BS = BS} {Γ = Γ} {f = f} {Γ' = Γ'} H ɣ T i t = NeededSubstGen (CtxToBSys AS Γ) BS Γ' (Eq3Diverge H ɣ i) T t
    
    TransportEqBase : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ₁ : Ctx (BSystemToTyStr BS))
            (T : TyTmStr.Typ B) (t : TyTmStr.Tm (CtxToTyTmStr BS Γ₁) (_↝_.Ty↝ (TerminalProj BS Γ₁) T))
            {Γ' : Ctx (BSystemToTyStr (CtxToBSys BS Γ₁))} {Δ' : Ctx (BSystemToTyStr (BSystem.BSlc BS T))}
            (fst₂ : Subst (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) Γ₁ (NeededSubst BS Γ₁ T t)) Γ' Δ')
            → (transport (λ i → B ↝ TopTyTm++BSys BS Γ₁ Γ' i)
                ((SubstToHomHelp fst₂) ○ TerminalProj BS (T ► Δ'))) 
            ≡ (transport (λ i → TopTyTm (CtxPToCtxB (BSystem.BSlc BS T) Δ') ↝ TopTyTm++BSys BS Γ₁ Γ' i)
                (SubstToHomHelp fst₂) ○ TerminalProj BS (T ► Δ'))
    TransportEqBase BS Γ₁ T t {Γ'} {Δ'} fst₂ = transportSplit (TopTyTm++BSys BS Γ₁ Γ') (TerminalProj BS (T ► Δ')) (SubstToHomHelp fst₂)

    Eq3 : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (fst₁ : Ctx (BSystemToTyStr BS)) (Γ : Ctx (BSystemToTyStr BS)) 
         (fst₂ : Subst (BSystemToDepPoly BS) Γ fst₁)
         → ((SubstToHom fst₂) ○ (TerminalProj BS fst₁)) ≡ (TerminalProj BS Γ) 
    Eq3 BS fst₁ Γ (● .Γ) = IdStrRN (TerminalProj BS Γ)
    Eq3 {B} {Bᵇ} BS fst₁ Γ (cns Γ₁ T t Γ' Δ' fst₂) = (sym (TransportEqBase BS Γ₁ T t fst₂))
            ∙ 
            (cong (λ x → (transport (λ i → B ↝ (TopTyTm++BSys BS Γ₁ Γ' i)) x))
                (SubstToHomHelp fst₂ ○ (TerminalProj (BSystem.BSlc BS T) Δ' ○ (PreBSystem.wk Bᵇ T)) 
            ≡⟨ sym (○-assoc (SubstToHomHelp fst₂) (TerminalProj (BSystem.BSlc BS T) Δ') (PreBSystem.wk Bᵇ T)) ⟩   
                (SubstToHomHelp fst₂ ○ TerminalProj (BSystem.BSlc BS T) Δ') ○ PreBSystem.wk Bᵇ T
            ≡⟨ cong (λ x → x ○ (PreBSystem.wk Bᵇ T)) (Eq3Diverge (NeededSubstIsHomomorphism BS Γ₁ T t) fst₂) ⟩
                (TerminalProj (CtxToBSys BS Γ₁) Γ' ○ NeededSubst BS Γ₁ T t) ○ PreBSystem.wk Bᵇ T
            ≡⟨ ○-assoc (TerminalProj (CtxToBSys BS Γ₁) Γ') (NeededSubst BS Γ₁ T t) (PreBSystem.wk Bᵇ T) ⟩
                TerminalProj (CtxToBSys BS Γ₁) Γ' ○ (NeededSubst BS Γ₁ T t ○ PreBSystem.wk Bᵇ T)
            ≡⟨ cong (λ x → (TerminalProj (CtxToBSys BS Γ₁) Γ' ○ x)) (NeededSubstTriv BS Γ₁ T t) ⟩
                TerminalProj (CtxToBSys BS Γ₁) Γ' ○ (TerminalProj BS Γ₁) 
            ∎))
            ∙
            (fromPathP (symP (TerminalProjComp BS Γ₁ Γ')))


    h : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B}
      {Cᵇ : PreBSystem C} (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ)
      (CS : BSystem C Cᵇ) (Γ : Ctx (BSystemToTyStr AS))
      (Δ : Ctx (BSystemToTyStr BS))
      (f : CtxToTyTmStr BS Δ ↝ CtxToTyTmStr AS Γ)
      (g : C ↝ CtxToTyTmStr BS Δ)
      (H : is-homomorphism (CtxToPreSys BS Δ) (CtxToPreSys AS Γ) f)
      {Γ' : Ctx (BSystemToTyStr (CtxToBSys AS Γ))}
      {T = T' : Ty (BSystemToTyStr CS)}
      {fst₁ : Ctx (BSystemToTyStr (CtxToBSys BS Δ))}
      (fst₂
       : Subst (BSystemToDepPolyHelp AS (CtxToBSys BS Δ) Γ f) Γ' fst₁)
      (snd : Tm (BSystemToDepPolyHelp BS CS Δ g) fst₁ T') 
        → (SubstToHomHelp fst₂ ○ NeededSubstGen (CtxToBSys BS Δ) CS fst₁ (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T' snd) 
        ≡ (NeededSubstGen (CtxToBSys AS Γ) CS Γ' (TerminalProj (CtxToBSys AS Γ) Γ' ○ (f ○ g)) T' (transport
                    (λ i → TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ (Eq3Diverge H fst₂ i) (_↝_.Ty↝ g T')))
                    (_↝_.Tm↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')) snd)))
    h AS BS CS Γ Δ f g H {Γ' = Γ'} {T = T'} {fst₁ = fst₁} fst₂ snd = 
                    (sym (○-assoc (SubstToHomHelp fst₂) (PreBSystem.sub (CtxToPreSys (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T') snd)
                        (_↝_.Slc↝ (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T'))
                    ∙ 
                     cong (λ x → x ○ (_↝_.Slc↝ (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T')) (is-homomorphism.sub≡ (SubstToHomHelpIsHomomorphism fst₂ H) ((_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T'))) snd) 
                    ∙
                     ○-assoc (PreBSystem.sub (CtxToPreSys (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')))
                                    (_↝_.Tm↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')) snd))
                                    (_↝_.Slc↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')))
                                    (_↝_.Slc↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T') ○ _↝_.Slc↝ g T')
                    ∙
                    cong (λ x → (PreBSystem.sub (CtxToPreSys (CtxToBSys AS Γ) Γ')
                         (_↝_.Ty↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')))
                            (_↝_.Tm↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')) snd) ○ x))
                                (sym (○-assoc (_↝_.Slc↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')))
                                    (_↝_.Slc↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T'))
                                    (_↝_.Slc↝ g T'))))
                    ∙ 
                    (λ i → ((PreBSystem.sub (CtxToPreSys (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ ((Eq3Diverge H fst₂ i) ○ g) T')
                        ((transport-fillerExt (λ i₁ → TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ ((Eq3Diverge H fst₂ i₁) ○ g) T'))) i
                            (_↝_.Tm↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ ((TerminalProj (CtxToBSys BS Δ) fst₁) ○ g) T') snd)))
                                ○ (_↝_.Slc↝ ((Eq3Diverge H fst₂ i) ○ g) T')))
                    ∙ 
                    (cong (λ x → (PreBSystem.sub (CtxToPreSys (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ (TerminalProj (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ f (_↝_.Ty↝ g T')))
                        (transport (λ i₁ → TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ (Eq3Diverge H fst₂ i₁) (_↝_.Ty↝ g T')))
                            (_↝_.Tm↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')) snd)) ○ x)) 
                                (○-assoc (_↝_.Slc↝ (TerminalProj (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ f (_↝_.Ty↝ g T'))) (_↝_.Slc↝ f (_↝_.Ty↝ g T')) (_↝_.Slc↝ g T'))) 


    {-# TERMINATING #-}
    BSystemToMonad-μ-Help : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C}
                (AS : BSystem A Aᵇ) (BS : BSystem B Bᵇ) (CS : BSystem C Cᵇ) (Γ : Ctx (BSystemToTyStr AS))
                (Δ : Ctx (BSystemToTyStr BS))
                (f : (CtxToTyTmStr BS Δ) ↝ (CtxToTyTmStr AS Γ)) (g : C ↝ CtxToTyTmStr BS Δ) (H : is-homomorphism (CtxToPreSys BS Δ) (CtxToPreSys AS Γ) f)
            → BSystemToDepPolyHelp AS (CtxToBSys BS Δ) Γ f ⊚ BSystemToDepPolyHelp BS CS Δ g ⇒ BSystemToDepPolyHelp AS CS Γ (f ○ g)
    BSystemToMonad-μ-Help AS BS CS Γ Δ f g H .Tm⇒ {Γ'} {T'} (fst₁ , fst₂ , snd₁) = transport (λ i → (TyTmStr.Tm (CtxToTyTmStr (CtxToBSys AS Γ) Γ') (_↝_.Ty↝ (Eq3Diverge H fst₂ i) (_↝_.Ty↝ g T'))))
             (_↝_.Tm↝ (SubstToHomHelp fst₂) (_↝_.Ty↝ (TerminalProj (CtxToBSys BS Δ) fst₁) (_↝_.Ty↝ g T')) snd₁)
    BSystemToMonad-μ-Help AS BS CS Γ Δ f g H .⇑⇒ {Γ'} {T'} (fst₁ , fst₂ , snd₁) = transport
            (cong (λ x → ⌈ fst₂ ⌉s ⊚ BSystemToDepPolyHelp (CtxToBSys BS Δ) (BSystem.BSlc CS T') fst₁ (NeededSubstGen (CtxToBSys BS Δ) CS fst₁
                (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T' snd₁)  ⇒ BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc CS T') Γ' x) (h AS BS CS Γ Δ f g H fst₂ snd₁))
            (transport (cong (λ x → x ⊚ BSystemToDepPolyHelp (CtxToBSys BS Δ) (BSystem.BSlc CS T') fst₁ (NeededSubstGen (CtxToBSys BS Δ) CS fst₁
                (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T' snd₁) ⇒ BSystemToDepPolyHelp (CtxToBSys AS Γ) (BSystem.BSlc CS T') Γ'
                (SubstToHomHelp fst₂ ○  NeededSubstGen (CtxToBSys BS Δ) CS fst₁ (TerminalProj (CtxToBSys BS Δ) fst₁ ○ g) T' snd₁)) (sym (SubstToHomEqHelp fst₂)))
            (BSystemToMonad-μ-Help (CtxToBSys AS Γ) (CtxToBSys BS Δ) (BSystem.BSlc CS T') Γ' fst₁ (SubstToHomHelp fst₂)
                (NeededSubstGen (CtxToBSys BS Δ) CS fst₁ ((TerminalProj (CtxToBSys BS Δ) fst₁) ○ g) T' snd₁) (SubstToHomHelpIsHomomorphism fst₂ H)))

    hBase : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) {Γ : Ctx (BSystemToTyStr BS)} (T : TyTmStr.Typ B) {fst₁ : Ctx (BSystemToTyStr BS)}
            (fst₂ : Subst (BSystemToDepPoly BS) Γ fst₁) (snd₁ : TyTmStr.Tm (CtxToTyTmStr BS fst₁) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
            → ((SubstToHom fst₂ ○ NeededSubst BS fst₁ T snd₁))
                ≡ (NeededSubst BS Γ T (transport
                    (λ i → TyTmStr.Tm (TopTyTm (CtxPToCtxB BS Γ)) (_↝_.Ty↝ (Eq3 BS fst₁ Γ fst₂ i) T))
                        (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)))
    hBase BS {Γ} T {fst₁} fst₂ snd₁ = 
                (SubstToHom fst₂ ○ NeededSubst BS fst₁ T snd₁)
            ≡⟨ sym (○-assoc (SubstToHom fst₂) (PreBSystem.sub (CtxToPreSys BS fst₁) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁) (_↝_.Slc↝(TerminalProj BS fst₁) T)) ⟩
                (SubstToHom fst₂ ○ (PreBSystem.sub (CtxToPreSys BS fst₁) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)) ○ (_↝_.Slc↝(TerminalProj BS fst₁) T)
            ≡⟨ cong (λ x → x ○ (_↝_.Slc↝ (TerminalProj BS fst₁) T)) (is-homomorphism.sub≡ (SubstToHomHomomorphism fst₂) ((_↝_.Ty↝ (TerminalProj BS fst₁) T)) snd₁) ⟩
                (PreBSystem.sub (CtxToPreSys BS Γ)  (_↝_.Ty↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T)) (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)
                    ○ _↝_.Slc↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
                        ○ _↝_.Slc↝ (TerminalProj BS fst₁) T
            ≡⟨ ○-assoc (PreBSystem.sub (CtxToPreSys BS Γ)  (_↝_.Ty↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T)) (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁))
                    (_↝_.Slc↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T)) (_↝_.Slc↝ (TerminalProj BS fst₁) T) ⟩
                PreBSystem.sub (CtxToPreSys BS Γ)  (_↝_.Ty↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T)) (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)
                    ○ ((_↝_.Slc↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T))
                        ○ (_↝_.Slc↝ (TerminalProj BS fst₁) T))
            ≡⟨ refl ⟩
                PreBSystem.sub (CtxToPreSys BS Γ)  (_↝_.Ty↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T)) (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)
                    ○ (_↝_.Slc↝ ((SubstToHom fst₂) ○ (TerminalProj BS fst₁)) T)
            ≡⟨ (λ i → (PreBSystem.sub (CtxToPreSys BS Γ) (_↝_.Ty↝ (Eq3 BS fst₁ Γ fst₂ i) T) 
                    (transport-fillerExt (λ i → TyTmStr.Tm (TopTyTm (CtxPToCtxB BS Γ)) (_↝_.Ty↝ (Eq3 BS fst₁ Γ fst₂ i) T)) i (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)))
                        ○ (_↝_.Slc↝ (Eq3 BS fst₁ Γ fst₂ i) T)) ⟩  
                    NeededSubst BS Γ T    
                        (transport (λ i → TyTmStr.Tm (TopTyTm (CtxPToCtxB BS Γ)) (_↝_.Ty↝ (Eq3 BS fst₁ Γ fst₂ i) T))
                            (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁))                      
             ∎        

    BSystemToMonad-μ : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (BSystemToDepPoly BS ⊚ BSystemToDepPoly BS ⇒ BSystemToDepPoly BS)
    BSystemToMonad-μ BS .Tm⇒ {Γ} {T} (fst₁ , fst₂ , snd₁) = transport (λ i → (TyTmStr.Tm (TopTyTm (CtxPToCtxB BS Γ)) (_↝_.Ty↝ (Eq3 BS fst₁ Γ fst₂ i) T))) (_↝_.Tm↝ (SubstToHom fst₂) (_↝_.Ty↝ (TerminalProj BS fst₁) T) snd₁)
    BSystemToMonad-μ BS .⇑⇒  {Γ} {T} (fst₁ , fst₂ , snd₁) = transport (cong₂ (λ x y → x ⊚ BSystemToDepPolyHelp BS (BSystem.BSlc BS T) fst₁ (NeededSubst BS fst₁ T snd₁) ⇒ BSystemToDepPolyHelp BS (BSystem.BSlc BS T) Γ y)
            (sym (SubstToHomEq1 fst₂)) (hBase BS T fst₂ snd₁)) 
            (BSystemToMonad-μ-Help  BS BS (BSystem.BSlc BS T) Γ fst₁ (SubstToHom fst₂) (NeededSubst BS fst₁ T snd₁) (SubstToHomHomomorphism fst₂))




    -- this is all written to work without the rewrite

    -- !!! The η definition needs to be reworked since I simplified BSystemToDepPolyHelp to take the already sliced BSystem and not the original BSystem and a type !!!
    -- !!! This hopeully simplifies μ but probably implies one needs to rework some of the equalities !!!

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
                (proj-slc (EqTerProj BS T) T) ⟩
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
            → (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (idStr (TyTmStr.Slc B T)))
            ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    DepPolyHelpIsTrivialStep BS T i .Tm x x₁ = refl {x = TyTmStr.Tm (CtxToTyTmStr (BSystem.BSlc BS T) x) (_↝_.Ty↝ (TerminalProj (BSystem.BSlc BS T) x) x₁)} i
    DepPolyHelpIsTrivialStep BS T i .⇑ {Γ} {T'} t =  BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc (BSystem.BSlc BS T) T') Γ (DepPolyHelpIsTrivialHom BS T Γ T' t i)


            -- cong (λ x → transport (λ i₁ →
            -- DepPoly (⌈ BSystem.BSlc BS T ⌉BSysEqual Γ (~ i₁)) (BSystemToTyStr (BSystem.BSlc (BSystem.BSlc BS T) T')))
            -- (BSystemToDepPolyHelp (BSystem.BSlc BS T) (BSystem.BSlc (BSystem.BSlc BS T) T') Γ x))(DepPolyHelpIsTrivialHom BS T Γ T' t ) i


    -- This is the central equality since we can then reduce DepPolyHelp to BSystemToDepPoly BS and recursively apply BSystemToMonad-η

    DepPolyHelpIsTrivial : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
            → (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
                ≡ BSystemToDepPoly (BSystem.BSlc BS T)
    DepPolyHelpIsTrivial {B} {Bᵇ} BS T = (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
        ≡⟨ cong (λ x → BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) x) (NeededSubstIsID BS T) ⟩
            (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (idStr (TyTmStr.Slc B T)))
        ≡⟨ DepPolyHelpIsTrivialStep BS T ⟩      
            BSystemToDepPoly (BSystem.BSlc BS T)
        ∎ 


    -- needed to get rid of the constant transport introduced by BSystemToDepPolyHelp
    Eq-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : TyTmStr.Typ B)
        → IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
            transport (λ i →
            DepPoly (BSystemToTyStr (BSystem.BSlc BS T)) (BSystemToTyStr (BSystem.BSlc BS T)))
            (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T)))
        ≡ IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒
            BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))
    Eq-η {Bᵇ = Bᵇ} BS T = cong (λ x → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T)) ⇒ x)) 
        (transportRefl (BSystemToDepPolyHelp BS (BSystem.BSlc BS T) (T ► ϵ) (NeededSubst BS (T ► ϵ) T (PreBSystem.var Bᵇ T))))


    {-# TERMINATING #-}
    BSystemToMonad-η : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) 
        → IdPoly (BSystemToTyStr BS) ⇒ BSystemToDepPoly BS
    BSystemToMonad-η {Bᵇ = Bᵇ} BS .Tm⇒ {Γ} {T} (idT .T) = PreBSystem.var Bᵇ T
    BSystemToMonad-η BS .⇑⇒ {Γ} {T} (idT _) = (transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (DepPolyHelpIsTrivial BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)))

    -- (Iso.fun (pathToIso (sym (Eq-η BS T))))     
    --     (transport (λ i → (IdPoly (BSystemToTyStr (BSystem.BSlc BS T))) ⇒ (DepPolyHelpIsTrivial BS T (~ i))) (BSystemToMonad-η (BSystem.BSlc BS T)))


    BSystemToMonad : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) → (Monad (BSystemToTyStr BS))
    BSystemToMonad BS .Monad.P = BSystemToDepPoly BS
    BSystemToMonad BS .Monad.μ = BSystemToMonad-μ BS
    BSystemToMonad {Bᵇ = Bᵇ} BS .Monad.η = BSystemToMonad-η BS
        
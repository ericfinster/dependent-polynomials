open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import Monad
open import PolyTheory

open import BSystems

module PolyTheoryToBSys where

    open PolyTheory.PolyTheory public
    open Monad.Monad public
    open SubStr public
    open WkPoly public
    open WknStr public
    open TyTmStr public

    DepPolyToTyTmLift : {𝕊 𝕋 : TyStr} (I : Type) (P : I → DepPoly 𝕊 𝕋) → TyTmStr
    DepPolyToTyTmLift {𝕋 = 𝕋} I P₁ .TyTmStr.Typ = Ty 𝕋
    DepPolyToTyTmLift I P₁ .TyTmStr.Tm x = (i : I) → (Tm (P₁ i) ϵ x)
    DepPolyToTyTmLift I P₁ .TyTmStr.Slc x = DepPolyToTyTmLift  (Σ[ i ∈ I ] (Tm (P₁ i) ϵ x)) (λ t → (⇑ (P₁ (fst t)) (snd t)))

    DepPolyToTyTm : {𝕊 𝕋 : TyStr} (P : DepPoly 𝕊 𝕋) → TyTmStr
    DepPolyToTyTm {𝕋 = 𝕋} P₁ .TyTmStr.Typ = Ty 𝕋
    DepPolyToTyTm P₁ .TyTmStr.Tm x = Tm P₁ ϵ x
    DepPolyToTyTm P₁ .TyTmStr.Slc x = DepPolyToTyTmLift (Tm P₁ ϵ x) λ t → (⇑ P₁ t) 

    DepPolyToTyTm2 : {𝕊 𝕋 : TyStr} (P : DepPoly 𝕊 𝕋) → TyTmStr
    DepPolyToTyTm2 {𝕋 = 𝕋} P₁ .TyTmStr.Typ = Ty 𝕋
    DepPolyToTyTm2 P₁ .TyTmStr.Tm x = Tm P₁ ϵ x
    DepPolyToTyTm2 P₁ .TyTmStr.Slc x = {! ΠStructure {Tm P₁ ϵ x} (λ t → (DepPolyToTyTm ))  !}

    TheoryToTyTmStr : {𝕋 : TyStr} → PolyTheory 𝕋 → TyTmStr
    TheoryToTyTmStr x = DepPolyToTyTm (P (M x)) 

    TheoryToPreBSub : {𝕋 : TyStr} (x : PolyTheory 𝕋) (T : TyTmStr.Typ (TheoryToTyTmStr x)) (t : Tm (TheoryToTyTmStr x) T) → Slc (TheoryToTyTmStr x) T ↝ (TheoryToTyTmStr x)
    TheoryToPreBSub x T t ._↝_.Ty↝ x₁ = SubStrCtx (SubS x) x₁ t
    TheoryToPreBSub x T t ._↝_.Tm↝ T₁ x₁ = {!   !}
    TheoryToPreBSub x T t ._↝_.Slc↝ T₁ = {!   !}

    TheoryToPreBSys : {𝕋 : TyStr} (x : PolyTheory 𝕋) 
      → PreBSystem (TheoryToTyTmStr x)
    TheoryToPreBSys x .PreBSystem.wk T ._↝_.Ty↝ x₁ = WkAB (WkS x) T x₁
    TheoryToPreBSys x .PreBSystem.wk T ._↝_.Tm↝ T₁ x₁ i = WkSub (WkS x) T T₁ x₁ i
    TheoryToPreBSys x .PreBSystem.wk T ._↝_.Slc↝ = {!   !}
    TheoryToPreBSys x .PreBSystem.sub T t ._↝_.Ty↝ x₁ = SubStrCtx (SubS x) x₁ t
    TheoryToPreBSys x .PreBSystem.sub T t ._↝_.Tm↝ T₁ x₁ = {! Sublift (SubS x) T₁ t (Subst⇒ (η (M x)) (idSubst ϵ)) ϵ   !}
    TheoryToPreBSys x .PreBSystem.sub T t ._↝_.Slc↝ = {!   !}
    TheoryToPreBSys x .PreBSystem.var T i = WkSub (WkS x) T T i i -- (wk ((WkP (WkS x))) ϵ T T i)
    TheoryToPreBSys x .PreBSystem.slc T = {!   !}
    
    
    -- x .PreBSystem.wk T ._↝_.Ty↝ x₁ .fst = {!   !}
    -- TheoryToPreBSys x .PreBSystem.wk T ._↝_.Ty↝ x₁ .snd = WkAB (WkS x) T x₁
    -- TheoryToPreBSys x .PreBSystem.wk T ._↝_.Tm↝ T₁ x₁ = {! Wkt (WkS x) T T₁  !}
    -- TheoryToPreBSys x .PreBSystem.wk T ._↝_.Slc↝ T₁ = {!   !}
    -- TheoryToPreBSys x .PreBSystem.sub T t ._↝_.Ty↝ x₁ = SubStrCtx (SubS x) (snd x₁) t
    -- TheoryToPreBSys x .PreBSystem.sub T t ._↝_.Tm↝ T₁ x₁ = {!  SubStrTm (SubS x) (snd T₁) t !} -- SubStrTm (SubS x) (snd T₁) t  (cns ϵ T₁ x₁ ϵ ϵ (● ϵ))
    -- TheoryToPreBSys x .PreBSystem.sub T t ._↝_.Slc↝ T₁ = {!   !}
    -- TheoryToPreBSys x .PreBSystem.var T = {! Tm⇒ (η (M x)) (idT T) !}
    -- TheoryToPreBSys x .PreBSystem.slc = {!   !}    
open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import Monad
open import PolyTheory

open import BSystems

open import ToBSys

module PolyTheoryToBSys where

    open PolyTheory.PolyTheory public
    open Monad.Monad public
    open SubStr public
    open WkPoly public
    open WkStr public

    {-# TERMINATING #-}
    DPolyToTyTm : {𝕋 : TyStr} → DepPoly 𝕋 𝕋 → TyTmStr
    DPolyToTyTm {𝕋} x .TyTmStr.Typ = Ty 𝕋
    DPolyToTyTm x .TyTmStr.Tm x₁ = Tm x (x₁ ► ϵ) x₁
    DPolyToTyTm x .TyTmStr.Slc x₁ = ΣStructure {Tm x (x₁ ► ϵ) x₁} (λ t → DPolyToTyTm (⇑ x t)) 

    DepPolyToTyTm2 : {𝕋 : TyStr} → DepPoly 𝕋 𝕋 → TyTmStr
    DepPolyToTyTm2 {𝕋} x .TyTmStr.Typ = Ty 𝕋
    DepPolyToTyTm2 x .TyTmStr.Tm x₁ = {!   !}
    DepPolyToTyTm2 x .TyTmStr.Slc x₁ = {! ΣStructure {Tm x ϵ x₁} (λ t →  DPolyToTyTm (⇑ x t))  !}

    DepPolyToTyTm2Div : {𝕋 𝕊 : TyStr} → DepPoly 𝕊 𝕋 → TyTmStr
    DepPolyToTyTm2Div {𝕋} x .TyTmStr.Typ = Ty 𝕋
    DepPolyToTyTm2Div x .TyTmStr.Tm = {!   !}
    DepPolyToTyTm2Div x .TyTmStr.Slc = {!   !}

    DepPolyToTyTm3 : {𝕋 : TyStr} → DepPoly 𝕋 𝕋 → TyTmStr
    DepPolyToTyTm3 {𝕋} x .TyTmStr.Typ = Ty (CtxStr 𝕋)
    DepPolyToTyTm3 x .TyTmStr.Tm x₁ = {!   !}
    DepPolyToTyTm3 x .TyTmStr.Slc = {!   !}

    -- pretty sure this is wrong, since I'd need to guarantee a term for every combination of Γ T for wk to work
    TheoryToTyTmStr : {𝕋 : TyStr} → PolyTheory 𝕋 → TyTmStr
    TheoryToTyTmStr x = DPolyToTyTm (P (M x)) 

    TheoryToPreBSys : {𝕋 : TyStr} (x : PolyTheory 𝕋) 
      → PreBSystem (TheoryToTyTmStr x)
    TheoryToPreBSys x .wk T ._↝_.Ty↝ x₁ .fst = Tm⇒ (η (M x)) (idT T)
    TheoryToPreBSys x .wk T ._↝_.Ty↝ x₁ .snd = ty (wk (wkStr (WkS x)) T) x₁
    TheoryToPreBSys x .wk T ._↝_.Tm↝ T₁ x₁ = {! wk (WkS x) (T₁ ► ϵ) T₁ (ty (wk (wkStr (WkS x)) T₁) T) x₁   !}
    TheoryToPreBSys x .wk T ._↝_.Slc↝ = {!   !}
    TheoryToPreBSys x .sub T t ._↝_.Ty↝ (fst₁ , snd₁) = {!   !}
    TheoryToPreBSys x .sub T t ._↝_.Tm↝ = {!   !}
    TheoryToPreBSys x .sub T t ._↝_.Slc↝ = {!   !} 
    TheoryToPreBSys x .var = {!   !} 
    TheoryToPreBSys x .slc = {!   !} 
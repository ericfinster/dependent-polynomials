open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma

open import TyStr
open import BSystems
open import DepPoly
open import Monad
open import BSystemToMonad
open import BSystemToDepPoly

module ToBSys where 

    {-# TERMINATING #-}
    DepPolyToTyTm : {S T : TyStr} (P : DepPoly S T) → TyTmStr
    DepPolyToTyTm {S} {T} P .TyTmStr.Typ = (TyStr.Ty (CtxStr S)) × (TyStr.Ty T)
    DepPolyToTyTm P .TyTmStr.Tm (Γ , T) = DepPoly.Tm P Γ T
    DepPolyToTyTm {T = T} P .TyTmStr.Slc (Γ , T') = ΣStructure {Tm P Γ T'} (λ t → (DepPolyToTyTm (DepPoly.⇑ P t)))

    -- I think wk needs to be postulated for the TyStr
    -- I'll expect subst to be μ 
    -- var should be η
    MonadToPreSys : {T : TyStr} (M : Monad T) → (PreBSystem (DepPolyToTyTm (Monad.P M)))
    MonadToPreSys M .PreBSystem.wk T ._↝_.Ty↝ (fst₁ , snd₁) = {!  !}
    MonadToPreSys M .PreBSystem.wk T ._↝_.Tm↝ = {!   !}
    MonadToPreSys M .PreBSystem.wk T ._↝_.Slc↝ = {!   !}
    MonadToPreSys M .PreBSystem.sub T t = {! ⇑ (Monad.P M) t   !}
    MonadToPreSys M .PreBSystem.var T = {!    !}
    MonadToPreSys M .PreBSystem.slc = {!   !}  

    BSysMonadToPreSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ)
        → (PreBSystem (DepPolyToTyTm (Monad.P (BSystemToMonad BS))))
    BSysMonadToPreSys BS .PreBSystem.wk T = {!   !}
    BSysMonadToPreSys BS .PreBSystem.sub = {!   !} 
    BSysMonadToPreSys BS .PreBSystem.var = {!   !}
    BSysMonadToPreSys BS .PreBSystem.slc = {!   !} 
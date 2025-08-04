open import Cubical.Foundations.Prelude
-- open import Cubical.Data.Prod
open import Cubical.Data.Sigma

open import TyStr
open import BSystems
open import DepPoly

module ToBSys where 

    {-# TERMINATING #-}
    DepPolyToTyTm : {S T : TyStr} (P : DepPoly S T) → TyTmStr
    DepPolyToTyTm {S} {T} P .TyTmStr.Typ = (TyStr.Ty (CtxStr S)) × (TyStr.Ty T)
    DepPolyToTyTm P .TyTmStr.Tm (Γ , T) = DepPoly.Tm P Γ T
    DepPolyToTyTm {T = T} P .TyTmStr.Slc (Γ , T') = ΣStructure {Tm P Γ T'} (λ t → (DepPolyToTyTm (DepPoly.⇑ P t)))  
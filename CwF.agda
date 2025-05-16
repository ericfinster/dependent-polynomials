open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly

module CwF where

  record CwF : Type₁ where
    field
      Ob : Type
      Hom : Ob → Ob → Type

      𝕋y : Ob → Type
      [_]ty : (Γ Δ : Ob) (σ : Hom Γ Δ) → 𝕋y Δ → 𝕋y Γ

      Ext : (Γ : Ob) → 𝕋y Γ → Ob 

      𝟙 : Ob 

  open CwF

  postulate

    CwF-slice : (C : CwF) → Ob C → CwF

  CwFToTyStr : (C : CwF) → TyStr
  CwFToTyStr C .Ty = 𝕋y C (𝟙 C)
  CwFToTyStr C ._//_ T = CwFToTyStr (CwF-slice C (Ext C (𝟙 C) T))

  postulate
  
    CwFToDepPoly : (C : CwF) → DepPoly (CwFToTyStr C) (CwFToTyStr C)


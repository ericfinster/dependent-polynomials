
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Nat.Base

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Presheaf 
open import Cubical.Categories.Constructions.Elements 
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Functor
open import Cubical.Data.Bool

open import TCategory -- Categories with a terminal object
open import TyStr
open import DepPoly
open import CwFH
open import CwFHToDepPoly
open import Contextual

module ContextualToDepPoly where

    ContextualToTyStr : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} {CwFH : CwFH Ctxt T} (CwF : (Contextual CwFH)) → TyStr
    ContextualToTyStr {CwFH = CwFH} CwF = CwFHToDepPoly.CwFHToTyStr CwFH


    {-# TERMINATING #-}
    ObjToCtxtCont : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} {CwFH : CwFH Ctxt T} (CwF : (Contextual CwFH))
            → (Γ : Ctxt .ob) → {n : ℕ} → (ɣ : ((Contextual.length CwF Γ) ≡ n)) → (Ctx (ContextualToTyStr CwF))
    ObjToCtxtCont {ℓ} {Ctxt} {T} {CwFH₁} CwF Γ {zero} ɣ = ϵ
    ObjToCtxtCont {ℓ} {Ctxt} {T} {CwFH₁} CwF Γ {suc n} ɣ = (ObjToCtxtCont CwF (Contextual.PredOb CwF ɣ) (refl {x = (Contextual.length CwF (Contextual.PredOb CwF ɣ))})) ++ ({! Contextual.PredTy CwF ɣ  !} ► ϵ)


    -- data Ctx (𝕋 : TyStr) : Type where
    -- ϵ : Ctx 𝕋 
    -- _►_ : (T : Ty 𝕋) → (Γ : Ctx (𝕋 // T)) → Ctx 𝕋 

    -- _++_ : {𝕋 : TyStr} → (Γ : Ctx 𝕋) → Ctx ⌈ Γ ⌉ → Ctx 𝕋
    -- _++_ ϵ Δ = Δ
    -- _++_ (T ► Γ) Δ = T ► Γ ++ Δ
    

open import Cubical.Foundations.Prelude 

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Presheaf 
open import Cubical.Categories.Constructions.Elements 
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Functor

open import TCategory -- Categories with a terminal object
open import TyStr
open import DepPoly

open Category
open Contravariant

module CwFH where -- like in Hoffmann Syntax and Semantics of dependent Type Theory

    open Category 

    record CwFH {ℓ ℓ' : Level} (Ctxt : (Category ℓ ℓ')) (T : TCategory Ctxt) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) ℓ) ℓ') where
        field
            TyP : (ob Ctxt) → Type
            TmP : {Γ : (ob Ctxt)} (A : TyP Γ) → Type
            TyPm : {Γ Δ : (ob Ctxt)} (f : Ctxt [ Γ , Δ ]) → (TyP Δ → TyP Γ)
            TmPm : {Γ Δ : (ob Ctxt)} (f : Ctxt [ Γ , Δ ]) →  (σ : TyP Δ) → (TmP σ → (TmP (TyPm f σ)))
            TyPmId : {Γ : (ob Ctxt)} (σ : TyP Γ) → TyPm (Ctxt .id {x = Γ}) σ ≡ σ
            TyPmComp : {Γ Δ Φ : Ctxt .ob} (σ : TyP Φ) (f : Ctxt [ Γ , Δ ]) → (g : Ctxt [ Δ , Φ ]) → (TyPm f ((TyPm g) σ)) ≡ (TyPm (Ctxt ._⋆_ f g) σ)
            TmPmId : {Γ : ob Ctxt} {σ : TyP Γ} (tm : TmP σ) → subst (λ σ′ → TmP σ′) (TyPmId σ) (TmPm (Ctxt .id {x = Γ}) σ tm) ≡ tm
            TmPmComp : {Γ Δ Φ : Ctxt .ob} {σ : TyP Φ} (tm : TmP σ) (f : Ctxt [ Γ , Δ ]) → (g : Ctxt [ Δ , Φ ]) → subst (λ σ' → TmP σ') (TyPmComp σ f g) (TmPm f (TyPm g σ) (TmPm g σ tm)) ≡ TmPm (Ctxt ._⋆_ f g) σ tm
            cextOb : (Γ : Ctxt .ob) → (σ : TyP Γ) → (Ctxt .ob)
            cextHom1 : {Γ : Ctxt .ob} (σ : TyP Γ) → Ctxt [ (cextOb Γ σ) , Γ ] 
            cextHom2 : {Γ : Ctxt .ob} (σ : TyP Γ) → (TmP (TyPm (cextHom1 σ) σ))
            cextHomM : {Γ Δ : Ctxt .ob} (f : Ctxt [ Γ , Δ ]) → {σ : TyP Δ} → (M : TmP (TyPm f σ)) → Ctxt [ Γ , (cextOb Δ σ) ]
            ConsL : {Γ Δ : Ctxt .ob} {σ : TyP Δ} (f : Ctxt [ Γ , Δ ]) → (M : TmP (TyPm f σ)) → f ≡ Ctxt ._⋆_ (cextHomM f M) (cextHom1 σ)
            ConsR : {Γ Δ : ob Ctxt} → {σ : TyP Δ} → (f : Ctxt [ Γ , Δ ]) → (M : TmP (TyPm f σ)) 
                → subst (λ τ → TmP τ) (  TyPmComp σ (cextHomM f M) (cextHom1 σ) ∙ cong (λ h → TyPm h σ) (sym (ConsL f M))) (TmPm (cextHomM f M) (TyPm (cextHom1 σ) σ) (cextHom2 σ)) ≡ M
            ConsNat : {Γ Δ B : Ctxt .ob} (f : Ctxt [ Γ , Δ ]) → (g : Ctxt [ B , Γ ]) →  {σ : TyP Δ} → (M : TmP (TyPm f σ)) → (Ctxt ._⋆_ g  (cextHomM f M)) ≡ cextHomM (Ctxt ._⋆_ g f) (subst (λ σ' → TmP σ') (TyPmComp σ g f) (TmPm g (TyPm f σ) M))   
            ConsId : {Γ Δ : Ctxt .ob} (f : Ctxt [ Γ , Δ ]) → (σ : TyP Δ) → cextHomM (cextHom1 σ) (cextHom2 σ) ≡ Ctxt .id {x = cextOb Δ σ} 
            -- ((TmPm (cextHomM f M) ((TyPm (cextHom1 σ)) σ)) (cextHom2 σ)) ≡ M







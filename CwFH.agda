{-# OPTIONS --allow-unsolved-metas #-}

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
            TyPmComp : {Γ Δ Φ : Ctxt .ob} (σ : TyP Φ) (f : Ctxt [ Γ , Δ ]) → (g : Ctxt [ Δ , Φ ]) 
                    → (TyPm f ((TyPm g) σ)) ≡ (TyPm (Ctxt ._⋆_ f g) σ)
            TmPmId : {Γ : ob Ctxt} {σ : TyP Γ} (tm : TmP σ) → subst (λ σ′ 
                    → TmP σ′) (TyPmId σ) (TmPm (Ctxt .id {x = Γ}) σ tm) ≡ tm
            TmPmComp : {Γ Δ Φ : Ctxt .ob} {σ : TyP Φ} (tm : TmP σ) (f : Ctxt [ Γ , Δ ]) → (g : Ctxt [ Δ , Φ ]) 
                    → subst (λ σ' → TmP σ') (TyPmComp σ f g) (TmPm f (TyPm g σ) (TmPm g σ tm)) ≡ TmPm (Ctxt ._⋆_ f g) σ tm
            cextOb : (Γ : Ctxt .ob) → (σ : TyP Γ) → (Ctxt .ob)
            cextHom1 : {Γ : Ctxt .ob} (σ : TyP Γ) → Ctxt [ (cextOb Γ σ) , Γ ] 
            cextHom2 : {Γ : Ctxt .ob} (σ : TyP Γ) → (TmP (TyPm (cextHom1 σ) σ))
            cextHomM : {Γ Δ : Ctxt .ob} (f : Ctxt [ Γ , Δ ]) → {σ : TyP Δ} → (M : TmP (TyPm f σ)) → Ctxt [ Γ , (cextOb Δ σ) ]
            ConsL : {Γ Δ : Ctxt .ob} {σ : TyP Δ} (f : Ctxt [ Γ , Δ ]) → (M : TmP (TyPm f σ)) 
                    → f ≡ Ctxt ._⋆_ (cextHomM f M) (cextHom1 σ)
            ConsR : {Γ Δ : ob Ctxt} → {σ : TyP Δ} → (f : Ctxt [ Γ , Δ ]) → (M : TmP (TyPm f σ)) 
                    → subst (λ τ → TmP τ) (  TyPmComp σ (cextHomM f M) (cextHom1 σ) 
                    ∙ cong (λ h → TyPm h σ) (sym (ConsL f M))) (TmPm (cextHomM f M) (TyPm (cextHom1 σ) σ) (cextHom2 σ)) ≡ M
            ConsNat : {Γ Δ B : Ctxt .ob} (f : Ctxt [ Γ , Δ ]) → (g : Ctxt [ B , Γ ]) →  {σ : TyP Δ} → (M : TmP (TyPm f σ)) 
                    → (Ctxt ._⋆_ g  (cextHomM f M)) 
                        ≡ cextHomM (Ctxt ._⋆_ g f) (subst (λ σ' → TmP σ') (TyPmComp σ g f) (TmPm g (TyPm f σ) M))   
            ConsId : {Γ Δ : Ctxt .ob} (f : Ctxt [ Γ , Δ ]) → (σ : TyP Δ) 
                    → cextHomM (cextHom1 σ) (cextHom2 σ) ≡ Ctxt .id {x = cextOb Δ σ} 

    open CwFH
    open Category public

    CwFHId : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) → (CwFH Ctxt T)
    CwFHId CwF = CwF

    CwFHTerminal : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) 
            → {Γ : Ctxt .ob} → (Ty : CwF .TyP Γ) → (TCategory (SliceCat Ctxt (cextOb CwF Γ Ty))) 
    CwFHTerminal {T = T} CwF {Γ = Γ} Ty₁ = TCat-Slice (cextOb CwF Γ Ty₁) T


    CwFHslice : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) 
            → {Γ : Ctxt .ob} → (Ty : CwF .TyP Γ) → (CwFH (SliceCat Ctxt (cextOb CwF Γ Ty)) (CwFHTerminal CwF Ty))
    CwFHslice CwF Ty₁ .TyP x = TyP CwF (S-ob x)
    CwFHslice CwF Ty₁ .TmP A = TmP CwF A
    CwFHslice CwF Ty₁ .TyPm f x = (TyPm CwF (S-hom f)) x
    CwFHslice CwF Ty₁ .TmPm f σ x = (TmPm CwF (S-hom f) σ) x
    CwFHslice CwF Ty₁ .TyPmId σ = TyPmId CwF σ
    CwFHslice CwF Ty₁ .TyPmComp σ f g = TyPmComp CwF σ (S-hom f) (S-hom g)
    CwFHslice CwF Ty₁ .TmPmId tm = TmPmId CwF tm
    CwFHslice CwF Ty₁ .TmPmComp tm f g = TmPmComp CwF tm (S-hom f) (S-hom g)
    CwFHslice {Ctxt = Ctxt} CwF Ty₁ .cextOb Γ σ = sliceob (Ctxt ._⋆_ (CwF .cextHom1 σ) (S-arr Γ))
    CwFHslice CwF Ty₁ .cextHom1 σ = slicehom (CwF .cextHom1 σ) refl
    CwFHslice CwF Ty₁ .cextHom2 σ = CwF .cextHom2 σ
    CwFHslice {ℓ} {ℓ'} {Ctxt = Ctxt} {T} CwF Ty₁ .cextHomM {Γ} {Δ} f {σ} M = 
        slicehom (cextHomM CwF ((S-hom f)) M) 
        ((sym (⋆Assoc Ctxt (cextHomM CwF (S-hom f) M) (cextHom1 CwF σ) (S-arr Δ))) ∙ 
        (⟨_⟩⋆⟨_⟩ Ctxt (sym (CwF .ConsL (S-hom f) M)) (refl {x = S-arr Δ})) ∙ (S-comm f))
    CwFHslice {Ctxt = Ctxt} CwF {Γ = Γ} Ty₁ .ConsL f M = SliceHom-≡-intro' Ctxt (cextOb CwF Γ Ty₁) (ConsL CwF ((S-hom f)) M)
    CwFHslice CwF Ty₁ .ConsR f M = ConsR CwF ((S-hom f)) M
    CwFHslice {Ctxt = Ctxt} CwF {Γ = Γ} Ty₁ .ConsNat f g M = SliceHom-≡-intro' Ctxt (cextOb CwF Γ Ty₁) ((ConsNat CwF (S-hom f) (S-hom g) M))
    CwFHslice {Ctxt = Ctxt} CwF {Γ = Γ} Ty₁ .ConsId f σ = SliceHom-≡-intro' Ctxt (cextOb CwF Γ Ty₁) (ConsId CwF (S-hom f) σ)


        -- Probably not needed but maybe nice to have, slices over the object itself not over the Ctxt Extension as CwFHSlice does
    CwFHSliceHelp : {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) 
            → (Γ : Ctxt .ob) → (CwFH (SliceCat Ctxt Γ) (TCat-Slice Γ T))
    CwFHSliceHelp CwF Γ .TyP x = TyP CwF (S-ob x)
    CwFHSliceHelp CwF Γ .TmP A = TmP CwF A
    CwFHSliceHelp CwF Γ .TyPm f x = (TyPm CwF (S-hom f)) x
    CwFHSliceHelp CwF Γ .TmPm f σ x = (TmPm CwF (S-hom f) σ) x
    CwFHSliceHelp CwF Γ .TyPmId σ = TyPmId CwF σ
    CwFHSliceHelp CwF Γ .TyPmComp σ f g = TyPmComp CwF σ (S-hom f) (S-hom g)
    CwFHSliceHelp CwF Γ .TmPmId tm = TmPmId CwF tm
    CwFHSliceHelp CwF Γ .TmPmComp tm f g = TmPmComp CwF tm (S-hom f) (S-hom g)
    CwFHSliceHelp {Ctxt = Ctxt} CwF Γ .cextOb Γ₁ σ = sliceob (Ctxt ._⋆_ (CwF .cextHom1 σ) (S-arr Γ₁))
    CwFHSliceHelp CwF Γ .cextHom1 σ = slicehom (CwF .cextHom1 σ) refl
    CwFHSliceHelp CwF Γ .cextHom2 σ = CwF .cextHom2 σ
    CwFHSliceHelp {Ctxt = Ctxt} CwF Γ .cextHomM {Γ₁} {Δ} f {σ} M = slicehom (cextHomM CwF ((S-hom f)) M) 
        ((sym (⋆Assoc Ctxt (cextHomM CwF (S-hom f) M) (cextHom1 CwF σ) (S-arr Δ))) ∙ 
        (⟨_⟩⋆⟨_⟩ Ctxt (sym (CwF .ConsL (S-hom f) M)) (refl {x = S-arr Δ})) ∙ (S-comm f))
    CwFHSliceHelp {Ctxt = Ctxt} CwF Γ .ConsL f M = SliceHom-≡-intro' Ctxt Γ (ConsL CwF (S-hom f) M)
    CwFHSliceHelp CwF Γ .ConsR f M = ConsR CwF ((S-hom f)) M
    CwFHSliceHelp {Ctxt = Ctxt} CwF Γ .ConsNat f g M = SliceHom-≡-intro' Ctxt Γ (ConsNat CwF (S-hom f) (S-hom g) M)
    CwFHSliceHelp {Ctxt = Ctxt} CwF Γ .ConsId f σ = SliceHom-≡-intro' Ctxt Γ (ConsId CwF (S-hom f) σ)



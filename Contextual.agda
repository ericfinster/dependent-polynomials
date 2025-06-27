
open import Cubical.Foundations.Prelude 
open import Cubical.Functions.Embedding

open import Cubical.Data.Nat.Base
open import Cubical.Data.List renaming (length to len)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Presheaf 
open import Cubical.Categories.Constructions.Elements 
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Functor

open import TCategory -- Categories with a terminal object
open import TyStr
open import DepPoly
open import CwFH

open Category
open Contravariant

module Contextual where

    record Contextual {ℓ ℓ' : Level} {Ctxt : Category ℓ ℓ'} {T : TCategory Ctxt} (CwF : CwFH Ctxt T) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ-zero) ℓ) ℓ') where

        field
                length : (Ctxt .ob) → ℕ
                Ter-length : {Γ : Ctxt .ob} (ɣ : (Γ ≡ (TCategory.TerObj T))) → (length Γ) ≡ zero
                0-length : {Γ : Ctxt .ob} (ɣ : ((length Γ) ≡ zero)) → (Γ ≡ (TCategory.TerObj T))
                lengthExt : {Γ : Ctxt .ob} (A : (CwFH.TyP CwF Γ)) → (length (CwFH.cextOb CwF Γ A)) ≡ (length Γ) + 1
                PredOb : {Γ : Ctxt .ob} {n : ℕ} (ɣ : ((length Γ) ≡ (suc n))) → (Ctxt .ob)
                PredTy : {Γ : Ctxt .ob} {n : ℕ} (ɣ : ((length Γ) ≡ (suc n))) → (CwFH.TyP CwF (PredOb ɣ))
                PredEq : {Γ : Ctxt .ob} {n : ℕ} (ɣ : ((length Γ) ≡ (suc n))) → Γ ≡ (CwFH.cextOb CwF (PredOb ɣ) (PredTy ɣ))
        
    open Contextual public
    
    FibrantSlice : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} {CwF : CwFH Ctxt T} (C : Contextual CwF) 
            → {Γ : Ctxt .ob} → (Ty : CwFH.TyP CwF Γ) → (Category ℓ ℓ)
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ .ob = 
                Σ (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁) .ob) (λ x → (
                Σ (CwFH.TyP CwF (CwFH.cextOb CwF Γ Ty₁)) (λ y → (
                Σ ((S-ob x) ≡ (CwFH.cextOb CwF (CwFH.cextOb CwF Γ Ty₁) y)) (
                λ z → (transport (
                λ i → Category.Hom[_,_] Ctxt (z i) (CwFH.cextOb CwF Γ Ty₁)) (S-arr x)) 
                ≡ (CwFH.cextHom1 CwF y))))))
    Hom[ FibrantSlice {Ctxt = Ctxt} {CwF = CwF} C {Γ = Γ} Ty₁ , fst₁ , x ] (fst₂ , x₁) = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁)).Hom[_,_] fst₁ fst₂
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ .id = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁)).id
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ ._⋆_ = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁))._⋆_
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ .⋆IdL = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁)).⋆IdL
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ .⋆IdR = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁)).⋆IdR
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ .⋆Assoc = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁)).⋆Assoc
    FibrantSlice {Ctxt = Ctxt} {T = T} {CwF = CwF} C {Γ = Γ} Ty₁ .isSetHom = (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁)).isSetHom

    FibrantSliceToBase :  {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt} {CwF : CwFH Ctxt T} (C : Contextual CwF) 
            → {Γ : Ctxt .ob} → (Ty : CwFH.TyP CwF Γ) → (Functor (FibrantSlice C Ty) Ctxt)
    FibrantSliceToBase C Ty₁ .Functor.F-ob (fst₁ , x) = S-ob fst₁
    FibrantSliceToBase C Ty₁ .Functor.F-hom x = S-hom x
    FibrantSliceToBase C Ty₁ .Functor.F-id = refl
    FibrantSliceToBase C Ty₁ .Functor.F-seq f g = refl

    -- Σ (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁) .ob) (λ x → (Σ (CwFH.TyP CwF (CwFH.cextOb CwF Γ Ty₁)) 
    --            (λ y → (Σ ((S-ob x) ≡ (CwFH.cextOb CwF (CwFH.cextOb CwF Γ Ty₁) y)) (λ z → (S-arr x) ≡ (CwFH.cextHom1 CwF y))))))

    -- Σ (SliceCat Ctxt (CwFH.cextOb CwF Γ Ty₁) .ob)
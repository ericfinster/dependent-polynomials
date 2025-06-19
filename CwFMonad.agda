open import Cubical.Foundations.Prelude 

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
open import Monad

module CwFMonad where


    
    CwFPolyMonad : {ℓ : Level} {Ctxt : Category ℓ ℓ} {T : TCategory Ctxt}
        (CwF : CwFH Ctxt T) → (Monad (CwFHToTyStr CwF))
    CwFPolyMonad CwF .Monad.P = CwFHToDepPoly CwF
    CwFPolyMonad CwF .Monad.μ .Tm⇒ {Γ} {T} (fst₁ , ● .Γ , snd₁) = {!   !}
    CwFPolyMonad CwF .Monad.μ .Tm⇒ {Γ} {T} (fst₁ , cns Γ₁ T₁ t Γ' Δ' fst₂ , snd₁) = {!   !}
    CwFPolyMonad CwF .Monad.μ .⇑⇒ (fst₁ , fst₂ , snd₁) = {!   !}
    CwFPolyMonad {T = Ter} CwF .Monad.η .Tm⇒ {T₁ ► ϵ} {T} x = {!   !}
    CwFPolyMonad CwF .Monad.η .⇑⇒ = {!   !}
    
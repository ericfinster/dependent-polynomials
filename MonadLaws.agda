open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import TyStr
open import DepPoly
open import Monad
open import BSystems
open import BSystemToDepPoly
open import ConvertingSubstitutions
open import Monad
open import BSystemToMonad

module MonadLaws where

-- -- -- Multiplication Law

Multiplication : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B)
        → (t₁ : Tm (((Monad.P (BSystemToMonad BS)) ⊚ (Monad.P (BSystemToMonad BS))) ⊚ (Monad.P (BSystemToMonad BS))) Γ T)
        → (t₂ : Tm ((Monad.P (BSystemToMonad BS)) ⊚ ((Monad.P (BSystemToMonad BS)) ⊚ (Monad.P (BSystemToMonad BS)))) Γ T)
        → assoc-mult-left (BSystemToMonad BS) Γ T t₁ ≡ assoc-mult-right (BSystemToMonad BS) Γ T t₂
Multiplication BS Γ T (fst₁ , fst₂ , snd₁) (fst₃ , fst₄ , fst₅ , fst₆ , snd₂) i = {!   !}


UnitLaw : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctx (BSystemToTyStr BS)) (T : TyTmStr.Typ B) (t : Tm (Monad.P (BSystemToMonad BS)) Γ T)
        → (unit-mult-left (BSystemToMonad BS) Γ T t) ≡ unit-mult-right (BSystemToMonad BS) Γ T t
UnitLaw BS Γ T t i = {!   !} 
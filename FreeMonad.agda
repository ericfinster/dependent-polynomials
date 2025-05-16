open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import Monad

module FreeMonad where -- I want to show that the free Monoid from DepPoly is a monad

    ηh : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋) → IdPoly 𝕋 ⇒ Free M -- we want to do something like λ idT T → lf T but this doesn't work for some fibrancy reason
    ηh M .Tm⇒ (idT T) = lf T
    ηh {𝕋} M .⇑⇒ (idT T) = Id⇒ (IdPoly (𝕋 // T))

    μh : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋) {T : Ty 𝕋} → Free M ⊚ Free M ⇒ Free M -- we want to use nd to basically connect the tress along the substitution given by ⊚  nd Γ Γ T σ w this but I would need to move Γ and T into scope
    μh {𝕋} M {T₀} .Tm⇒ {Γ} (_ , σ , lf T) = {!!}
    μh M .Tm⇒ (Γ , σ , nd .Γ Γ₁ _ σ₁ w) = {!!}
    μh M .⇑⇒ = {!!}

  -- λ M → record { Tm⇒ =  {! λ (Tm Γ T) → nd Γ Γ T σ t   !} ; ⇑⇒ = λ t → {!   !}}  -- lift: should in some sense just be the identity, since we lift the trees in Free M ⊚ Free M to their concatenation

    FreeMon : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋) → Monad 𝕋
    FreeMon M = record { P = Free M ; μ = μh M ; η = ηh M }   

    -- proving the associativity of μ should also just be an application of nd, since nd itself should be associative since the tree structure is associative

    unit-law : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋)
        → (Γ : Ctx 𝕋) (A : Ty 𝕋) (t : Tm (Monad.P (FreeMon M)) Γ A) 
        → unit-mult-left (FreeMon M) Γ A t ≡ unit-mult-right (FreeMon M) Γ A t 
    unit-law = λ M Γ A t i → {!  !}

{-
    assoc-law : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋)
        → (Γ : Ctx 𝕋) → (A : Ty 𝕋) → 
        (t1 : Tm ((Monad.P (FreeMon M)) ⊚ ((Monad.P (FreeMon M)) ⊚ (Monad.P (FreeMon M)))) Γ A) → 
        (t2 : Tm (((Monad.P (FreeMon M)) ⊚ (Monad.P (FreeMon M))) ⊚ (Monad.P (FreeMon M))) Γ A)
        → (assoc-mult-left (FreeMon M) Γ A t1 ≡ assoc-mult-right (FreeMon M) Γ A t2)
    assoc-law = ? 

    this doesn't type check and I don't understand why 

    /home/karlh/agda/dependent-polynomials/FreeMonad.agda:32,44-46
    (Free M) != (Monad.P (FreeMon M) ⊚ Monad.P (FreeMon M)) of type
    (DepPoly 𝕋 𝕋)
    when checking that the expression t1 has type   
    Tm
    (Monad.P (FreeMon M) ⊚ Monad.P (FreeMon M) ⊚ Monad.P (FreeMon M)) Γ
    A

-}  

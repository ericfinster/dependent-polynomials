open import Cubical.Foundations.Prelude 

open import Cubical.Categories.Category.Base 

open import TyStr
open import DepPoly
open import Monad

module DepPolyToCat where

    DepPolyToCat : {T : TyStr} (M : Monad T) → (Category ℓ-zero ℓ-zero)
    DepPolyToCat {T} M .Category.ob = Ctx T
    DepPolyToCat M .Category.Hom[_,_] = Subst (Monad.P M)
    DepPolyToCat M .Category.id {x} = Subst⇒ (Monad.η M) (idSubst x)
    DepPolyToCat M .Category._⋆_ = {!   !}
    DepPolyToCat M .Category.⋆IdL = {!   !}
    DepPolyToCat M .Category.⋆IdR = {!   !}
    DepPolyToCat M .Category.⋆Assoc = {!   !}
    DepPolyToCat M .Category.isSetHom x y x₁ y₁ = {! refl {x = x ≡ y} !}

{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude 

module BSystems where

  record TyTmStr : Type₁ where 
    coinductive
    field
      Typ : Type -- this is just X itself
      Tm : Typ → Type -- this is delta^-1
      Slc : Typ → TyTmStr -- this is ft^-1

  open TyTmStr
  
  record _↝_ (A B : TyTmStr) : Type where
    coinductive
    field
      Ty↝ : Typ A → Typ B
      Tm↝ : (T : Typ A) → Tm A T → Tm B (Ty↝ T)
      Slc↝ : (T : Typ A) → Slc A T ↝ Slc B (Ty↝ T)

  open _↝_

  
  record PreBSystem (A : TyTmStr) : Type where
    coinductive
    field
      wk : (T : Typ A) → A ↝ Slc A T
      sub : (T : Typ A) (t : Tm A T) → Slc A T ↝ A
      var : (T : Typ A) → Tm (Slc A T) (Ty↝ (wk T) T)
      slc : (T : Typ A) → PreBSystem (Slc A T) 

  open PreBSystem
  
  record is-homomorphism (A B : TyTmStr) (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (ϕ : A ↝ B) : Type where
    coinductive
    field
      wk≡Ty : (T U : Typ A) → Ty↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) U) ≡ Ty↝ (wk Bᵇ (ϕ .Ty↝ T)) (Ty↝ ϕ U)
      wk≡Tm : (T : Typ A) → (t : Tm A T) → (Tm↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) T) (Tm↝ (wk Aᵇ T) T t)) 
          ≡ transport (λ i → (Tm (Slc B (Ty↝ ϕ T)) (wk≡Ty T T (~ i)))) (Tm↝ (wk Bᵇ (Ty↝ ϕ T)) (Ty↝ ϕ T) (Tm↝ ϕ T t)) 
      sub≡Ty : (T : Typ A) → (t : Tm A T) → (U : Typ (Slc A T)) → Ty↝ ϕ (Ty↝ (sub Aᵇ T t) U) ≡ Ty↝ (sub Bᵇ (Ty↝ ϕ T) (Tm↝ ϕ T t)) (Ty↝ (Slc↝ ϕ T) U)
      sub≡Tm : (T : Typ A) → (t : Tm A T) → (U : Typ (Slc A T)) → (u : Tm (Slc A T) U) 
          → Tm↝ ϕ (Ty↝ (sub Aᵇ T t) U) (Tm↝ (sub Aᵇ T t) U u)
          ≡ transport (λ i → Tm B (sub≡Ty T t U (~ i)))
          (Tm↝ (sub Bᵇ (Ty↝ ϕ T) (Tm↝ ϕ T t)) (Ty↝ (Slc↝ ϕ T) U) (Tm↝ (Slc↝ ϕ T) U u))
      var≡ : (T : Typ A) → (Tm↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T)) ≡ transport (λ i → Tm (Slc B (Ty↝ ϕ T)) (wk≡Ty T T (~ i))) (var Bᵇ (Ty↝ ϕ T)) 
      SlcHomomorphism : (T : Typ A) → is-homomorphism (Slc A T) (Slc B (Ty↝ ϕ T)) (slc Aᵇ T) (slc Bᵇ (Ty↝ ϕ T)) (Slc↝ ϕ T) -- not in BSystemsRewrite, but I'm pretty sure one needs this

  idStr : (A : TyTmStr) → (A ↝ A)
  idStr A .Ty↝ x = x
  idStr A .Tm↝ T x = x
  idStr A .Slc↝ T = idStr (Slc A T)   

  _○_ : {A B C : TyTmStr} → (f : B ↝ C) → (g : A ↝ B) → (A ↝ C)
  (f ○ g) .Ty↝ x = Ty↝ f (Ty↝ g x)
  (f ○ g) .Tm↝ T x = Tm↝ f (Ty↝ g T) (Tm↝ g T x)
  (f ○ g) .Slc↝ T = (Slc↝ f (Ty↝ g T)) ○ (Slc↝ g T) 

  IdStrLN : (A B : TyTmStr) (f : A ↝ B) → (idStr B) ○ f ≡ f
  IdStrLN A B f = {!  !}
  
  record BSystem (A : TyTmStr) (Aᵇ : PreBSystem A) : Type where
    coinductive
    field
      wk-is-homomorphism : (T : Typ A) → is-homomorphism A (Slc A T) Aᵇ (slc Aᵇ T) (wk Aᵇ T) 
      sub-is-homomorphism : (T : Typ A) → (t : Tm A T) → is-homomorphism (Slc A T) A (slc Aᵇ T) Aᵇ (sub Aᵇ T t)
      sub-of-wk-Tm : {T : Typ A} (t : Tm A T) → ((sub Aᵇ T t) ○ (wk Aᵇ T)) ≡ (idStr A)
      sub-of-wk-Typ : (T : Typ A) → ((sub (slc Aᵇ T) (Ty↝ (Aᵇ .wk T) T) (var Aᵇ T)) ○ (Slc↝ (wk Aᵇ T)) T) ≡ (idStr (Slc A T))
      Variable-sub : {T : Typ A} → (t : Tm A T) → (transport (λ i → (Tm A ((Ty↝ (sub-of-wk-Tm t i)) T))) (Tm↝ (sub Aᵇ T t) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T))) ≡ t
      BSlc : (T : Typ A) → BSystem (Slc A T) (slc Aᵇ T) -- this maybe makes SlcHomomorphism redundant at least from a BSystem viewpointt


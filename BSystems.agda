
open import Cubical.Foundations.Prelude 

module BSystems where

  record TyTmStr : Type₁ where
    coinductive
    field
      Ty : Type
      Tm : Ty → Type
      Slc : Ty → TyTmStr

  open TyTmStr
  
  record _⇒_ (A B : TyTmStr) : Type where
    coinductive
    field
      Ty⇒ : Ty A → Ty B
      Tm⇒ : (T : Ty A) → Tm A T → Tm B (Ty⇒ T)
      Slc⇒ : (T : Ty A) → Slc A T ⇒ Slc B (Ty⇒ T)

  open _⇒_
  
  record PreBSystem (A : TyTmStr) : Type where
    coinductive
    field
      wk : (T : Ty A) → A ⇒ Slc A T
      sub : (T : Ty A) (t : Tm A T) → Slc A T ⇒ A
      var : (T : Ty A) → Tm (Slc A T) (Ty⇒ (wk T) T)
      slc : (T : Ty A) → PreBSystem (Slc A T) 

  open PreBSystem
  
  record is-homomorphism (A B : TyTmStr) (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (ϕ : A ⇒ B) : Type where
    coinductive
    field
      wk≡ : (T U : Ty A) → Ty⇒ (Slc⇒ ϕ T) (Ty⇒ (wk Aᵇ T) U) ≡ Ty⇒ (wk Bᵇ (ϕ .Ty⇒ T)) (Ty⇒ ϕ U) 
      -- sub≡ : ......
      -- var≡ : .....
  
  record BSystem (A : TyTmStr) (Aᵇ : PreBSystem A) : Type where
    coinductive
    field
      wk-is-homomorphism : (T : Ty A) → is-homomorphism A (Slc A T) Aᵇ (slc Aᵇ T) (wk Aᵇ T) 

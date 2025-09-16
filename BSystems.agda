{-# OPTIONS --allow-unsolved-metas #-}
 
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Empty
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels 
open import Cubical.Data.Sigma


module BSystems where

  record TyTmStr : Type₁ where 
    coinductive
    field
      Typ : Type -- this is just X itself
      -- TypIsSet : isSet Typ
      Tm : Typ → Type -- this is delta^-1
      -- TmIsSet : (T : Typ) → isSet (Tm T)
      Slc : Typ → TyTmStr -- this is ft^-1

  open TyTmStr

  record isSetStr (B : TyTmStr) : Type₁ where
    coinductive
    field
      TypIsSet : isSet (Typ B) 
      TmIsSet : (T : Typ B) → isSet (Tm B T)
      SlcIsSet : (T : Typ B) → (isSetStr (Slc B T))

  open isSetStr

  ΣStructure : {I : Type} (A : I → TyTmStr) → TyTmStr
  ΣStructure {I} A .Typ = Σ[ i ∈ I ] Typ (A i)
  ΣStructure A .Tm (fst₁ , snd₁) = Tm (A fst₁) snd₁
  ΣStructure A .Slc (fst₁ , snd₁) = Slc (A fst₁) snd₁

  -- emptyStr : TyTmStr
  -- emptyStr .Typ = ⊥
  -- emptyStr .Tm = rec
  -- emptyStr .Slc = rec

  -- equalities needed for the intoduction of hom equality

  proj-Typ : (A B : TyTmStr) (ɣ : A ≡ B) → (Typ A ≡ (Typ B))
  proj-Typ A B ɣ i = Typ (ɣ i)

  proj-Tm : (A B : TyTmStr) (ɣ : A ≡ B) → PathP (λ i → Typ (ɣ i) → Type) (Tm A) (Tm B)
  proj-Tm A B ɣ i = Tm (ɣ i)
 

  proj-Slc : {A B : TyTmStr} (ɣ : A ≡ B) → PathP (λ i → Typ (ɣ i) → TyTmStr) (Slc A) (Slc B)
  proj-Slc ɣ i = Slc (ɣ i)

  -- -- --

  -- -- -- Contexts (maybe usefull in the conversion case to DepPoly)
        -- in a actaul BSystem viewpoint these are better thought of as the result of TopTyTm, so as a TyTmStr
        -- which handles the dependency implicitely

  data Ctxt (A : TyTmStr) : Type where
    ε : Ctxt A
    _⊳_ : (T : Typ A) (Γ : Ctxt (Slc A T)) → (Ctxt A) 

  TopTyTm : {B : TyTmStr} (Γ : Ctxt B) → TyTmStr
  TopTyTm {B} ε = B
  TopTyTm (T ⊳ Γ) = TopTyTm Γ 

  concat : {B : TyTmStr} (Γ : Ctxt B) (Γ' : Ctxt (TopTyTm Γ)) → (Ctxt B)
  concat ε Γ' = Γ'
  concat (T ⊳ Γ) Γ' = T ⊳ (concat Γ Γ')

  TypesInCtx : {B : TyTmStr} (Γ : Ctxt B) → Type
  TypesInCtx Γ = Typ (TopTyTm Γ)

  TermsInCtx : {B : TyTmStr} (Γ : Ctxt B) → (T : (TypesInCtx Γ)) → Type
  TermsInCtx Γ T = Tm (TopTyTm Γ) T

  -- -- --

  record _↝_ (A B : TyTmStr) : Type where
    coinductive
    field
      Ty↝ : Typ A → Typ B
      Tm↝ : (T : Typ A) → Tm A T → Tm B (Ty↝ T)
      Slc↝ : (T : Typ A) → Slc A T ↝ Slc B (Ty↝ T)

  open _↝_


  -- -- -- Composition and identity of Morphisms

  idStr : (A : TyTmStr) → (A ↝ A)
  idStr A .Ty↝ x = x
  idStr A .Tm↝ T x = x
  idStr A .Slc↝ T = idStr (Slc A T) 

  _○_ : {A B C : TyTmStr} → (f : B ↝ C) → (g : A ↝ B) → (A ↝ C)
  (f ○ g) .Ty↝ x = Ty↝ f (Ty↝ g x)
  (f ○ g) .Tm↝ T x = Tm↝ f (Ty↝ g T) (Tm↝ g T x)
  (f ○ g) .Slc↝ T = (Slc↝ f (Ty↝ g T)) ○ (Slc↝ g T)


  -- EmptySubst : (B : TyTmStr) → emptyStr ↝ B
  -- EmptySubst B .Ty↝ = rec
  -- EmptySubst B .Tm↝ T x = rec T
  -- EmptySubst B .Slc↝ T = rec T

  -- -- --

  -- -- -- introducing and eliminating equalities between Homs

  -- -- Elimination

  proj-ty : {A B : TyTmStr} {f g : A ↝ B} → f ≡ g → (T : Typ A) → Ty↝ f T ≡ Ty↝ g T
  proj-ty p T i = Ty↝ (p i) T 

  proj-tm : {A B : TyTmStr} {f g : A ↝ B} → (p : f ≡ g) → (T : Typ A) (t : Tm A T) → PathP (λ i → Tm B (proj-ty p T i)) (Tm↝ f T t) (Tm↝ g T t)
  proj-tm {A} {B} p T t i = Tm↝ (p i) T t 

  proj-slc : {A B : TyTmStr} {f g : A ↝ B} → (p : f ≡ g) → (T : Typ A) → PathP (λ i → (Slc A T) ↝ (Slc B (proj-ty p T i))) (Slc↝ f T) (Slc↝ g T)
  proj-slc p T i = Slc↝ (p i) T




  isSetHomTy : (A B : TyTmStr) (a : isSetStr A) (b : isSetStr B) (f : A ↝ B) (g : A ↝ B) 
      (eq₁ : f ≡ g) (eq₂ : f ≡ g) (T : Typ A) → (proj-ty eq₁ T) ≡ (proj-ty eq₂ T)
  isSetHomTy A B a b f g eq₁ eq₂ T = TypIsSet b (Ty↝ f T) (Ty↝ g T)
      (λ i → Ty↝ (eq₁ i) T) (λ i → Ty↝ (eq₂ i) T)

  {-# TERMINATING #-}
  HomIsSet : (A B : TyTmStr) (a : isSetStr A) (b : isSetStr B) → (isSet (A ↝ B))
  HomIsSet A B a b x y x₁ y₁ i i₁ .Ty↝ T = isSetHomTy A B a b x y x₁ y₁ T i i₁
  HomIsSet A B a b x y x₁ y₁ i i₁ .Tm↝ T t = isSet→SquareP (λ j j₁ → (TmIsSet b (isSetHomTy A B a b x y x₁ y₁ T j j₁)))
      (λ i → (Tm↝ (x₁ i) T t)) (λ i → (Tm↝ (y₁ i) T t)) (λ i → (Tm↝ x T t)) (λ i → (Tm↝ y T t)) i i₁
  HomIsSet A B a b x y x₁ y₁ i i₁ .Slc↝ T = isSet→SquareP (λ j j₁ → (HomIsSet (Slc A T) (Slc B (isSetHomTy A B a b x y x₁ y₁ T j j₁))
      (SlcIsSet a T) (SlcIsSet b (isSetHomTy A B a b x y x₁ y₁ T j j₁))))
      (λ i → (Slc↝ (x₁ i) T)) (λ i → (Slc↝ (y₁ i) T)) (λ i → (Slc↝ x T)) (λ i → (Slc↝ y T)) i i₁

  -- Intoduction

  -- needed to have a coinductive record of equality, to handle the coinductive structure of homs
  record ↝-bi-sim {A B C : TyTmStr} (f : A ↝ B) (g : A ↝ C) (ɣ : B ≡ C) : Type where
     coinductive
     field
       Ty-eq : (T : Typ A) → (PathP (λ i → (Typ (ɣ i))) (Ty↝ f T) (Ty↝ g T))
       Tm-eq : (T : Typ A) (t : Tm A T) → PathP (λ i → Tm (ɣ i) (Ty-eq T i)) (Tm↝ f T t) (Tm↝ g T t)
       Slc-eq : (T : Typ A) → ↝-bi-sim (Slc↝ f T) (Slc↝ g T) (λ i → (proj-Slc ɣ i) (Ty-eq T i))

  open ↝-bi-sim

  ↝-≡-intro : {A B C : TyTmStr} (f : A ↝ B) (g : A ↝ C) (ɣ : B ≡ C) (β : ↝-bi-sim f g ɣ) → (PathP (λ i → (A ↝ (ɣ i))) f g) 
  ↝-≡-intro f g ɣ β i .Ty↝ T = Ty-eq β T i
  ↝-≡-intro f g ɣ β i .Tm↝ T t = Tm-eq β T t i
  ↝-≡-intro {B = B} {C = C} f g ɣ β i .Slc↝ T = ↝-≡-intro (Slc↝ f T) (Slc↝ g T) (λ j → (proj-Slc ɣ j) (Ty-eq β T j)) (Slc-eq β T) i

  -- ↝-≡-intro (Slc↝ f T) (Slc↝ g T) (proj-Slc B C ɣ (Ty↝ f T) (Ty↝ g T) (Ty-eq β T)) (Slc-eq β T) i 

  -- -- -- Standard Properties of composition and identity

  ○-assoc : {A B C D : TyTmStr} → (f : C ↝ D) → (g : B ↝ C) → (h : A ↝ B) 
      → ((f ○ g) ○ h) ≡ (f ○ (g ○ h))
  ○-assoc f g h i .Ty↝ x = (Ty↝ f (Ty↝ g (Ty↝ h x)))
  ○-assoc f g h i .Tm↝ T x = Tm↝ f (Ty↝ g (Ty↝ h T)) (Tm↝ g (Ty↝ h T) (Tm↝ h T x))
  ○-assoc f g h i .Slc↝ T = ○-assoc (Slc↝ f (Ty↝ g (Ty↝ h T))) (Slc↝ g (Ty↝ h T)) (Slc↝ h T) i 

  IdStrLN-bi-sim : {A B : TyTmStr} (f : A ↝ B) → ↝-bi-sim ((idStr B) ○ f) f refl
  IdStrLN-bi-sim f .Ty-eq T = refl
  IdStrLN-bi-sim f .Tm-eq T t = refl
  IdStrLN-bi-sim f .Slc-eq T = IdStrLN-bi-sim (Slc↝ f T)

  IdStrRN-bi-sim : {A B : TyTmStr} (f : A ↝ B) → ↝-bi-sim (f ○ (idStr A)) f refl
  IdStrRN-bi-sim f .Ty-eq T = refl
  IdStrRN-bi-sim f .Tm-eq T t = refl
  IdStrRN-bi-sim f .Slc-eq T = IdStrRN-bi-sim (Slc↝ f T)

  IdStrLN : {A B : TyTmStr} (f : A ↝ B) → (idStr B) ○ f ≡ f
  IdStrLN {B = B} f = ↝-≡-intro ((idStr B) ○ f) f refl (IdStrLN-bi-sim f)

  IdStrRN : {A B : TyTmStr} (f : A ↝ B) → f ○ (idStr A) ≡ f
  IdStrRN {A} f = ↝-≡-intro (f ○ (idStr A)) f refl (IdStrRN-bi-sim f)

  Ty↝-comp : {A B C : TyTmStr} (f : B ↝ C) (g : A ↝ B) (T : Typ A) → (Ty↝ (f ○ g) T) ≡ (Ty↝ f (Ty↝ g T))
  Ty↝-comp f g T = refl


  -- -- --
  
  record PreBSystem (A : TyTmStr) : Type where
    coinductive
    field
      wk : (T : Typ A) → A ↝ Slc A T
      sub : (T : Typ A) (t : Tm A T) → Slc A T ↝ A
      var : (T : Typ A) → Tm (Slc A T) (Ty↝ (wk T) T)
      slc : (T : Typ A) → PreBSystem (Slc A T) 

  open PreBSystem

  -- -- -- Interaction between morphisms to Contexts

  AppCtxt : {B : TyTmStr} {A : TyTmStr} (Γ : Ctxt A) (f : A ↝ B) → (Ctxt B)
  AppCtxt ε f = ε
  AppCtxt (T ⊳ Γ) f = (Ty↝ f T) ⊳ (AppCtxt Γ (Slc↝ f T))

  SubCtxt : {B : TyTmStr} (Bᵇ : PreBSystem B) (T : Typ B) (t : Tm B T) (Γ : Ctxt (Slc B T)) → (Ctxt B)
  SubCtxt Bᵇ T t Γ = AppCtxt Γ (sub Bᵇ T t)

  wkCtxt : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) → (B ↝ (TopTyTm Γ))
  wkCtxt {B} Bᵇ ε = idStr B
  wkCtxt Bᵇ (T ⊳ Γ) = (wkCtxt (slc Bᵇ T) Γ) ○ (wk Bᵇ T)

  -- AppCtxtWk : {B : TyTmStr} (Bᵇ : PreBSystem B) (T : Typ B) (Γ : Ctxt (Slc B T)) → wkCtxt (slc Bᵇ T) Γ ≡ {! wkCtxt (slc Bᵇ T) (AppCtxt (T ⊳ Γ) (wk Bᵇ T))  !}


  SlcHomCtxt : {A B : TyTmStr} (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (Γ : Ctxt A) (f : A ↝ B) → ((TopTyTm Γ) ↝ (TopTyTm (AppCtxt Γ f)))
  SlcHomCtxt Aᵇ Bᵇ ε f = f
  SlcHomCtxt Aᵇ Bᵇ (T ⊳ Γ) f = SlcHomCtxt (slc Aᵇ T) (slc Bᵇ (Ty↝ f T)) Γ (Slc↝ f T) 


  -- -- -- 
  
  -- Lifiting PreBSystem along Context

  TopPre : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) → (PreBSystem (TopTyTm Γ))
  TopPre Bᵇ ε = Bᵇ
  TopPre Bᵇ (T ⊳ Γ) = TopPre (slc Bᵇ T) Γ

  -- record is-homomorphism2 (A B : TyTmStr) (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (ϕ : A ↝ B) : Type where
  --   coinductive
  --   field
  --     wk≡Ty : (T U : Typ A) → Ty↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) U) ≡ Ty↝ (wk Bᵇ (ϕ .Ty↝ T)) (Ty↝ ϕ U)
  --     -- Does this need to be a PathP?
  --     wk≡Tm : (T : Typ A) → (t : Tm A T) → (Tm↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) T) (Tm↝ (wk Aᵇ T) T t)) 
  --         ≡ transport (λ i → (Tm (Slc B (Ty↝ ϕ T)) (wk≡Ty T T (~ i)))) (Tm↝ (wk Bᵇ (Ty↝ ϕ T)) (Ty↝ ϕ T) (Tm↝ ϕ T t)) 
  --     sub≡Ty : (T : Typ A) → (t : Tm A T) → (U : Typ (Slc A T)) → Ty↝ ϕ (Ty↝ (sub Aᵇ T t) U) 
  --         ≡ Ty↝ (sub Bᵇ (Ty↝ ϕ T) (Tm↝ ϕ T t)) (Ty↝ (Slc↝ ϕ T) U)
  --     -- Does this need to be a PathP? Turning these into PathPs would allow to prove actual equalities
  --     sub≡Tm : (T : Typ A) → (t : Tm A T) → (U : Typ (Slc A T)) → (u : Tm (Slc A T) U) 
  --         → Tm↝ ϕ (Ty↝ (sub Aᵇ T t) U) (Tm↝ (sub Aᵇ T t) U u)
  --         ≡ transport (λ i → Tm B (sub≡Ty T t U (~ i)))
  --         (Tm↝ (sub Bᵇ (Ty↝ ϕ T) (Tm↝ ϕ T t)) (Ty↝ (Slc↝ ϕ T) U) (Tm↝ (Slc↝ ϕ T) U u))
  --     var≡ : (T : Typ A) → (Tm↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T)) ≡ transport (λ i → Tm (Slc B (Ty↝ ϕ T)) (wk≡Ty T T (~ i))) (var Bᵇ (Ty↝ ϕ T)) 
  --     SlcHomomorphism : (T : Typ A) → is-homomorphism2 (Slc A T) (Slc B (Ty↝ ϕ T)) (slc Aᵇ T) (slc Bᵇ (Ty↝ ϕ T)) (Slc↝ ϕ T) -- not in BSystemsRewrite, but I'm pretty sure one needs this

  record is-homomorphism {A B : TyTmStr} (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (ϕ : A ↝ B) : Type where
    coinductive
    field
      wk≡ :  (T : Typ A) → ((Slc↝ ϕ T) ○ (wk Aᵇ T)) ≡ (wk Bᵇ (ϕ .Ty↝ T)) ○ ϕ
      sub≡ : (T : Typ A) → (t : Tm A T) → (ϕ ○ (sub Aᵇ T t)) ≡ ((sub Bᵇ (Ty↝ ϕ T) (Tm↝ ϕ T t)) ○ (Slc↝ ϕ T))
      var≡ : (T : Typ A) → PathP ((λ i → Tm (Slc B (Ty↝ ϕ T)) (Ty↝ (wk≡ T (i)) T))) ((Tm↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T))) ((var Bᵇ (Ty↝ ϕ T)))
      SlcHomomorphism : (T : Typ A) → is-homomorphism (slc Aᵇ T) (slc Bᵇ (Ty↝ ϕ T)) (Slc↝ ϕ T)
  
  open is-homomorphism

  IdIsHomomorphsimwk : {B : TyTmStr} (Bᵇ : PreBSystem B) (T : Typ B)
      → (idStr (Slc B T) ○ wk Bᵇ T) ≡ (wk Bᵇ T ○ idStr B)
  IdIsHomomorphsimwk {B} Bᵇ T = (idStr (Slc B T) ○ wk Bᵇ T)
      ≡⟨ IdStrLN (wk Bᵇ T) ⟩
        wk Bᵇ T
      ≡⟨ sym (IdStrRN (wk Bᵇ T)) ⟩
          wk Bᵇ T ○ idStr B
      ∎

  IdTest : {B : TyTmStr} (Bᵇ : PreBSystem B) (b : isSetStr B) (T : Typ B)
      → cong (λ x → (Ty↝ x T)) (IdIsHomomorphsimwk Bᵇ T) ≡ λ i → (Ty↝ (wk Bᵇ T) T)
  IdTest Bᵇ b T  = TypIsSet (SlcIsSet b T) (Ty↝ (wk Bᵇ T) T) (Ty↝ (wk Bᵇ T) T)
      (cong (λ x → (Ty↝ x T)) (IdIsHomomorphsimwk Bᵇ T)) 
      (λ i → (Ty↝ (wk Bᵇ T) T))


  IdIsHomomorphismVar : {B : TyTmStr} (Bᵇ : PreBSystem B) (b : isSetStr B) (T : Typ B)
      → PathP (λ i → Tm (Slc B T) (Ty↝ (IdIsHomomorphsimwk Bᵇ T i) T)) (var Bᵇ T) (var Bᵇ T) 
  IdIsHomomorphismVar {B} Bᵇ b T = subst (λ x → PathP (λ i → (Tm (Slc B T) (x i))) (var Bᵇ T) (var Bᵇ T)) (sym (IdTest Bᵇ b T)) refl



  IdIsHomomorphism : {B : TyTmStr} (Bᵇ : PreBSystem B) (b : isSetStr B) → is-homomorphism Bᵇ Bᵇ (idStr B)
  IdIsHomomorphism {B} Bᵇ b .wk≡ T = IdIsHomomorphsimwk Bᵇ T
  IdIsHomomorphism {B} Bᵇ b .sub≡ T t = (idStr B ○ sub Bᵇ T t)
      ≡⟨ IdStrLN (sub Bᵇ T t) ⟩
        sub Bᵇ T t
      ≡⟨ sym (IdStrRN (sub Bᵇ T t)) ⟩
        sub Bᵇ T t ○ idStr (Slc B T)   
      ∎
  IdIsHomomorphism {B = B} Bᵇ b .var≡ T = IdIsHomomorphismVar Bᵇ b T
  IdIsHomomorphism Bᵇ b .SlcHomomorphism T = IdIsHomomorphism (slc Bᵇ T) (SlcIsSet b T) 

  wkCtxtCommutes : {B C : TyTmStr} (Bᵇ : PreBSystem B) (Cᵇ : PreBSystem C) (Γ : Ctxt B) (f : B ↝ C)
    (H : is-homomorphism Bᵇ Cᵇ f)
    → ((SlcHomCtxt Bᵇ Cᵇ Γ f) ○ (wkCtxt Bᵇ Γ)) ≡ ((wkCtxt Cᵇ (AppCtxt Γ f)) ○ f)
  wkCtxtCommutes Bᵇ Cᵇ ε f H = (IdStrRN f) ∙ (sym (IdStrLN f))
  wkCtxtCommutes Bᵇ Cᵇ (T ⊳ Γ) f H = (SlcHomCtxt (slc Bᵇ T) (slc Cᵇ (Ty↝ f T)) Γ (Slc↝ f T) ○ (wkCtxt (slc Bᵇ T) Γ ○ wk Bᵇ T))
      ≡⟨ sym (○-assoc (SlcHomCtxt (slc Bᵇ T) (slc Cᵇ (Ty↝ f T)) Γ (Slc↝ f T)) (wkCtxt (slc Bᵇ T) Γ) (wk Bᵇ T)) ⟩
        ((SlcHomCtxt (slc Bᵇ T) (slc Cᵇ (Ty↝ f T)) Γ (Slc↝ f T) ○ (wkCtxt (slc Bᵇ T) Γ)) ○ wk Bᵇ T)
      ≡⟨ (cong (λ x → x ○ (wk Bᵇ T)) (wkCtxtCommutes (slc Bᵇ T) (slc Cᵇ (Ty↝ f T)) Γ (Slc↝ f T) (SlcHomomorphism H T))) ⟩
        ((wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T)) ○ (Slc↝ f T)) ○ (wk Bᵇ T))
      ≡⟨ (○-assoc (wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T))) (Slc↝ f T) (wk Bᵇ T)) ⟩
        (wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T)) ○ ((Slc↝ f T) ○ (wk Bᵇ T)))
      ≡⟨ cong (λ x → ((wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T)))) ○ x) (wk≡ H T) ⟩
        (wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T)) ○ (wk Cᵇ (Ty↝ f T) ○ f))
      ≡⟨ sym (○-assoc (wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T))) (wk Cᵇ (Ty↝ f T)) f) ⟩
        ((wkCtxt (slc Cᵇ (Ty↝ f T)) (AppCtxt Γ (Slc↝ f T)) ○ wk Cᵇ (Ty↝ f T)) ○ f)
      ∎ 
  
  ○-homomorphismwk : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} {f : A ↝ B} {g : B ↝ C}
        (Hf : is-homomorphism Aᵇ Bᵇ f) (Hg : is-homomorphism Bᵇ Cᵇ g) (T : Typ A)
        → (Slc↝ (g ○ f) T) ○ (wk Aᵇ T)  ≡ ((wk Cᵇ (Ty↝ (g ○ f) T)) ○ (g ○ f))
  ○-homomorphismwk {Aᵇ = Aᵇ} {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg T = ((Slc↝ g (Ty↝ f T) ○ Slc↝ f T) ○ wk Aᵇ T) 
      ≡⟨ ○-assoc (Slc↝ g (Ty↝ f T)) (Slc↝ f T) (wk Aᵇ T) ⟩
        (Slc↝ g (Ty↝ f T) ○ (Slc↝ f T ○ wk Aᵇ T))
      ≡⟨ cong (λ x → (Slc↝ g (Ty↝ f T)) ○ x) (wk≡ Hf T) ⟩
        (Slc↝ g (Ty↝ f T)) ○ ((wk Bᵇ (Ty↝ f T)) ○ f)
      ≡⟨ sym (○-assoc (Slc↝ g (Ty↝ f T)) (wk Bᵇ (Ty↝ f T)) f) ⟩
        ((Slc↝ g (Ty↝ f T)) ○ (wk Bᵇ (Ty↝ f T))) ○ f
      ≡⟨ cong (λ x → x ○ f) (wk≡ Hg (Ty↝ f T)) ⟩
        ((wk Cᵇ (Ty↝ g (Ty↝ f T))) ○ g) ○ f
      ≡⟨ ○-assoc (wk Cᵇ (Ty↝ g (Ty↝ f T))) g f ⟩
        (wk Cᵇ (Ty↝ g (Ty↝ f T))) ○ (g ○ f)
      ∎

  CompTest : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} {f : A ↝ B} {g : B ↝ C}
        (Hf : is-homomorphism Aᵇ Bᵇ f) (Hg : is-homomorphism Bᵇ Cᵇ g) (a : isSetStr A) (b : isSetStr B) (c : isSetStr C) (T : Typ A)
        → cong (λ x → Ty↝ x T) (○-homomorphismwk Hf Hg T) ≡ (λ z → (Slc↝ g (Ty↝ f T) .Ty↝ (Ty↝ (wk≡ Hf T z) T))) ∙ (λ i → (Ty↝ (Hg .wk≡ (Ty↝ f T) i) (Ty↝ f T)))
  CompTest {Aᵇ = Aᵇ} {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg a b c T = TypIsSet (SlcIsSet c (Ty↝ (g ○ f) T)) 
      (Ty↝ ((Slc↝ (g ○ f) T) ○ (wk Aᵇ T)) T) (Ty↝ ((wk Cᵇ (Ty↝ (g ○ f) T)) ○ (g ○ f)) T)
      (cong (λ x → Ty↝ x T) (○-homomorphismwk Hf Hg T)) ((λ z → (Slc↝ g (Ty↝ f T) .Ty↝ (Ty↝ (wk≡ Hf T z) T))) ∙ (λ i → (Ty↝ (Hg .wk≡ (Ty↝ f T) i) (Ty↝ f T))))

  PathCompFunc : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} {f : A ↝ B} {g : B ↝ C}
        (Hf : is-homomorphism Aᵇ Bᵇ f) (Hg : is-homomorphism Bᵇ Cᵇ g) (a : isSetStr A) (b : isSetStr B) (c : isSetStr C) (T : Typ A)
        → cong (λ x → Tm (Slc C (Ty↝ g (Ty↝ f T))) x) ((λ z → (Slc↝ g (Ty↝ f T) .Ty↝ (Ty↝ (wk≡ Hf T z) T))) ∙ (λ i → (Ty↝ (Hg .wk≡ (Ty↝ f T) i) (Ty↝ f T))))
            ≡ (λ j → ((λ z → Tm (Slc C (g .Ty↝ (Ty↝ f T))) (Slc↝ g (Ty↝ f T) .Ty↝ (Ty↝ (wk≡ Hf T z) T)))
                ∙ (λ i → Tm (Slc C (Ty↝ g (Ty↝ f T))) (Ty↝ (Hg .wk≡ (Ty↝ f T) i) (Ty↝ f T)))) j)
  PathCompFunc {C = C} {f = f} {g = g} Hf Hg a b c T = cong-∙ (λ x → Tm (Slc C (Ty↝ g (Ty↝ f T))) x) 
      (λ z → (Slc↝ g (Ty↝ f T) .Ty↝ (Ty↝ (wk≡ Hf T z) T))) 
        (λ i → (Ty↝ (Hg .wk≡ (Ty↝ f T) i) (Ty↝ f T)))


  CompFinal :  {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} {f : A ↝ B} {g : B ↝ C}
        (Hf : is-homomorphism Aᵇ Bᵇ f) (Hg : is-homomorphism Bᵇ Cᵇ g) (a : isSetStr A) (b : isSetStr B) (c : isSetStr C) (T : Typ A)
        → PathP ((λ i → Tm (Slc C (Ty↝ g (Ty↝ f T))) (Ty↝ (○-homomorphismwk Hf Hg T i) T))) 
            ((Tm↝ (Slc↝ g (Ty↝ f T)) (Ty↝ (Slc↝ f T) (Ty↝ (wk Aᵇ T) T)) (Tm↝ (Slc↝ f T) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T)))) 
              ((var Cᵇ (Ty↝ g (Ty↝ f T))))
  CompFinal {C = C} {Aᵇ = Aᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg a b c T = subst (λ x → x
      (Tm↝ (Slc↝ g (Ty↝ f T)) (Ty↝ (Slc↝ f T) (Ty↝ (wk Aᵇ T) T)) (Tm↝ (Slc↝ f T) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T))) (var Cᵇ (Ty↝ g (Ty↝ f T))))
      ((sym (cong (λ x → PathP (λ i → (x i))) (PathCompFunc Hf Hg a b c T))) ∙ (sym (cong (λ x → PathP (λ i →  Tm (Slc C (Ty↝ g (Ty↝ f T))) (x i))) (CompTest Hf Hg a b c T))))
      (compPathP (λ i → (Tm↝ (Slc↝ g (Ty↝ f T)) (Ty↝ (wk≡ Hf T i) T) (var≡ Hf T i))) (var≡ Hg (Ty↝ f T)))


  ○-homomorphism : {A B C : TyTmStr} {Aᵇ : PreBSystem A} {Bᵇ : PreBSystem B} {Cᵇ : PreBSystem C} {f : A ↝ B} {g : B ↝ C}
        (Hf : is-homomorphism Aᵇ Bᵇ f) (Hg : is-homomorphism Bᵇ Cᵇ g) 
        → is-homomorphism Aᵇ Cᵇ (g ○ f)
  ○-homomorphism {Aᵇ = Aᵇ} {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg .wk≡ T = ○-homomorphismwk Hf Hg T
  ○-homomorphism {Aᵇ = Aᵇ} {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg .sub≡ T t = (g ○ f) ○ sub Aᵇ T t
      ≡⟨ ○-assoc g f (sub Aᵇ T t) ⟩
        g ○ (f ○ sub Aᵇ T t)
      ≡⟨ cong (λ x → g ○ x) (sub≡ Hf T t) ⟩
        g ○ ((sub Bᵇ (Ty↝ f T) (Tm↝ f T t)) ○ (Slc↝ f T))
      ≡⟨ sym (○-assoc g (sub Bᵇ (Ty↝ f T) (Tm↝ f T t)) (Slc↝ f T)) ⟩
        (g ○ (sub Bᵇ (Ty↝ f T) (Tm↝ f T t))) ○ (Slc↝ f T)
      ≡⟨ cong (λ x → x ○ (Slc↝ f T)) (sub≡ Hg (Ty↝ f T) (Tm↝ f T t)) ⟩ 
        ((sub Cᵇ (Ty↝ g (Ty↝ f T)) (Tm↝ g (Ty↝ f T) (Tm↝ f T t))) ○ (Slc↝ g (Ty↝ f T))) ○ (Slc↝ f T)
      ≡⟨ ○-assoc (sub Cᵇ (Ty↝ g (Ty↝ f T)) (Tm↝ g (Ty↝ f T) (Tm↝ f T t))) (Slc↝ g (Ty↝ f T)) (Slc↝ f T) ⟩
        (sub Cᵇ (Ty↝ g (Ty↝ f T)) (Tm↝ g (Ty↝ f T) (Tm↝ f T t))) ○ ((Slc↝ g (Ty↝ f T)) ○ (Slc↝ f T))
      ∎
  ○-homomorphism {C = C} {Aᵇ = Aᵇ} {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg .var≡ T = {!  compPathP (λ i → (Tm↝ (Slc↝ g (Ty↝ f T)) (Ty↝ (wk≡ Hf T i) T) (var≡ Hf T i))) (var≡ Hg (Ty↝ f T))  !}   
  ○-homomorphism {Aᵇ = Aᵇ} {Bᵇ = Bᵇ} {Cᵇ = Cᵇ} {f = f} {g = g} Hf Hg .SlcHomomorphism T = ○-homomorphism (SlcHomomorphism Hf T) (SlcHomomorphism Hg (Ty↝ f T))


  -- -- next try for substitutions
{-}
  data BSubst {B : TyTmStr} (Bᵇ : PreBSystem B) : (Γ : Ctxt B) → Type where
    ϵ : BSubst Bᵇ ε
    _►_ : {T : Typ B} {Γ : Ctxt (Slc B T)}
          → (t : Tm (Slc B T) (Ty↝ (wk Bᵇ T) T))
          → BSubst (slc Bᵇ T) Γ 
          → BSubst Bᵇ (T ⊳ Γ)


  data BSubst' {B : TyTmStr} (Bᵇ : PreBSystem B) : (Γ : Ctxt B) → Ctxt (TopTyTm Γ) → Type where
    ϵ : (Γ : Ctxt B) → BSubst' Bᵇ Γ ε
    _►_ : (Γ : Ctxt B)
      → (T : Typ (TopTyTm Γ)) (Δ : Ctxt (Slc (TopTyTm Γ) T))
      → (t : Tm (TopTyTm Γ) T)
      → BSubst' Bᵇ Γ (SubCtxt (TopPre Bᵇ Γ) T t Δ) 
      → BSubst' Bᵇ Γ (T ⊳ Δ) 

  VarSub : {B : TyTmStr} (Bᵇ : PreBSystem B) (T : Typ B) → BSubst' Bᵇ (T ⊳ ε) (Ty↝ (wk Bᵇ T) T ⊳ ε)
  VarSub Bᵇ T = _►_ (T ⊳ ε) (Ty↝ (wk Bᵇ T) T) ε (var Bᵇ T) (ϵ (T ⊳ ε)) 

  NonDepBSubst : {B : TyTmStr} (Bᵇ : PreBSystem B) → Ctxt B → Ctxt B → Type 
  NonDepBSubst Bᵇ Γ Δ = BSubst' Bᵇ Γ (AppCtxt Δ (wkCtxt Bᵇ Γ))

-}
  
  -- -- --

  record BSystem (A : TyTmStr) (Aᵇ : PreBSystem A) : Type where
    coinductive
    field
      wk-is-homomorphism : (T : Typ A) → is-homomorphism Aᵇ (slc Aᵇ T) (wk Aᵇ T) 
      sub-is-homomorphism : (T : Typ A) → (t : Tm A T) → is-homomorphism  (slc Aᵇ T) Aᵇ (sub Aᵇ T t)
      sub-of-wk-Tm : {T : Typ A} (t : Tm A T) → ((sub Aᵇ T t) ○ (wk Aᵇ T)) ≡ (idStr A)
      sub-of-wk-Typ : (T : Typ A) → ((sub (slc Aᵇ T) (Ty↝ (Aᵇ .wk T) T) (var Aᵇ T)) ○ (Slc↝ (wk Aᵇ T)) T) ≡ (idStr (Slc A T))
      Variable-sub : {T : Typ A} → (t : Tm A T) → (transport (λ i → (Tm A ((Ty↝ (sub-of-wk-Tm t i)) T))) (Tm↝ (sub Aᵇ T t) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T))) ≡ t
      BSlc : (T : Typ A) → BSystem (Slc A T) (slc Aᵇ T) 
  
  open BSystem

  -- -- -- Isomorphism between terms and homs

  record SubHom {A : TyTmStr} (Aᵇ : PreBSystem A) (T : Typ A) : Type where
    field
      f : (Slc A T) ↝ A
      sect : (f ○ (wk Aᵇ T)) ≡ idStr A
  
  open SubHom

  ToTm : {A : TyTmStr} {Aᵇ : PreBSystem A} {T : Typ A} → SubHom Aᵇ T → Tm A T
  ToTm {A} {Aᵇ} {T} sh = transport (λ i → Tm A ((Ty↝ (sect sh i)) T)) (Tm↝ (f sh) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T)) 

  ToHom : {A : TyTmStr} (Aᵇ : PreBSystem A) (AS : BSystem A Aᵇ) {T : Typ A} (t : Tm A T) → SubHom Aᵇ T 
  ToHom {A} Aᵇ AS {T} t .f = sub Aᵇ T t
  ToHom {A} Aᵇ AS {T} t .sect = sub-of-wk-Tm AS t

  Rinv : {A : TyTmStr} (Aᵇ : PreBSystem A) (AS : BSystem A Aᵇ) {T : Typ A} (t : Tm A T) → ToTm (ToHom Aᵇ AS t) ≡ t
  Rinv Aᵇ AS t = Variable-sub AS t 

  Linv : {A : TyTmStr} {Aᵇ : PreBSystem A} (AS : BSystem A Aᵇ) {T : Typ A} (sh : SubHom Aᵇ T) → ToHom Aᵇ AS (ToTm sh) ≡ sh
  Linv AS sh i .f .Ty↝ x = {!   !}
  Linv AS sh i .f .Tm↝ T x = {!   !}
  Linv AS sh i .f .Slc↝ T = {!   !}
  Linv AS sh i .sect = {!   !}

  TopBSys : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctxt B) 
    → BSystem (TopTyTm Γ) (TopPre Bᵇ Γ)
  TopBSys BS ε = BS
  TopBSys BS (T ⊳ Γ) = TopBSys (BSystem.BSlc BS T) Γ


  WkCtxtSort : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (T : Typ B) → (wk (slc Bᵇ T) (Ty↝ (wk Bᵇ T) T)) ○ (wk Bᵇ T) ≡ ((Slc↝ (wk Bᵇ T) T) ○ (wk Bᵇ T))
  WkCtxtSort BS T = sym (wk≡ (wk-is-homomorphism BS T) T)

  wkCtxtIsHomomorphism : {B : TyTmStr} {Bᵇ : PreBSystem B} (BS : BSystem B Bᵇ) (Γ : Ctxt B) → is-homomorphism Bᵇ (TopPre Bᵇ Γ) (wkCtxt Bᵇ Γ)
  wkCtxtIsHomomorphism {Bᵇ = Bᵇ} BS ε = {! IdIsHomomorphism Bᵇ !}
  wkCtxtIsHomomorphism BS (T ⊳ Γ) = ○-homomorphism (wk-is-homomorphism BS T) (wkCtxtIsHomomorphism (BSlc BS T) Γ)

  transportSplitTy↝ : {A B C D : TyTmStr} (p : C ≡ D) (f : A ↝ B) (g : B ↝ C) (T : Typ A)
      → Ty↝ (transport (λ i → (A ↝ (p i))) (g ○ f)) T ≡ (Ty↝ ((transport (λ i → B ↝ (p i)) g) ○ f) T)
  transportSplitTy↝ p f g T i = sym ((cong (λ x → (transp (λ i₁ → Typ (p i₁)) i0 (Ty↝ g x))) ((transportRefl (Ty↝ f T)))) 
      ∙ (sym (cong (λ x → transp (λ i₁ → Typ (p i₁)) i0 (Ty↝ g (Ty↝ f x))) (transportRefl T)))) i

  transportSplit : {A B C D : TyTmStr} (p : C ≡ D) (f : A ↝ B) (g : B ↝ C) → transport (λ i → (A ↝ (p i))) (g ○ f) ≡ ((transport (λ i → B ↝ (p i)) g) ○ f)
  transportSplit {A = A} {B = B} {C = C} {D = D} refl f g = {!    !}

  
   
      
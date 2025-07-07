

open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

module BSystems where

  record TyTmStr : Type₁ where 
    coinductive
    field
      Typ : Type -- this is just X itself
      Tm : Typ → Type -- this is delta^-1
      Slc : Typ → TyTmStr -- this is ft^-1

  open TyTmStr

  proj-Typ : (A B : TyTmStr) (ɣ : A ≡ B) → (Typ A ≡ (Typ B))
  proj-Typ A B ɣ i = Typ (ɣ i)

  proj-Slc : (A B : TyTmStr) (ɣ : A ≡ B) (T : Typ A) (T' : Typ B) (ɣ' : (PathP (λ i → (Typ (ɣ i))) T T')) → (Slc A T) ≡ (Slc B T')
  proj-Slc A B ɣ T T' ɣ' i = Slc (ɣ i) (ɣ' i)

  -- -- -- Contexts

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
  TypesInCtx {B} ε = Typ B
  TypesInCtx (T ⊳ Γ) = TypesInCtx Γ

  TermsInCtx : {B : TyTmStr} (Γ : Ctxt B) → (T : (TypesInCtx Γ)) → Type
  TermsInCtx {B} ε T = Tm B T
  TermsInCtx (T₁ ⊳ Γ) T = TermsInCtx Γ T

  record _↝_ (A B : TyTmStr) : Type where
    coinductive
    field
      Ty↝ : Typ A → Typ B
      Tm↝ : (T : Typ A) → Tm A T → Tm B (Ty↝ T)
      Slc↝ : (T : Typ A) → Slc A T ↝ Slc B (Ty↝ T)

  open _↝_

  proj-ty : {A B : TyTmStr} (f g : A ↝ B) → f ≡ g → (T : Typ A) → Ty↝ f T ≡ Ty↝ g T
  proj-ty f g p T i = Ty↝ (p i) T 

  proj-tm : {A B : TyTmStr} (f g : A ↝ B) → (p : f ≡ g) → (T : Typ A) (t : Tm A T) → PathP (λ i → Tm B (proj-ty f g p T i)) (Tm↝ f T t) (Tm↝ g T t)
  proj-tm {A} {B} f g p T t i = Tm↝ (p i) T t 

  proj-slc : {A B : TyTmStr} (f g : A ↝ B) → (p : f ≡ g) → (T : Typ A) → PathP (λ i → (Slc A T) ↝ (Slc B (proj-ty f g p T i))) (Slc↝ f T) (Slc↝ g T)
  proj-slc f g p T i = Slc↝ (p i) T

  record ↝-bi-sim {A B C : TyTmStr} (f : A ↝ B) (g : A ↝ C) (ɣ : B ≡ C) : Type where
     coinductive
     field
       Ty-eq : (T : Typ A) → (PathP (λ i → (Typ (ɣ i))) (Ty↝ f T) (Ty↝ g T))
       Tm-eq : (T : Typ A) (t : Tm A T)  → PathP (λ i → Tm (ɣ i) (Ty-eq T i)) (Tm↝ f T t) (Tm↝ g T t)
       Slc-eq : (T : Typ A) → ↝-bi-sim (Slc↝ f T) (Slc↝ g T) (proj-Slc B C ɣ (Ty↝ f T) (Ty↝ g T) (Ty-eq T))

  --  -- PathP (λ i → (Slc A T) ↝ (Slc B (Ty-eq i T))) (Slc↝ f T) (Slc↝ g T)
  -- ↝-bi-sim (Slc↝ f T) (Slc↝ g T)
  -- proj-Slc B C ɣ (Ty↝ f T) (Ty↝ g T)
  -- (T : Typ A) (t : Tm A T) → PathP (λ i → (Tm B (Ty-eq i T))) (Tm↝ f T t) (Tm↝ g T t)

  open ↝-bi-sim

  ↝-≡-intro : {A B C : TyTmStr} (f : A ↝ B) (g : A ↝ C) (ɣ : B ≡ C) (β : ↝-bi-sim f g ɣ) → (PathP (λ i → (A ↝ (ɣ i))) f g) 
  ↝-≡-intro f g ɣ β i .Ty↝ T = Ty-eq β T i
  ↝-≡-intro f g ɣ β i .Tm↝ T t = Tm-eq β T t i
  ↝-≡-intro {B = B} {C = C} f g ɣ β i .Slc↝ T = ↝-≡-intro (Slc↝ f T) (Slc↝ g T) (proj-Slc B C ɣ (Ty↝ f T) (Ty↝ g T) (Ty-eq β T)) (Slc-eq β T) i 

  record PreBSystem (A : TyTmStr) : Type where
    coinductive
    field
      wk : (T : Typ A) → A ↝ Slc A T
      sub : (T : Typ A) (t : Tm A T) → Slc A T ↝ A
      var : (T : Typ A) → Tm (Slc A T) (Ty↝ (wk T) T)
      slc : (T : Typ A) → PreBSystem (Slc A T) 

  open PreBSystem
  
  TopPre : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) → (PreBSystem (TopTyTm Γ))
  TopPre Bᵇ ε = Bᵇ
  TopPre Bᵇ (T ⊳ Γ) = TopPre (slc Bᵇ T) Γ

  record is-homomorphism (A B : TyTmStr) (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (ϕ : A ↝ B) : Type where
    coinductive
    field
      wk≡Ty : (T U : Typ A) → Ty↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) U) ≡ Ty↝ (wk Bᵇ (ϕ .Ty↝ T)) (Ty↝ ϕ U)
      -- Does this need to be a PathP?
      wk≡Tm : (T : Typ A) → (t : Tm A T) → (Tm↝ (Slc↝ ϕ T) (Ty↝ (wk Aᵇ T) T) (Tm↝ (wk Aᵇ T) T t)) 
          ≡ transport (λ i → (Tm (Slc B (Ty↝ ϕ T)) (wk≡Ty T T (~ i)))) (Tm↝ (wk Bᵇ (Ty↝ ϕ T)) (Ty↝ ϕ T) (Tm↝ ϕ T t)) 
      sub≡Ty : (T : Typ A) → (t : Tm A T) → (U : Typ (Slc A T)) → Ty↝ ϕ (Ty↝ (sub Aᵇ T t) U) ≡ Ty↝ (sub Bᵇ (Ty↝ ϕ T) (Tm↝ ϕ T t)) (Ty↝ (Slc↝ ϕ T) U)
      -- Does this need to be a PathP?
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

  AppCtxt : {B : TyTmStr} {A : TyTmStr} (Γ : Ctxt A) (f : A ↝ B) → (Ctxt B)
  AppCtxt ε f = ε
  AppCtxt (T ⊳ Γ) f = (Ty↝ f T) ⊳ (AppCtxt Γ (Slc↝ f T))

  SubCtxt : {B : TyTmStr} (Bᵇ : PreBSystem B) (T : Typ B) (t : Tm B T) (Γ : Ctxt (Slc B T)) → (Ctxt B)
  SubCtxt Bᵇ T t Γ = AppCtxt Γ (sub Bᵇ T t)

  wkCtxt : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) → (B ↝ (TopTyTm Γ))
  wkCtxt {B} Bᵇ ε = idStr B
  wkCtxt Bᵇ (T ⊳ Γ) = (wkCtxt (slc Bᵇ T) Γ) ○ (wk Bᵇ T)

  SlcHomCtxt : {A B : TyTmStr} (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (Γ : Ctxt A) (f : A ↝ B) → ((TopTyTm Γ) ↝ (TopTyTm (AppCtxt Γ f)))
  SlcHomCtxt Aᵇ Bᵇ ε f = f
  SlcHomCtxt Aᵇ Bᵇ (T ⊳ Γ) f = SlcHomCtxt (slc Aᵇ T) (slc Bᵇ (Ty↝ f T)) Γ (Slc↝ f T) 

  -- -- -- Substitutions

  -- this should basically be substitution, though I would like to turn this into a morphism somehow
  data ListOfTerms {B : TyTmStr} (Bᵇ : PreBSystem B) : (Γ : Ctxt B) → Type where
    e : ListOfTerms Bᵇ ε
    cnsTy : (T : Typ B) (Γ' : Ctxt (Slc B T)) → (ɣ : ListOfTerms (slc Bᵇ T) Γ') → (ListOfTerms Bᵇ (T ⊳ Γ'))
    cnsTm : (T : Typ B) (t : Tm B T) (Γ' : Ctxt (Slc B T)) → (ɣ : ListOfTerms (slc Bᵇ T) Γ') → (ListOfTerms Bᵇ (T ⊳ Γ'))

  AppListOfTerms : {A : TyTmStr} {B : TyTmStr} (Aᵇ : PreBSystem A) (Bᵇ : PreBSystem B) (Γ : Ctxt A) (f : A ↝ B) (L : ListOfTerms Aᵇ Γ) → (ListOfTerms Bᵇ (AppCtxt Γ f))
  AppListOfTerms Aᵇ Bᵇ Γ f e = e
  AppListOfTerms Aᵇ Bᵇ Γ f (cnsTy T Γ' L) = cnsTy (Ty↝ f T) (AppCtxt Γ' (Slc↝ f T)) (AppListOfTerms (slc Aᵇ T) (slc Bᵇ (Ty↝ f T)) Γ' (Slc↝ f T) L)
  AppListOfTerms Aᵇ Bᵇ Γ f (cnsTm T t Γ' L) = cnsTm (Ty↝ f T) (Tm↝ f T t) (AppCtxt Γ' (Slc↝ f T)) (AppListOfTerms (slc Aᵇ T) (slc Bᵇ (Ty↝ f T)) Γ' (Slc↝ f T) L) 

  SubListOfTerms : {B : TyTmStr} (Bᵇ : PreBSystem B) (T : Typ B) (t : Tm B T) (Γ : Ctxt (Slc B T)) (L : ListOfTerms (slc Bᵇ T) Γ) → (ListOfTerms Bᵇ (SubCtxt Bᵇ T t Γ))
  SubListOfTerms Bᵇ T t Γ L = AppListOfTerms (slc Bᵇ T) Bᵇ Γ (sub Bᵇ T t) L

  {-# TERMINATING #-} -- this should hopefully be fixable but we leave it in here to test the idea
  SubstCtxt : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) (L : ListOfTerms Bᵇ Γ) → (Ctxt B)
  SubstCtxt Bᵇ ε e = ε
  SubstCtxt Bᵇ Γ (cnsTy T Γ' L) = T ⊳ (SubstCtxt (slc Bᵇ T) Γ' L)
  SubstCtxt Bᵇ Γ (cnsTm T t Γ' L) = SubstCtxt Bᵇ (SubCtxt Bᵇ T t Γ') (SubListOfTerms Bᵇ T t Γ' L)

  SubCtxtTyStep : {B : TyTmStr} (Bᵇ : PreBSystem B) (T' : Typ B) (t : Tm B T') (Γ' : Ctxt (Slc B T')) (T : Typ (TopTyTm Γ')) → (Typ (TopTyTm (SubCtxt Bᵇ T' t Γ')))
  SubCtxtTyStep Bᵇ T' t Γ' T = Ty↝ (SlcHomCtxt (slc Bᵇ T') Bᵇ Γ' (sub Bᵇ T' t)) T

  SubCtxtTmStep : {B : TyTmStr} (Bᵇ : PreBSystem B) (T' : Typ B) (t : Tm B T') (Γ' : Ctxt (Slc B T')) (T : Typ (TopTyTm Γ')) (t' : Tm (TopTyTm Γ') T) 
      → (Tm (TopTyTm (SubCtxt Bᵇ T' t Γ')) (SubCtxtTyStep Bᵇ T' t Γ' T))
  SubCtxtTmStep Bᵇ T' t Γ' T t' = Tm↝ (SlcHomCtxt (slc Bᵇ T') Bᵇ Γ' (sub Bᵇ T' t)) T t'

  -- {-# TERMINATING #-}
  -- SubstFun : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) (L : ListOfTerms Bᵇ Γ) → ((TopTyTm Γ) ↝ (TopTyTm (SubstCtxt Bᵇ Γ L)))
  -- SubstFun {B} Bᵇ Γ e = idStr B
  -- SubstFun Bᵇ Γ (cnsTy T Γ' L) = SubstFun (slc Bᵇ T) Γ' L
  -- SubstFun Bᵇ Γ (cnsTm T t Γ' L) .Ty↝ T' = Ty↝ (SubstFun Bᵇ (SubCtxt Bᵇ T t Γ') (SubListOfTerms Bᵇ T t Γ' L)) (SubCtxtTyStep Bᵇ T t Γ' T')
  -- SubstFun Bᵇ Γ (cnsTm T t Γ' L) .Tm↝ T' t' = Tm↝ (SubstFun Bᵇ (SubCtxt Bᵇ T t Γ') (SubListOfTerms Bᵇ T t Γ' L)) (SubCtxtTyStep Bᵇ T t Γ' T') (SubCtxtTmStep Bᵇ T t Γ' T' t')
  -- SubstFun Bᵇ Γ (cnsTm T t Γ' L) .Slc↝ T' = {!    !}

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
  
  record BSystem (A : TyTmStr) (Aᵇ : PreBSystem A) : Type where
    coinductive
    field
      wk-is-homomorphism : (T : Typ A) → is-homomorphism A (Slc A T) Aᵇ (slc Aᵇ T) (wk Aᵇ T) 
      sub-is-homomorphism : (T : Typ A) → (t : Tm A T) → is-homomorphism (Slc A T) A (slc Aᵇ T) Aᵇ (sub Aᵇ T t)
      sub-of-wk-Tm : {T : Typ A} (t : Tm A T) → ((sub Aᵇ T t) ○ (wk Aᵇ T)) ≡ (idStr A)
      sub-of-wk-Typ : (T : Typ A) → ((sub (slc Aᵇ T) (Ty↝ (Aᵇ .wk T) T) (var Aᵇ T)) ○ (Slc↝ (wk Aᵇ T)) T) ≡ (idStr (Slc A T))
      Variable-sub : {T : Typ A} → (t : Tm A T) → (transport (λ i → (Tm A ((Ty↝ (sub-of-wk-Tm t i)) T))) (Tm↝ (sub Aᵇ T t) (Ty↝ (wk Aᵇ T) T) (var Aᵇ T))) ≡ t
      BSlc : (T : Typ A) → BSystem (Slc A T) (slc Aᵇ T) -- this maybe makes SlcHomomorphism redundant at least from a BSystem viewpoint


  -- Eric's substitution setup
  data Subst {B : TyTmStr} (Bᵇ : PreBSystem B) : (Γ : Ctxt B) → Type where
    ϵ : Subst Bᵇ ε
    _►_ : {T : Typ B} {Γ : Ctxt (Slc B T)}
          → (t : Tm B T)
          → Subst (slc Bᵇ T) Γ 
          → Subst Bᵇ (T ⊳ Γ)
    
  ApplySubst : {B : TyTmStr} (Bᵇ : PreBSystem B) (Γ : Ctxt B) (σ : Subst Bᵇ Γ) → TopTyTm Γ ↝ B 
  ApplySubst {B} Bᵇ Γ ϵ = idStr B
  ApplySubst {B} Bᵇ _ (_►_ {T} {Γ} t σ) = sub Bᵇ T t ○ ApplySubst (slc Bᵇ T) Γ σ

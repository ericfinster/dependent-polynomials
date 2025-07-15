--
--  DepPoly.agda - Dependent Polynomials
--

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import TyStr 

module DepPoly where

  record DepPoly (𝕊 𝕋 : TyStr) : Type₁ where
    coinductive
    field
      Tm : Ctx 𝕊 → Ty 𝕋 → Type
      ⇑ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm Γ T)
        → DepPoly ⌈ Γ ⌉ (𝕋 // T)

  open DepPoly public 
  
  -- needs a dependent path but I'm not sure how to define it
  -- maybe this can be done using a substitution
  DepPoly-≡-intro : {𝕊 𝕋 : TyStr} {P M : DepPoly 𝕊 𝕋} 
      → (Tm-≡ : (Γ : Ctx 𝕊) (T : Ty 𝕋) → (Tm P Γ T) ≡ (Tm M Γ T))
      → (⇑-≡ : (Γ : Ctx 𝕊) (T : Ty 𝕋) → PathP (λ i → Tm-≡ Γ T i
             → DepPoly ⌈ Γ ⌉ (𝕋 // T)) (⇑ P) (⇑ M))
      → (P ≡ M)
  DepPoly-≡-intro Tm-≡ ⇑-≡ i .Tm Γ T = Tm-≡ Γ T i
  DepPoly-≡-intro Tm-≡ ⇑-≡ i .⇑ {Γ} {T} t = ⇑-≡ Γ T i t


  data Subst {𝕊 𝕋 : TyStr} (M : DepPoly 𝕊 𝕋) : Ctx 𝕊 → Ctx 𝕋 → Type where
    ● : (Γ : Ctx 𝕊) → Subst M Γ ϵ
    cns : (Γ : Ctx 𝕊) (T : Ty 𝕋) (t : Tm M Γ T)
      → (Γ' : Ctx ⌈ Γ ⌉)
      → (Δ' : Ctx (𝕋 // T))
      → Subst (⇑ M t) Γ' Δ'
      → Subst M (Γ ++ Γ') (T ► Δ') 
  
  ⌈_⌉s : {𝕊 𝕋 : TyStr} {M : DepPoly 𝕊 𝕋}
    → {Γ : Ctx 𝕊} {Δ : Ctx 𝕋}
    → Subst M Γ Δ
    → DepPoly ⌈ Γ ⌉ ⌈ Δ ⌉
  ⌈_⌉s {M = M} (● Γ) .Tm Γ' x₁ = M .Tm (Γ ++ Γ') x₁
  ⌈_⌉s {𝕋 = 𝕋} {M = M} {Γ} (● Γ) .⇑ {Γ₁} {T} t = transport (λ i → (DepPoly (++-ceil Γ Γ₁ i)) (𝕋 // T)) (M .⇑ t)
  ⌈_⌉s {M = M} (cns Γ T t Γ' Δ' σ) = transport (λ i → DepPoly (++-ceil Γ Γ' (~ i)) ⌈ Δ' ⌉) ⌈ σ ⌉s 

  -- ++-sub : {𝕊 𝕋 : TyStr} {M : DepPoly 𝕊 𝕋}
  --   → {Γ : Ctx 𝕊} {Δ : Ctx 𝕋}
  --   → (ɣ : Subst M Γ Δ) → (Γ' : Ctx ⌈ Γ ⌉) (Δ' : Ctx ⌈ Δ ⌉)
  --   → (ɣ' : Subst ⌈ ɣ ⌉s Γ' Δ')
  --   → (Subst M (Γ ++ Γ') (Δ ++ Δ'))
  -- ++-sub (● _) Γ' Δ' ɣ' = {!   !}
  -- ++-sub (cns Γ T t Γ'' Δ'' ɣ) Γ' Δ' ɣ' = {!  ++-sub ɣ ? Δ'  !}

  tmToSubst : {𝕊 𝕋 : TyStr} {P : DepPoly 𝕊 𝕋}
    → {Γ : Ctx 𝕊} {A : Ty 𝕋} (t : Tm P Γ A)
    → Subst P Γ (A ► ϵ)
  tmToSubst {P = P} {Γ} {A} t =
    transport (λ i → Subst P (++-unit-left Γ i) (A ► ϵ)) (cns Γ A t ϵ ϵ (● ϵ)) 

  infixl 30 _⊚_
  
  _⊚_ : {𝕊 𝕋 𝕍 : TyStr} → DepPoly 𝕊 𝕋 → DepPoly 𝕋 𝕍 → DepPoly 𝕊 𝕍
  Tm (_⊚_ {𝕋 = 𝕋} M N) Γ T =
    Σ[ Δ ∈ Ctx 𝕋 ]
    Σ[ σ ∈ Subst M Γ Δ ]
    Tm N Δ T 
  ⇑ (M ⊚ N) (Δ , σ , t) = ⌈ σ ⌉s ⊚ ⇑ N t

{-
  _*_ : {𝕋 : TyStr} {M : DepPoly 𝕋 𝕋} → {Γ Φ Δ : Ctx 𝕋} → (ɣ : Subst M Γ Φ) 
      → (φ : Subst M Φ Δ) → (Subst M Γ Δ)
  _*_ {𝕋} {M} {Γ} {Φ} {Δ} ɣ (● .Φ) = ● Γ
  _*_ {𝕋} {M} {Γ} {Φ} {Δ} ɣ (cns Γ₁ T t Γ' Δ' φ) = cns Γ T (⌈ ɣ ⌉s .Tm Γ₁ t) Γ' Δ' (ɣ * φ)
-}

  data IdTm (𝕋 : TyStr) : Ctx 𝕋 → Ty 𝕋 → Type where
    idT : (T : Ty 𝕋) → IdTm 𝕋 (T ► ϵ) T 

  IdPoly : (𝕋 : TyStr) → DepPoly 𝕋 𝕋
  Tm (IdPoly 𝕋) = IdTm 𝕋
  ⇑ (IdPoly 𝕋) (idT T) = IdPoly (𝕋 // T)

  idSubst : {𝕋 : TyStr} (Γ : Ctx 𝕋) → Subst (IdPoly 𝕋) Γ Γ
  idSubst ϵ = (● ϵ)
  idSubst (T ► Γ) = cns (T ► ϵ) T (idT T) Γ Γ (idSubst Γ)

  infixr 20 _⇒_
  
  record _⇒_ {𝕊 𝕋 : TyStr} (P Q : DepPoly 𝕊 𝕋) : Type where
    coinductive
    field
      Tm⇒ : {Γ : Ctx 𝕊} {T : Ty 𝕋} → Tm P Γ T → Tm Q Γ T
      ⇑⇒ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm P Γ T)
        → (⇑ P t) ⇒ (⇑ Q (Tm⇒ t)) 

  open _⇒_ public

  -- Substitutions are functorial
  Subst⇒ : {𝕊 𝕋 : TyStr} {P Q : DepPoly 𝕊 𝕋} (f : P ⇒ Q)
    → {Γ : Ctx 𝕊} {Δ : Ctx 𝕋}
    → Subst P Γ Δ
    → Subst Q Γ Δ
  Subst⇒ {Q = Q} f (● Γ) = ● {M = Q} Γ 
  Subst⇒ {P = P} {Q} f (cns Γ T t Γ' Δ' σ) =
    cns Γ T (Tm⇒ f t) Γ' Δ' (Subst⇒ (⇑⇒ f t) σ)


  postulate

    ⌈_∣_⌉⇒ : {𝕊 𝕋 : TyStr} {P Q : DepPoly 𝕊 𝕋} (f : P ⇒ Q)
      → {Γ : Ctx 𝕊} {Δ : Ctx 𝕋} (σ : Subst P Γ Δ)
      → ⌈ σ ⌉s ⇒ ⌈ Subst⇒ f σ ⌉s
  -- ⌈ f ∣ ● _ ⌉⇒ .Tm⇒ x = f. Tm⇒ x
  -- ⌈ f ∣ ● _ ⌉⇒ .⇑⇒ t = {!   !}
  -- ⌈ f ∣ cns Γ T t Γ' Δ' σ ⌉⇒ = {! transport (λ i → DepPoly (++-ceil Γ Γ' (~ i)) ⌈ Δ' ⌉)  !}

  -- ⌈ ⇑⇒ f t ∣ σ ⌉⇒


  -- ⊚ is functorial in each argument
  ⊚-func-left : {𝕊 𝕋 𝕍 : TyStr} {P Q : DepPoly 𝕊 𝕋} (f : P ⇒ Q)
    → (R : DepPoly 𝕋 𝕍)
    → P ⊚ R ⇒ Q ⊚ R
  Tm⇒ (⊚-func-left f R) (Γ , σ , t) = Γ , Subst⇒ f σ , t
  ⇑⇒ (⊚-func-left f R) (Γ , σ , t) = ⊚-func-left ⌈ f ∣ σ ⌉⇒ (⇑ R t)

  ⊚-func-right : {𝕊 𝕋 𝕍 : TyStr} (P : DepPoly 𝕊 𝕋) 
    → {Q R : DepPoly 𝕋 𝕍} (f : Q ⇒ R)
    → P ⊚ Q ⇒ P ⊚ R
  Tm⇒ (⊚-func-right P f) (Γ , σ , t) = Γ , σ , Tm⇒ f t
  ⇑⇒ (⊚-func-right P f) (Γ , σ , t) = ⊚-func-right (⌈ σ ⌉s) (⇑⇒ f t)

  infix 10 [_≅_↓_]
  
  record [_≅_↓_] {𝕊 𝕋 : TyStr} {P Q R : DepPoly 𝕊 𝕋} (f : P ⇒ Q) (g : P ⇒ R) (p : Q ≡ R) : Type where
    coinductive
    field
      tm : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm P Γ T)
        → PathP (λ i → Tm (p i) Γ T) (Tm⇒ f t) (Tm⇒ g t)
      co : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm P Γ T)
        → [ ⇑⇒ f t ≅ ⇑⇒ g t ↓ (λ i → ⇑ (p i) (tm t i)) ]

  open [_≅_↓_]
  
  to : {𝕊 𝕋 : TyStr} {P Q R : DepPoly 𝕊 𝕋} (f : P ⇒ Q) (g : P ⇒ R) (p : Q ≡ R)
    → [ f ≅ g ↓ p ] → PathP (λ i → P ⇒ (p i)) f g
  Tm⇒ (to f g p e i) t = tm e t i
  ⇑⇒ (to {P = P} {Q} {R} f g p e i) t = to (⇑⇒ f t) (⇑⇒ g t) (λ i → ⇑ (p i) (tm e t i)) (co e t) i

  -- from : {𝕊 𝕋 : TyStr} {P Q R : DepPoly 𝕊 𝕋} (f : P ⇒ Q) (g : P ⇒ R) (p : Q ≡ R)
  --   → PathP (λ i → P ⇒ (p i)) f g → [ f ≅ g ↓ p ]
  -- from = {!!} 


  --
  --  Free Monoid on a dependent polynomial 
  --
  
  data W {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋) : Ctx 𝕋 → Ty 𝕋 → Type where
    lf : (T : Ty 𝕋) → W M (T ► ϵ) T
    nd : (Δ : Ctx 𝕋) (Γ : Ctx 𝕋) (T : Ty 𝕋) 
      → (σ : Subst M Δ Γ)
      → (w : W M Γ T)
      → W M Δ T 

  _↑w_ : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋) {Γ : Ctx 𝕋} {T : Ty 𝕋}
    → W M Γ T → DepPoly ⌈ Γ ⌉ (𝕋 // T)
  _↑w_ {𝕋} M (lf T) = IdPoly (𝕋 // T)
  _↑w_ M (nd Γ Δ T σ w) = ⌈ σ ⌉s ⊚ (M ↑w w)

  Free : {𝕋 : TyStr} (M : DepPoly 𝕋 𝕋) → DepPoly 𝕋 𝕋
  Tm (Free M) = W M
  ⇑ (Free M) w = M ↑w w 


--
--  DepPoly.agda - Dependent Polynomials
--

open import Cubical.Foundations.Prelude

open import TyStr 

module DepPoly where

  record DepPoly (𝕊 𝕋 : TyStr) : Type₁ where
    coinductive
    field
      Tm : Ctx 𝕊 → Ty 𝕋 → Type
      ⇑ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm Γ T)
        → DepPoly ⌈ Γ ⌉ (𝕋 // T)

  open DepPoly

  data Subst {𝕊 𝕋 : TyStr} (M : DepPoly 𝕊 𝕋) : Ctx 𝕊 → Ctx 𝕋 → Type where
    ● : Subst M ϵ ϵ
    cns : (Γ : Ctx 𝕊) (T : Ty 𝕋) (t : Tm M Γ T)
      → (Γ' : Ctx ⌈ Γ ⌉)
      → (Δ' : Ctx (𝕋 // T))
      → Subst (⇑ M t) Γ' Δ'
      → Subst M (Γ ++ Γ') (T ► Δ') 

  ⌈_⌉s : {𝕊 𝕋 : TyStr} {M : DepPoly 𝕊 𝕋}
    → {Γ : Ctx 𝕊} {Δ : Ctx 𝕋}
    → Subst M Γ Δ
    → DepPoly ⌈ Γ ⌉ ⌈ Δ ⌉
  ⌈_⌉s {M = M} ● = M
  ⌈_⌉s {M = M} (cns Γ T t Γ' Δ' σ) =
    transport (λ i → DepPoly (++-ceil Γ Γ' (~ i)) ⌈ Δ' ⌉) ⌈ σ ⌉s 

  infixl 30 _⊚_
  
  _⊚_ : {𝕊 𝕋 𝕍 : TyStr} → DepPoly 𝕊 𝕋 → DepPoly 𝕋 𝕍 → DepPoly 𝕊 𝕍
  Tm (_⊚_ {𝕋 = 𝕋} M N) Γ T =
    Σ[ Δ ∈ Ctx 𝕋 ]
    Σ[ σ ∈ Subst M Γ Δ ]
    Tm N Δ T 
  ⇑ (M ⊚ N) (Δ , σ , t) = ⌈ σ ⌉s ⊚ ⇑ N t

  data IdTm (𝕋 : TyStr) : Ctx 𝕋 → Ty 𝕋 → Type where
    idT : (T : Ty 𝕋) → IdTm 𝕋 (T ► ϵ) T 

  IdPoly : (𝕋 : TyStr) → DepPoly 𝕋 𝕋
  Tm (IdPoly 𝕋) = IdTm 𝕋
  ⇑ (IdPoly 𝕋) (idT T) = IdPoly (𝕋 // T)

  infixr 20 _⇒_
  
  record _⇒_ {𝕊 𝕋 : TyStr} (P Q : DepPoly 𝕊 𝕋) : Type where
    coinductive
    field
      Tm⇒ : {Γ : Ctx 𝕊} {T : Ty 𝕋} → Tm P Γ T → Tm Q Γ T
      ⇑⇒ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm P Γ T)
        → (⇑ P t) ⇒ (⇑ Q (Tm⇒ t)) 

  open _⇒_ public
  
  record _≅_ {𝕊 𝕋 : TyStr} {P Q : DepPoly 𝕊 𝕋} (f g : P ⇒ Q) : Type where
    coinductive
    field
      Tm~ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm P Γ T)
        → Tm⇒ f t ≡ Tm⇒ g t
      -- ⇑~ : {Γ : Ctx 𝕊} {T : Ty 𝕋} (t : Tm P Γ T)
      --   → (⇑⇒ f t) ≅ {!(⇑⇒ g t) !} -- (⇑⇒ g t) 

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


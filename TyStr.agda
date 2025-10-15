--
--  TyStr.agda - Type Structures
--

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Bool

module TyStr where

  record TyStr : Type₁ where
    coinductive
    field
      Ty : Type
      _//_ : Ty → TyStr

  open TyStr public 

  infixl 20 _►_
  
  data Ctx (𝕋 : TyStr) : Type where
    ϵ : Ctx 𝕋 
    _►_ : (T : Ty 𝕋) → (Γ : Ctx (𝕋 // T)) → Ctx 𝕋 

  record Hom (𝕊 𝕋 : TyStr) : Type₁ where
    coinductive
    field
      ty : Ty 𝕊 → Ty 𝕋
      //Hom : (S : Ty 𝕊) → Hom (𝕊 // S) (𝕋 // (ty S))

  open Hom public

  HomCtx : {𝕊 𝕋 : TyStr} (f : Hom 𝕊 𝕋) (Γ : Ctx 𝕊) → Ctx 𝕋
  HomCtx f ϵ = ϵ
  HomCtx f (T ► Γ) = (ty f T) ► (HomCtx (//Hom f T) Γ)

  ImgStr : {𝕊 𝕋 : TyStr} (f : Hom 𝕊 𝕋) → TyStr
  ImgStr {𝕊} {𝕋} f .Ty = Σ[ T ∈ Ty 𝕊 ] Σ[ T' ∈ Ty 𝕋 ] (ty f T ≡ T')
  ImgStr f // (fst₁ , fst₂ , snd₁) = ImgStr (//Hom f fst₁)
      

  record WkStr (𝕋 : TyStr) : Type₁ where
    coinductive
    field
      wk : (T : Ty 𝕋) → Hom 𝕋 (_//_ 𝕋 T)
      liftStr : (T : Ty 𝕋) → WkStr (_//_ 𝕋 T)

  open WkStr public 


  ⌈_⌉ : {𝕋 : TyStr} → Ctx 𝕋 → TyStr
  ⌈_⌉ {𝕋} ϵ = 𝕋
  ⌈_⌉ (T ► Γ) = ⌈ Γ ⌉  

  WkCtx : {𝕋 : TyStr} (Wk : WkStr 𝕋) (Γ : Ctx 𝕋) (T : Ty 𝕋) → Ctx 𝕋
  WkCtx Wk Γ T = T ► HomCtx (wk Wk T) Γ

  CtxStep : {𝕋 : TyStr} (Γ : Ctx 𝕋) → TyStr
  CtxStep {𝕋} ϵ = 𝕋
  CtxStep {𝕋} (T ► Γ) = 𝕋 // T

  CtxSlice : {𝕋 : TyStr} (Γ : Ctx 𝕋) → (Ctx (CtxStep Γ))
  CtxSlice ϵ = ϵ
  CtxSlice (T ► Γ) = Γ 

  isEmptyCtx : {𝕋 : TyStr} (Γ : Ctx 𝕋) → Bool
  isEmptyCtx ϵ = true
  isEmptyCtx (T ► Γ) = false

  infixl 30 _++_

  _++_ : {𝕋 : TyStr} → (Γ : Ctx 𝕋) → Ctx ⌈ Γ ⌉ → Ctx 𝕋
  _++_ ϵ Δ = Δ
  _++_ (T ► Γ) Δ = T ► Γ ++ Δ

  ++-ceil : {𝕋 : TyStr} → (Γ : Ctx 𝕋) (Δ : Ctx ⌈ Γ ⌉) → ⌈ Γ ++ Δ ⌉ ≡ ⌈ Δ ⌉
  ++-ceil ϵ Δ = refl
  ++-ceil (T ► Γ) Δ = ++-ceil Γ Δ

  ++-unit-left : {𝕋 : TyStr} (Γ : Ctx 𝕋)
    → Γ ++ ϵ ≡ Γ
  ++-unit-left ϵ = refl
  ++-unit-left (T ► Γ) i = T ► ++-unit-left Γ i

  --
  --  The TyStr of Contexts 
  --

  CtxStr : TyStr → TyStr
  Ty (CtxStr 𝕋) = Ctx 𝕋
  _//_ (CtxStr 𝕋) Γ = CtxStr ⌈ Γ ⌉

  --
  --  Various Tensor Products
  --

  infixl 20 _∔_ _⊘_ 
  
  _∔_ : TyStr → TyStr → TyStr
  Ty (𝕋 ∔ 𝕊) = Ty 𝕋 ⊎ Ty 𝕊
  (𝕋 ∔ 𝕊) // inl T = (𝕋 // T) ∔ 𝕊
  (𝕋 ∔ 𝕊) // inr S = 𝕋 ∔ (𝕊 // S)

  -- This choses, arbitrarily, an order on the two ...
  ∔-pair : {𝕊 𝕋 : TyStr} → Ctx 𝕊 → Ctx 𝕋 → Ctx (𝕊 ∔ 𝕋)
  ∔-pair ϵ ϵ = ϵ
  ∔-pair ϵ (T ► Δ) = inr T ► ∔-pair ϵ Δ
  ∔-pair (T ► Γ) Δ = inl T ► ∔-pair Γ Δ

  ∔-π₁ : {𝕊 𝕋 : TyStr} → Ctx (𝕊 ∔ 𝕋) → Ctx 𝕊
  ∔-π₁ ϵ = ϵ
  ∔-π₁ (inl S ► Γ) = S ► ∔-π₁ Γ
  ∔-π₁ (inr T ► Γ) = ∔-π₁ Γ

  ∔-π₂ : {𝕊 𝕋 : TyStr} → Ctx (𝕊 ∔ 𝕋) → Ctx 𝕋
  ∔-π₂ ϵ = ϵ
  ∔-π₂ (inl S ► Γ) = ∔-π₂ Γ
  ∔-π₂ (inr T ► Γ) = T ► ∔-π₂ Γ

  -- Oh, I guess it's chosen so that this works...
  ∔-ceil : {𝕊 𝕋 : TyStr} (Γ : Ctx 𝕊) (Δ : Ctx 𝕋)
    → (⌈ ∔-pair Γ Δ ⌉) ≡ (⌈ Γ ⌉ ∔ ⌈ Δ ⌉)
  ∔-ceil ϵ ϵ = refl
  ∔-ceil ϵ (T ► Δ) = ∔-ceil ϵ Δ
  ∔-ceil (T ► Γ) Δ = ∔-ceil Γ Δ

  -- This one is non-symmetric, but I think has a closed
  -- structure.
  _⊘_ : TyStr → TyStr → TyStr
  Ty (𝕊 ⊘ 𝕋) = Ty 𝕊 ⊎ Ty 𝕋 
  (𝕊 ⊘ 𝕋) // inl S = (𝕊 // S) ⊘ 𝕋 
  (𝕊 ⊘ 𝕋) // inr T = 𝕋 // T

  ⊘-pair : {𝕊 𝕋 : TyStr} → Ctx 𝕊 → Ctx 𝕋 → Ctx (𝕊 ⊘ 𝕋)
  ⊘-pair ϵ ϵ = ϵ
  ⊘-pair ϵ (T ► Δ) = inr T ► Δ
  ⊘-pair (S ► Γ) Δ = inl S ► ⊘-pair Γ Δ

  ⊘-π₁ : {𝕊 𝕋 : TyStr} → Ctx (𝕊 ⊘ 𝕋) → Ctx 𝕊
  ⊘-π₁ ϵ = ϵ
  ⊘-π₁ (inl S ► Γ) = S ► ⊘-π₁ Γ
  ⊘-π₁ (inr T ► Γ) = ϵ

  ⊘-π₂ : {𝕊 𝕋 : TyStr} → Ctx (𝕊 ⊘ 𝕋) → Ctx 𝕋
  ⊘-π₂ ϵ = ϵ
  ⊘-π₂ (inl S ► Γ) = ⊘-π₂ Γ
  ⊘-π₂ (inr T ► Γ) = T ► Γ

  -- A product 
  _⊗_ : TyStr → TyStr → TyStr
  Ty (𝕋 ⊗ 𝕊) = Ty 𝕋 × Ty 𝕊
  _//_ (𝕋 ⊗ 𝕊) (T , S) = (𝕋 // T) ⊗ (𝕊 // S)

  -- wkStructure : {𝕋 : TyStr} (T : Ty 𝕋) → 


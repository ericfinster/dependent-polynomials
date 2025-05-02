
open import Cubical.Foundations.Prelude 
open import Cubical.Data.Sigma 

module Scratch where

  data Nat : Type where
    zero : Nat
    succ : Nat → Nat 

  three : Nat
  three = succ (succ (succ zero)) 

  record Stream (A : Type) : Type where
    coinductive
    field
      hd : A
      tl : Stream A

  open Stream
  
  get-third : (A : Type) (s : Stream A) → A
  get-third A s = hd (tl (tl (tl s)))

  iterate : (A : Type) (f : A → A) → Nat → (A → A)
  iterate A f zero = λ x → x
  iterate A f (succ n) = λ x → f (iterate A f n x)

  const : (A : Type) (a : A) → Stream A
  hd (const A a) = a
  tl (const A a)  = const A a

  record TyStr : Type₁ where
    coinductive
    field
      X : Type
      _↓_ : (x : X) → TyStr


  open TyStr 

  module _ (I : TyStr) where

    X₀ : Type
    X₀ = X I

    X₁ : X₀ → Type
    X₁ x₀ = X (I ↓ x₀)

    X₂ : (x₀ : X₀) → X₁ x₀ → Type
    X₂ x₀ x₁ = X ((I ↓ x₀) ↓ x₁) 

    -- ....

  record Span∞ (I J : TyStr) : Type₁ where
    coinductive
    field
      B : (X I) → (X J) → Type
      _⇓_ : {i : X I} {j : X J} → B i j → Span∞ (I ↓ i) (J ↓ j)

  open Span∞
  
  module _ (I J : TyStr) (S : Span∞ I J) where 

    -- (x : i) ⊢ s x : j 
    S₀ : X I → X J → Type
    S₀ = B S

    S₁ : (i : X I) (i' : X (I ↓ i))
       → (j : X J) (j' : X (J ↓ j))
       → (s : B S i j )
       → Type
    S₁ i i' j j' s = B (S ⇓ s) i' j' 

  comp-span : {I J K : Type} (S : I → J → Type) (T : J → K → Type) → (I → K → Type)
  comp-span {J = J} S T i k = Σ[ j ∈ J ] S i j × T j k  

  comp-span-∞ : {I J K : TyStr} → Span∞ I J → Span∞ J K → Span∞ I K
  comp-span-∞ S T .B = comp-span (B S) (B T)
  comp-span-∞ S T ._⇓_ (j , s , t) = comp-span-∞ (S ⇓ s) (T ⇓ t)

  infixr 20 _▸_ 
  
  data Ctx (I : TyStr) : Type where
    ϵ : Ctx I
    _▸_ : (i : X I) → Ctx (I ↓ i) → Ctx I 

  module _ (I : TyStr) where

    example : (i₀ : X I) (i₁ : X (I ↓ i₀)) (i₂ : X ((I ↓ i₀) ↓ i₁)) → Ctx I
    example i₀ i₁ i₂ = (i₀ ▸ i₁ ▸ i₂ ▸ ϵ)

  ⌈_⌉ : {I : TyStr} → Ctx I → TyStr
  ⌈_⌉ {I} ϵ = I
  ⌈_⌉ {I} (i ▸ Γ) = ⌈ Γ ⌉

  test : (I : TyStr) (i₀ : X I) (i₁ : X (I ↓ i₀)) (i₂ : X ((I ↓ i₀) ↓ i₁)) → TyStr
  test I i₀ i₁ i₂ = {!⌈ example I i₀ i₁ i₂ ⌉!} 
    
  CtxStr : TyStr → TyStr
  CtxStr I .X = Ctx I
  CtxStr I ._↓_ Γ = CtxStr ⌈ Γ ⌉

  module _ (I : TyStr)
    (i₀ : X I) (i₁ : X (I ↓ i₀)) (i₂ : X ((I ↓ i₀) ↓ i₁))
    (i₃ : X (((I ↓ i₀) ↓ i₁) ↓ i₂))
    where

    ex₀ : X (CtxStr I) 
    ex₀ = i₀ ▸ i₁ ▸ ϵ

    ex₁ : X (CtxStr I ↓ ex₀)
    ex₁ = i₂ ▸ i₃ ▸ ϵ

  DepPoly : (I J : TyStr) → Type₁
  DepPoly I J = Span∞ (CtxStr I) J

  module _ (I : TyStr) (J : TyStr)
    -- (i₀ : X I) (i₁ : X (I ↓ i₀)) (i₂ : X ((I ↓ i₀) ↓ i₁))
    -- (i₃ : X (((I ↓ i₀) ↓ i₁) ↓ i₂))
    -- (j₀ : X J) (j₁ : X (J ↓ j₀))
    (D : DepPoly I J) 
    where

    -- (x : i₀) (y : i₁) ⊢ s (x , y) : j 
    BinaryOp : (i₀ : X I) (i₁ : X (I ↓ i₀)) (j : X J) → Type 
    BinaryOp i₀ i₁ j = B D (i₀ ▸ i₁ ▸ ϵ) j 

    BinaryOp↓ : (i₀ : X I) (i₁ : X (I ↓ i₀)) (j₀ : X J)
      → (s : BinaryOp i₀ i₁ j₀)
      → (i₂ : X ((I ↓ i₀) ↓ i₁)) (i₃ : X (((I ↓ i₀) ↓ i₁) ↓ i₂))
      → (j₁ : X (J ↓ j₀))
      → Type
    BinaryOp↓ i₀ i₁ j₀ s i₂ i₃ j₁ = B (D ⇓ s) (i₂ ▸ i₃ ▸ ϵ) j₁ 
  

  BinaryOpType : (I₀ : Type) (I₁ : I₀ → Type) (J : Type) → Type
  BinaryOpType I₀ I₁ J = (i₀ : I₀) → (i₁ : I₁ i₀) → J

  BinaryOp↓Type : (I₀ : Type) (I₁ : I₀ → Type) (J : Type)
    → BinaryOpType I₀ I₁ J
    → (I₂ : (i₀ : I₀) → (i₁ : I₁ i₀) → Type)
    → (I₃ : (i₀ : I₀) → (i₁ : I₁ i₀) → I₂ i₀ i₁ → Type)
    → (J₁ : J → Type)
    → Type
  BinaryOp↓Type I₀ I₁ J ϕ I₂ I₃ J₁ = (i₀ : I₀) → (i₁ : I₁ i₀) → (i₂ : I₂ i₀ i₁) → (i₃ : I₃ i₀ i₁ i₂) → J₁ (ϕ i₀ i₁)  


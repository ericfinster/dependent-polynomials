--
--  Gats.agda - a universe of Gat's
--

open import Cubical.Foundations.Prelude 

module BSystemsRewrite where
  
  infix 10 _↦_
  
  postulate  
    _↦_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ

  {-# BUILTIN REWRITE _↦_ #-}  

  postulate

    𝔾 : Type
    _⇒_ : 𝔾 → 𝔾 → Type

    𝕋y : (G : 𝔾) → Type
    𝕋m : (G : 𝔾) (A : 𝕋y G) → Type
    𝔼xt : (G : 𝔾) (A : 𝕋y G) → 𝔾

    𝕋y⇒ : {G H : 𝔾} (σ : G ⇒ H) → 𝕋y G → 𝕋y H
    𝕋m⇒ : {G H : 𝔾} (σ : G ⇒ H) (A : 𝕋y G) → 𝕋m G A → 𝕋m H (𝕋y⇒ σ A) 
    𝔼xt⇒ : {G H : 𝔾} (σ : G ⇒ H) (A : 𝕋y G) → 𝔼xt G A ⇒ 𝔼xt H (𝕋y⇒ σ A)

    wk : (G : 𝔾) (A : 𝕋y G) → G ⇒ 𝔼xt G A
    var : (G : 𝔾) (A : 𝕋y G) → 𝕋m (𝔼xt G A) (𝕋y⇒ (wk G A) A) 
    sub : (G : 𝔾) (A : 𝕋y G) (a : 𝕋m G A) → 𝔼xt G A ⇒ G 

    -- Weakening is preserved by homomorphisms
    wk-𝕋y⇒ : {G H : 𝔾} (σ : G ⇒ H) 
      → (A B : 𝕋y G)
      → 𝕋y⇒ (𝔼xt⇒ σ A) (𝕋y⇒ (wk G A) B) ↦
        𝕋y⇒ (wk H (𝕋y⇒ σ A)) (𝕋y⇒ σ B)
    {-# REWRITE wk-𝕋y⇒ #-}

    wk-𝕋m⇒ : {G H : 𝔾} (σ : G ⇒ H) 
      → (A B : 𝕋y G) (b : 𝕋m G B)
      → 𝕋m⇒ (𝔼xt⇒ σ A) (𝕋y⇒ (wk G A) B) (𝕋m⇒ (wk G A) B b) ↦
        𝕋m⇒ (wk H (𝕋y⇒ σ A)) (𝕋y⇒ σ B) (𝕋m⇒ σ B b)
    {-# REWRITE wk-𝕋m⇒ #-}

    -- Variables are preserved by homomorphisms
    var-𝕋m⇒ : {G H : 𝔾} (σ : G ⇒ H) (A : 𝕋y G)
      → 𝕋m⇒ (𝔼xt⇒ σ A) (𝕋y⇒ (wk G A) A) (var G A) ↦
        var H (𝕋y⇒ σ A)
    {-# REWRITE var-𝕋m⇒ #-}

    --  Substitution is preserved by homomorphisms 
    sub-𝕋y⇒ : {G H : 𝔾} (σ : G ⇒ H)
      → (A : 𝕋y G) (a : 𝕋m G A)
      → (B : 𝕋y (𝔼xt G A))
      → 𝕋y⇒ σ (𝕋y⇒ (sub G A a) B) ↦
        𝕋y⇒ (sub H (𝕋y⇒ σ A) (𝕋m⇒ σ A a)) (𝕋y⇒ (𝔼xt⇒ σ A) B)
    {-# REWRITE sub-𝕋y⇒ #-}

    sub-𝕋m⇒ : {G H : 𝔾} (σ : G ⇒ H)
      → (A : 𝕋y G) (a : 𝕋m G A)
      → (B : 𝕋y (𝔼xt G A)) (b : 𝕋m (𝔼xt G A) B)
      → 𝕋m⇒ σ (𝕋y⇒ (sub G A a) B) (𝕋m⇒ (sub G A a) B b) ↦
        𝕋m⇒ (sub H (𝕋y⇒ σ A) (𝕋m⇒ σ A a)) (𝕋y⇒ (𝔼xt⇒ σ A) B) (𝕋m⇒ (𝔼xt⇒ σ A) B b)
    {-# REWRITE sub-𝕋m⇒ #-}

    -- Substitution in a weakend family is constant
    sub-wk-𝕋y⇒ : (G : 𝔾) (A B : 𝕋y G) (a : 𝕋m G A)
      → 𝕋y⇒ (sub G A a) (𝕋y⇒ (wk G A) B) ↦ B
    {-# REWRITE sub-wk-𝕋y⇒ #-}

    sub-wk-𝕋m⇒ : (G : 𝔾) (A B : 𝕋y G) (a : 𝕋m G A) (b : 𝕋m G B)
      → 𝕋m⇒ (sub G A a) (𝕋y⇒ (wk G A) B) (𝕋m⇒ (wk G A) B b) ↦ b
    {-# REWRITE sub-wk-𝕋m⇒ #-}

    -- Substituting a term into a variable just gives the term back
    sub-var-left : (G : 𝔾) (A : 𝕋y G) (a : 𝕋m G A)
      → 𝕋m⇒ (sub G A a) (𝕋y⇒ (wk G A) A) (var G A) ↦ a
    {-# REWRITE sub-var-left #-}

    -- Substituting a variable in a type or term does nothing
    -- sub-var-right-𝕋y⇒ : (G : 𝔾) (A : 𝕋y G)
    --   → (B : 𝕋y (𝔼xt G A)) 
    --   → 𝕋y⇒ (sub (𝔼xt G A) (𝕋y⇒ (wk G A) A) (var G A)) (𝕋y⇒ (wk (𝔼xt G A) (𝕋y⇒ (wk G A) A)) B) ↦ B

    -- Just sub-wk-𝕋y⇒ with:
    --    G = 𝔼xt G A
    --    A = (𝕋y⇒ (wk G A) A)
    --    a = (var G A)
    --    B = B

    -- sub-var-right-𝕋m⇒ : (G : 𝔾) (A : 𝕋y G)
    --   → (B : 𝕋y (𝔼xt G A)) (b : 𝕋m (𝔼xt G A) B)
    --   → 𝕋m⇒ (sub (𝔼xt G A) (𝕋y⇒ (wk G A) A) (var G A)) (𝕋y⇒ (wk (𝔼xt G A) (𝕋y⇒ (wk G A) A)) B) (𝕋m⇒ (wk (𝔼xt G A) (𝕋y⇒ (wk G A) A)) B b) ↦ b
    -- {-# REWRITE sub-var-right-𝕋m⇒ #-}


  
    -- Ty≡ : (G : 𝔾) (A B : 𝕋y G) → Type 
    -- Tm≡ : (G : 𝔾) (A : 𝕋y G) (a b : 𝕋m G A) → Type

    -- TyExt≡ : (G : 𝔾) (A B : 𝕋y G) (p : Ty≡ G A B) → A == B
    -- TmExt≡ : (G : 𝔾) (A : 𝕋y G) (a b : 𝕋m G A) → Tm≡ G A a b → a ≡ b


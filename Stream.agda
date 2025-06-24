
open import Cubical.Foundations.Prelude 

module Stream where

  record Stream (A : Type) : Type where
    coinductive
    field
      hd : A
      tail : Stream A

  open Stream
  
  hd≡ : {A : Type} {s t : Stream A} → s ≡ t → hd s ≡ hd t
  hd≡ p i = hd (p i)

  tail≡ : {A : Type} {s t : Stream A} → s ≡ t → tail s ≡ tail t
  tail≡ p i = tail (p i) 

  to≡ : {A : Type} {s t : Stream A} (h : hd s ≡ hd t) (tl : tail s ≡ tail t) → s ≡ t
  to≡ h tl i .hd = h i
  to≡ h tl i .tail = tl i

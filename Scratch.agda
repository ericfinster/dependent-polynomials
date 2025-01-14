
open import Cubical.Foundations.Prelude 


module Scratch where

  -- Just working out how coinductive extensionality works in cubical 

  record Stream (A : Type) : Type where
    coinductive
    field
      hd : A
      tl : Stream A

  open Stream
  
  record BiSim {A : Type} (S T : Stream A) : Type where
    coinductive
    field
      hd≡ : hd S ≡ hd T
      tl≡ : BiSim (tl S) (tl T)

  open BiSim
  
  claim : {A : Type} {S T : Stream A} → BiSim S T → S ≡ T
  hd (claim B i) = hd≡ B i
  tl (claim B i) = claim (tl≡ B) i

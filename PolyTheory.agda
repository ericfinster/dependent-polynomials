open import Cubical.Foundations.Prelude

open import TyStr
open import DepPoly
open import Monad

open import BSystems

module PolyTheory where

    record PolyTheory (𝕋 : TyStr) : Type₁ where
        coinductive
        field
            M : Monad 𝕋
            WkS : WknStr (Monad.P M) (Monad.P M) (Monad.P M) (Monad.μ M)
            SubS : SubStr (Monad.P M) (Monad.P M) (Monad.P M) (Monad.μ M)

    record PolyTheory2 (𝕋 : TyStr) : Type₁ where
        coinductive
        field
            M : Monad 𝕋
            WkS : WkPoly (Monad.P M)
            SubS : SubStr2 (Monad.P M) (Monad.P M) (Monad.P M) (Monad.μ M)

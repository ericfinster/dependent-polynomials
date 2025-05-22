open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit -- so we can use the empty type in ⊗-pair

open import Cubical.Data.Sum
open import Cubical.Data.Sigma

module TyStrLvl where

    record TyStrLvl (ℓ : Level) : Type (ℓ-suc ℓ) where
        coinductive
        field
            Ty : Type ℓ
            _//_ : Ty → TyStrLvl ℓ
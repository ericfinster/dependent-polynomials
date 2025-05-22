open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category


-- Catgories with terminal object

module  TCategory where

-- Categories with hom-sets
record TCategory {ℓ ℓ' : Level} (C : Category ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where 

    open Category C public

    field
        TerObj : ob  -- Terminal Object
        TermPr : ∀ {x} → Hom[ x , TerObj ] -- Terminal Projection
        TermPrUn : ∀ {x} (f : Hom[ x , TerObj ]) (g : Hom[ x , TerObj ]) → f ≡ g -- Uniqueness of terminal projection

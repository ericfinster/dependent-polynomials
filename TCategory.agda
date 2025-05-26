open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice


-- Catgories with terminal object

module  TCategory where

-- Categories with hom-sets
record TCategory {ℓ ℓ' : Level} (C : Category ℓ ℓ') : Type (ℓ-suc (ℓ-max ℓ ℓ')) where 

    open Category C public

    field
        TerObj : ob  -- Terminal Object
        TermPr : ∀ {x} → Hom[ x , TerObj ] -- Terminal Projection
        TermPrUn : ∀ {x} (f : Hom[ x , TerObj ]) (g : Hom[ x , TerObj ]) → f ≡ g -- Uniqueness of terminal projection

open TCategory
open Cubical.Categories.Constructions.Slice
open SliceOb
{-
TCat-Slice : {ℓ ℓ' : Level} {C : Category ℓ ℓ'} (c : Category.ob C) → (T : TCategory C) → (TCategory (SliceCat C c))
TCat-Slice {ℓ} {ℓ'} {C = C} c T .TerObj = {! sliceob {ℓ = ℓ} {ℓ' = ℓ'} {C = C} {c = c} C .id !}
TCat-Slice c T .TermPr = {!   !}
TCat-Slice c T .TermPrUn = {!   !}
-}
-- (TCategory {ℓ = (ℓ-max ℓ ℓ')} {ℓ' = ℓ'} (SliceCat C c))
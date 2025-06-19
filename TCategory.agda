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



TCat-Slice : {ℓ ℓ' : Level} {C : Category ℓ ℓ'} (c : Category.ob C) → (T : TCategory C) → (TCategory (SliceCat C c))
TCat-Slice {ℓ} {ℓ'} {C = C} c T .TerObj =  sliceob (id T {c})
TCat-Slice {ℓ} {ℓ'} {C} c T .TermPr {x} = slicehom (S-arr x) (⋆IdR T (S-arr x))
TCat-Slice {ℓ} {ℓ'} {C} c T .TermPrUn {x} (slicehom S-hom₁ S-comm₁) (slicehom S-hom₂ S-comm₂) = 
        SliceHom-≡-intro' C c  ((sym (⋆IdR T S-hom₁)) ∙ S-comm₁ ∙ (sym S-comm₂) ∙  (⋆IdR T S-hom₂)) 

IsId : {ℓ : Level} {C : Category ℓ ℓ} → (T : TCategory C) → (f : C [ (TerObj T) , (TerObj T) ]) → (id T {TerObj T}) ≡ f
IsId T f = TermPrUn T (id T) f




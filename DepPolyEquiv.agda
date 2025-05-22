open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.TypesOfCategories.TypeCategory

open import TyStr
open import TyStrLvl
open import TypeCatSlice
open import TCategory

module DepPolyEquiv where

    open Category
    open isTypeCategory
    open TCategory.TCategory
    
    -- Construction using levels, would require to rework DepPoly and TyStr
    TypeCatToTyStrLvl : {ℓ ℓ' ℓ'' : Level} {C : Category ℓ ℓ'} (Ter : TCategory C) → (TypeCat : (isTypeCategory {ℓ} {ℓ'} {ℓ'' = ℓ''} C)) → TyStrLvl ℓ'' -- level is wrong here, since the Types of the TypeCat are in ℓ''
    TypeCatToTyStrLvl Ter TypeCat .TyStrLvl.Ty = Ty[ TypeCat ] (TerObj Ter)
    TypeCatToTyStrLvl Ter TypeCat TyStrLvl.// x = {!   !} -- here we need slices

    -- (TypeCatToTyStrLvl (TypeCatSlice C T TypeCat))  Ty[ TypeCat ] 


    -- Using standard TyStr and requiring our Category to have sets as objects 
    TypeCatToTyStr : {ℓ ℓ' : Level} {C : Category ℓ ℓ'} (Ter : TCategory C) →  (TypeCat : (isTypeCategory {ℓ} {ℓ'} {ℓ-zero} C)) → TyStr
    TypeCatToTyStr Ter TypeCat .Ty = Ty[ TypeCat ] (TerObj Ter)
    TypeCatToTyStr Ter TypeCat ._//_ = {!   !}


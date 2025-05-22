{-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.TypesOfCategories.TypeCategory

open import TCategory

module TypeCatSlice where

    open Category -- apparently this is needed to be able to use ob 
    open isTypeCategory
    open SliceOb

    -- maybe agda is unable to infer that S-ob is actually ob C? YES THAT IS THE PROBLEM, WE DONT HAVE AN ACTUAL OBJECT!!!!!!

    TypeCatSlice : {ℓ ℓ' ℓ'' : Level} {C : Category ℓ ℓ'} {O : C. ob} (TyC : isTypeCategory {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} C) → (Ty : Ty[ TyC ] O) → (TC : TCategory C) → (isTypeCategory {ℓ = (ℓ-max ℓ ℓ')} {ℓ' = ℓ'} {ℓ'' = ℓ''} (SliceCat C (fst (cext TyC O Ty))))
    Ty[ TypeCatSlice {O = O} TyC Ty TC ] x =  {! (reindex TyC (S-arr x) (reindex TyC (snd (cext TyC O Ty)) Ty))  !} 
    TypeCatSlice TyC Ty TC .cext Γ A .fst = {! S-arr x  !}
    TypeCatSlice TyC Ty TC .cext Γ A .snd = {!   !}
    TypeCatSlice TyC Ty TC .reindex x x₁ = {!   !}
    TypeCatSlice TyC Ty TC .q⟨_,_⟩ = {!   !}
    TypeCatSlice TyC Ty TC .sq = {!   !}
    TypeCatSlice TyC Ty TC .isPB = {!   !}

    -- Ty[ TyC ] (fst (cext TyC O Ty)))
    -- (reindex TyC (S-arr x))
    -- (reindex TyC (S-arr x) (reindex TyC (snd (cext TyC O Ty)) Ty)) 




    -- I'm not sure if a TypeCat on the Slice is the right kind of object

    {-

    TypeCatSlice : {ℓ ℓ' jℓ : Level} (C : Category ℓ ℓ') → (T : ob C) →  (TyC : isTypeCategory {ℓ} {ℓ'} {ℓ'' = jℓ} C) → (isTypeCategory {ℓ'' = jℓ}  (SliceCat C T))
    Ty[ TypeCatSlice {ℓ} {ℓ'} {jℓ} C T TyC ] x = {! reindex TyC (S-arr x) (Ty[ TyC ] T) !}
    TypeCatSlice C T TyC .isTypeCategory.cext = {!   !}
    TypeCatSlice C T TyC .isTypeCategory.reindex = {!   !}
    TypeCatSlice C T TyC .isTypeCategory.q⟨_,_⟩ = {!   !}
    TypeCatSlice C T TyC .isTypeCategory.sq = {!   !}
    TypeCatSlice C T TyC .isTypeCategory.isPB = {!   !}

    -}

    -- (reindex TyC (S-arr x))
    -- ((reindex TyC (S-arr x)) (Ty[ TyC ] T))
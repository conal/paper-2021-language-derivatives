-- Star Semirings Structures
{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)
module Closed.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Level
open import Algebra.Core
open import Algebra.Structures _≈_

Starˡ : (_+_ _✲_ : Op₂ A) (𝟘 𝟙 : A) (_✯ : Op₁ A) → Set (a ⊔ ℓ)
Starˡ _+_ _✲_ 𝟘 𝟙 _✯ = ∀ x → (x ✯) ≈ (𝟙 + (x ✲ (x ✯)))

record IsClosedSemiring (_+_ _✲_ : Op₂ A) (𝟘 𝟙 : A) (_✯ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isSemiring : IsSemiring _+_ _✲_ 𝟘 𝟙
    starˡ : Starˡ _+_ _✲_ 𝟘 𝟙 _✯
  open IsSemiring isSemiring public

record IsClosedCommutativeSemiring (_+_ _✲_ : Op₂ A) (𝟘 𝟙 : A) (_✯ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isCommutativeSemiring : IsCommutativeSemiring _+_ _✲_ 𝟘 𝟙
    starˡ : Starˡ _+_ _✲_ 𝟘 𝟙 _✯

  open IsCommutativeSemiring isCommutativeSemiring public
  
  isClosedSemiring : IsClosedSemiring _+_ _✲_ 𝟘 𝟙 _✯
  isClosedSemiring = record { isSemiring = isSemiring ; starˡ = starˡ }

\begin{code}
-- {-# OPTIONS --safe #-}

module Language.Algebra {ℓ} (A : Set ℓ) where

-- Local (for now)
open import Algebra.Construct.Function using (semimodule)

open import Language A
open import Inverses
open import Language.Properties A
open Pred-Semimodule

open import Algebra.Structures {A = Lang} _⟷_

⋆-isMagma : IsMagma _⋆_
⋆-isMagma = record { isEquivalence = ⟷-isEquivalence ; ∙-cong = ⋆-cong }

⋆-isSemigroup : IsSemigroup _⋆_
⋆-isSemigroup = record { isMagma = ⋆-isMagma ; assoc = ⋆-assoc }

⋆-isMonoid : IsMonoid _⋆_ 𝟏
⋆-isMonoid = record
  { isSemigroup = ⋆-isSemigroup
  ; identity = ⋆-identity
  }

⋆-∪-isSemiringWithoutAnnihilatingZero :
  IsSemiringWithoutAnnihilatingZero _∪_ _⋆_ ∅ 𝟏
⋆-∪-isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid
  ; *-isMonoid = ⋆-isMonoid
  ; distrib = ⋆-distrib
  }

⋆-∪-isSemiring : IsSemiring _∪_ _⋆_ ∅ 𝟏
⋆-∪-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = ⋆-∪-isSemiringWithoutAnnihilatingZero
  ; zero = ⋆-zero
  }

\end{code}

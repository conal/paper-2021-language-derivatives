{-# OPTIONS --safe #-}
-- {-# OPTIONS --without-K #-}

open import Level
open import Algebra.Core
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≗_; cong; subst) renaming (refl to refl≡; sym to sym≡)
import Algebra.Structures as S

module Predicate.Algebra {ℓ : Level} {M : Set ℓ} {_∙_ : Op₂ M} {ε : M}
                         (isMonoid-M : S.IsMonoid _≡_ _∙_ ε) where

private
  variable
    A B C : Set ℓ

open import Function using (mk↔′)
open import Algebra.Definitions
open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Data.Product.Algebra using (×-⊎-commutativeSemiring)

-- Local
import Algebra.Construct.Function as C
open import Inverses {ℓ}
open import Predicate {ℓ}

open S.IsMonoid isMonoid-M

open import Algebra.Structures {suc ℓ} {ℓ} {Pred M} _⟷_

open MonoidOps _∙_ ε

-- Pred as commutative semiring
∩-∪-commutativeSemiring : Set ℓ → CommutativeSemiring _ _
∩-∪-commutativeSemiring A = C.commutativeSemiring A (×-⊎-commutativeSemiring ℓ)

open import Predicate.Properties {ℓ}
open Pred-Semimodule

open MonoidSemiringProperties isMonoid-M

⋆-isMagma : IsMagma _⋆_
⋆-isMagma = record { isEquivalence = ⟷-isEquivalence ; ∙-cong = ⋆-cong }

⋆-isSemigroup : IsSemigroup _⋆_
⋆-isSemigroup = record { isMagma = ⋆-isMagma ; assoc = mapⱽ-assoc assoc }

⋆-isMonoid : IsMonoid _⋆_ 𝟏
⋆-isMonoid = record
  { isSemigroup = ⋆-isSemigroup
  ; identity = mapⱽ-identity identity
  }

⋆-∪-isSemiringWithoutAnnihilatingZero :
  IsSemiringWithoutAnnihilatingZero _∪_ _⋆_ ∅ 𝟏
⋆-∪-isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid {M}
  ; *-isMonoid = ⋆-isMonoid
  ; distrib = mapⱽ-distrib
  }

⋆-∪-isSemiring : IsSemiring _∪_ _⋆_ ∅ 𝟏
⋆-∪-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = ⋆-∪-isSemiringWithoutAnnihilatingZero
  ; zero = mapⱽ-zero
  }

⋆-∪-isCommutativeSemiring :
  Commutative _≡_ _∙_ → IsCommutativeSemiring _∪_ _⋆_ ∅ 𝟏 
⋆-∪-isCommutativeSemiring ∙-comm = record
  { isSemiring = ⋆-∪-isSemiring
  ; *-comm = mapⱽ-comm ∙-comm
  }

-- TODO: consider parametrizing each algebraic structure by the corresponding
-- algebraic structure on M.

open import Closed ; open Closed.Types {ℓ}

⋆-∪-isClosedSemiring : IsClosedSemiring _⟷_ _∪_ _⋆_ ∅ 𝟏  _✪
⋆-∪-isClosedSemiring = record { isSemiring = ⋆-∪-isSemiring
                              ; starˡ = λ _ → ✪-starˡ
                              -- ; starʳ = λ _ → ✪-starʳ
                              }

⋆-∪-isClosedCommutativeSemiring :
  Commutative _≡_ _∙_ → IsClosedCommutativeSemiring _⟷_ _∪_ _⋆_ ∅ 𝟏 _✪
⋆-∪-isClosedCommutativeSemiring ∙-comm = record
  { isCommutativeSemiring = ⋆-∪-isCommutativeSemiring ∙-comm
  ; starˡ = λ _ → ✪-starˡ
  -- ; starʳ = λ _ → ✪-starʳ
  }

⋆-∪-closedSemiring : ClosedSemiring _ _
⋆-∪-closedSemiring = record { isClosedSemiring =  ⋆-∪-isClosedSemiring }

⋆-∪-closedCommutativeSemiring : Commutative _≡_ _∙_ → ClosedCommutativeSemiring _ _
⋆-∪-closedCommutativeSemiring ∙-comm =
  record { isClosedCommutativeSemiring = ⋆-∪-isClosedCommutativeSemiring ∙-comm }

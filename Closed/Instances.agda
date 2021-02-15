-- Some examples of closed semirings

{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

module Closed.Instances where

open import Level
open import Algebra.Core
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Function.Properties.Inverse using (↔-isEquivalence)

open import Closed.Structures
open import Closed.Bundles

-- Booleans
module _ where

  open import Data.Bool
  open import Data.Bool.Properties

  infixl 10 _✦
  -- b ✦ ≡ true ∨ b ∧ b ✦
  _✦ : Op₁ Bool
  _ ✦ = true

  ∨-∧-isClosedCommutativeSemiring :
    IsClosedCommutativeSemiring _≡_ _∨_ _∧_ false true _✦
  ∨-∧-isClosedCommutativeSemiring = record
    {  isCommutativeSemiring = ∨-∧-isCommutativeSemiring
    ;  starˡ = λ _ → refl
    }

  ∨-∧-closedCommutativeSemiring : ClosedCommutativeSemiring zero zero
  ∨-∧-closedCommutativeSemiring =
    record { isClosedCommutativeSemiring = ∨-∧-isClosedCommutativeSemiring }

-- Types
module Types {ℓ : Level} where

  open import Function.Bundles
  open import Data.Product
  open import Data.Sum
  open import Data.Unit.Polymorphic
  open import Data.Empty.Polymorphic
  open import Data.Product.Algebra
  open import Data.List renaming (List to _✶)

  -- A ✶ ↔ ⊤ ⊎ A × A ✶
  ✶-starˡ : Starˡ {ℓ = ℓ} _↔_ _⊎_ _×_ ⊥ ⊤ _✶
  ✶-starˡ _ = mk↔′
    (λ {[] → inj₁ tt ; (x ∷ xs) → inj₂ (x , xs)})
    (λ {(inj₁ _) → [] ; (inj₂ (x , xs)) → x ∷ xs})
    (λ {(inj₁ _) → refl ; (inj₂ (x , xs)) → refl})
    (λ {[] → refl ; (x ∷ xs) → refl})

  ⊎-×-isClosedCommutativeSemiring :
    IsClosedCommutativeSemiring {ℓ = ℓ} _↔_ _⊎_ _×_ ⊥ ⊤ _✶
  ⊎-×-isClosedCommutativeSemiring = record
    {  isCommutativeSemiring = ⊎-×-isCommutativeSemiring ℓ
    ;  starˡ = ✶-starˡ
    }

  ×-⊎-closedCommutativeSemiring : ClosedCommutativeSemiring (suc ℓ) ℓ
  ×-⊎-closedCommutativeSemiring =
    record { isClosedCommutativeSemiring = ⊎-×-isClosedCommutativeSemiring }

  -- A ✶ is satisfiable for all A. If & when we extract more than one satisfying
  -- value, we can find more here.
  open import Relation.Nullary

  _✶-reflects : ∀ {A b} → Reflects {p = ℓ} A b → Reflects (A ✶) (b ✦)
  _ ✶-reflects = ofʸ []

  infixl 10 _✶-dec
  _✶-dec : {A : Set ℓ} → Dec A → Dec (A ✶)
  does  (a? ✶-dec) = does  a? ✦  -- i.e., true
  proof (a? ✶-dec) = proof a? ✶-reflects

-- TODO: relations using Relation.Binary.Construct.Closure.ReflexiveTransitive

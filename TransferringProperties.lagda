\begin{code}

open import Relation.Binary.PropositionalEquality using (_≡_) ; open _≡_
open import Decidability

module TransferringProperties {ℓ} {A : Set ℓ} (_≟_ : Decidable₂ {A = A} _≡_) where

open import Level
open import Algebra
open import Data.Product

open import Existential ; open Inj
open import Closed

module ◬ where
  open import Symbolic _≟_ public

\end{code}

\begin{code}
module Examples where

  open import Data.List.Properties

  open import Predicate.Algebra (++-isMonoid {A = A})

  open import Size

  open import Closed.Instances ; open Types {ℓ}

  decCCS : ClosedCommutativeSemiring (suc ℓ) ℓ
  symbolicCS  : ClosedSemiring (suc ℓ) ℓ
  automaticCS : ClosedSemiring (suc ℓ) ℓ
\end{code}
%<*examples>
\begin{code}
  decCCS = mkClosedCommutativeSemiring ×-⊎-closedCommutativeSemiring
                                         Dec _⊎‽_ _×‽_ ⊥‽ ⊤‽ _✶‽

  symbolicCS = mkClosedSemiring ⋆-∪-ClosedSemiring Lang _∪_ _⋆_ ∅ 𝟏 _☆
    where open import Symbolic _≟_

  automaticCS = mkClosedSemiring ⋆-∪-ClosedSemiring (Lang ∞) _∪_ _⋆_ ∅ 𝟏 _☆
    where open import SizedAutomatic _≟_
\end{code}
%</examples>

\begin{code}
module Wrap where
  Lang : Set (suc ℓ)

  infixr 6 _∪_
  infixr 6 _∩_
  infixl 7 _·_
  infixl 7 _⋆_
  infixl 10 _☆

  ∅ : Lang
  𝒰 : Lang
  _∪_ : Op₂ Lang
  _∩_ : Op₂ Lang
  𝟏 : Lang
  _⋆_ : Op₂ Lang
  _·_ : ∀ {s} → Dec s → Op₁ Lang
  ` : A → Lang
  _☆ : Op₁ Lang

  Lang = ∃ ◬.Lang

  ∅      = inj   ◬.∅
  𝒰      = inj   ◬.𝒰
  _∪_    = inj₂  ◬._∪_
  _∩_    = inj₂  ◬._∩_
  𝟏      = inj   ◬.𝟏
  _⋆_    = inj₂  ◬._⋆_
  _·_ s  = inj₁  (s ◬.·_)
  ` c    = inj   (◬.` c)
  _☆     = inj₁  ◬._☆
\end{code}

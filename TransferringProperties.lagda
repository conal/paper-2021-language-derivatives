\begin{code}

open import Relation.Binary.PropositionalEquality using (_≡_) ; open _≡_
open import Decidability hiding (_◂_)

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

\end{code}

\begin{code}
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

open import Data.List.Properties

open import Predicate.Algebra (++-isMonoid {A = A})

-- open import 

-- semiring : Semiring {!!} {!!}
-- semiring = mkSemiring ⋆-∪-Semiring ◬.Lang ◬._∪_ ◬._⋆_ ◬.∅ ◬.𝟏

closedSemiring : ClosedSemiring {!!} {!!}
closedSemiring = mkClosedSemiring ⋆-∪-ClosedSemiring ◬.Lang ◬._∪_ ◬._⋆_ ◬.∅ ◬.𝟏 {!!} -- ◬._☆

\end{code}

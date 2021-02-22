\begin{code}

open import Relation.Binary.PropositionalEquality using (_≡_) ; open _≡_
open import Decidability

module Transport {ℓ} {A : Set ℓ} (_≟_ : Decidable₂ {A = A} _≡_) where

open import Level
open import Algebra
open import Data.Product

open import Existential ; open Inj
open import Closed

module ◇ where
  open import Predicate public
  open ListOps A public

module ▣ where
  open import Symbolic _≟_ public

\end{code}

\begin{code}
module Examples where

  open import Data.List.Properties

  open import Predicate.Algebra (++-isMonoid {A = A})

  open import Size

  open import Closed.Instances ; open Types {ℓ}

  module Symbolic where
    open import Symbolic _≟_ public

  module Automatic where
    open import SizedAutomatic _≟_ public

  decCCS : ClosedCommutativeSemiring (suc ℓ) ℓ
  symbolicCS₁ : CommutativeSemiring (suc ℓ) ℓ
  symbolicCS₂ : ClosedSemiring (suc ℓ) ℓ
  automaticCS₁ : CommutativeSemiring (suc ℓ) ℓ
  automaticCS₂ : ClosedSemiring (suc ℓ) ℓ
\end{code}
%<*examples>
\mathindent0ex
\begin{code}
  decCCS = mkClosedCommutativeSemiring ×-⊎-closedCommutativeSemiring
                                         Dec _⊎‽_ _×‽_ ⊥‽ ⊤‽ _✶‽

  symbolicCS₁ = mkCommutativeSemiring (∩-∪-commutativeSemiring _) Lang _∪_ _∩_ ∅ 𝒰
    where open Symbolic

  symbolicCS₂ = mkClosedSemiring ⋆-∪-closedSemiring Lang _∪_ _⋆_ ∅ 𝟏 _☆
    where open Symbolic

  automaticCS₁ = mkCommutativeSemiring (∩-∪-commutativeSemiring _) (Lang ∞) _∪_ _∩_ ∅ 𝒰
    where open Automatic

  automaticCS₂ = mkClosedSemiring ⋆-∪-closedSemiring (Lang ∞) _∪_ _⋆_ ∅ 𝟏 _☆
    where open Automatic
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

  Lang = ∃ ▣.Lang

  ∅      = inj   ▣.∅
  𝒰      = inj   ▣.𝒰
  _∪_    = inj₂  ▣._∪_
  _∩_    = inj₂  ▣._∩_
  𝟏      = inj   ▣.𝟏
  _⋆_    = inj₂  ▣._⋆_
  _·_ s  = inj₁  (s ▣.·_)
  ` c    = inj   (▣.` c)
  _☆     = inj₁  ▣._☆
\end{code}

\begin{code}
module ManualWrap where
\end{code}
%<*wrapped-Lang>
\begin{code}
  Lang = ∃ ▣.Lang
\end{code}
%</wrapped-Lang>
%<*wrapped-union>
\begin{code}
  _∪_ : Lang → Lang → Lang
  (P , p) ∪ (Q , q) = (P ◇.∪ Q , p ▣.∪ q)
\end{code}
%  (_ , p) ∪ (_ , q) = (_ , p ▣.∪ q)

%</wrapped-union>

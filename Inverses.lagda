\begin{code}
{-# OPTIONS --safe #-}

module Inverses where

open import Level

private
  ℓ = 0ℓ

open import Data.Unit using () renaming (tt to tt₀)
open import Algebra.Core
open import Data.Product
open import Data.Product.Properties
open import Data.Product.Algebra
open import Data.Sum hiding (map₂)
open import Data.Sum.Algebra
open import Data.List
open import Data.List.Properties
open import Function using (id; _∘_; const; flip; _↔_; Inverse; mk↔′; mk↔)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality
open import Function.Equivalence using (_⇔_; equivalence)

open import Function.Properties.Inverse using (↔-isEquivalence)
module ↔Eq = IsEquivalence {ℓ = ℓ} ↔-isEquivalence
import Relation.Binary.Reasoning.Setoid as SetoidR
module ↔R = SetoidR {s₂ = ℓ} (record {isEquivalence = ↔-isEquivalence})

Pred : Set → Set₁
Pred A = A → Set

private
  variable
    A B : Set
\end{code}

-- Function-lifted _↔_
%<*ext-iso>
\AgdaTarget{\_⟷\_, ⟷}
\begin{code}[hide]
infix 3 _⟷_
_⟷_ : Rel (Pred A) ℓ
\end{code}
\begin{code}
P ⟷ Q = ∀ {w} → P w ↔ Q w
\end{code}
%</ext-iso>

\begin{code}

⟷-isEquivalence : IsEquivalence (_⟷_ {A = A})
⟷-isEquivalence = record
  { refl  = ↔Eq.refl
  ; sym   = λ f⟷g → ↔Eq.sym f⟷g
  ; trans = λ f⟷g g⟷k → ↔Eq.trans f⟷g g⟷k
  }

\end{code}

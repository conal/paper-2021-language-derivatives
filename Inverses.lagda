\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Level

module Inverses {ℓ : Level} where

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

private
  Pred : Set ℓ → Set _
  Pred A = A → Set ℓ

private
  variable
    A B C D : Set ℓ
    P Q R S : A → Set ℓ
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

module ⟷Eq {A : Set ℓ} = IsEquivalence (⟷-isEquivalence {A = A})
import Relation.Binary.Reasoning.Setoid as SetoidR
module ⟷R {A : Set ℓ} = SetoidR (record {isEquivalence = ⟷-isEquivalence {A = A}})
\end{code}

\section{Existential quantification}

\begin{code}
∃-cong : (∀ {w} → P w ↔ Q w) → (∃ P ↔ ∃ Q)
∃-cong P↔Q = mk↔′ (map₂ J.f) (map₂ J.f⁻¹)
  (λ (a , d) → Inverse.f Σ-≡,≡↔≡ (refl , J.inverseˡ d) )
  (λ (a , c) → Inverse.f Σ-≡,≡↔≡ (refl , J.inverseʳ c) )
 where
   module J {t} = Inverse (P↔Q {t} )
\end{code}


\subsection{Products and sums}

\begin{code}
×-congʳ : A ↔ B → (A × C) ↔ (B × C)
×-congʳ A↔B = ×-cong A↔B ↔Eq.refl

×-congˡ : C ↔ D → (A × C) ↔ (A × D)
×-congˡ C↔D = ×-cong ↔Eq.refl C↔D
\end{code}

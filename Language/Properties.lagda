\begin{code}
-- {-# OPTIONS --safe #-}

module Language.Properties {ℓ} (A : Set ℓ) where

open import Algebra.Module.Bundles

open import Level

open import Algebra.Construct.Function

open import Language A
open import Inverses {ℓ}
open import Closed ; open Closed.Types {ℓ}

open import Algebra.Definitions {A = Lang} _⟷_

private
  variable
    P Q R S : Lang

postulate

  ⋆-cong : P ⟷ R → Q ⟷ S → P ⋆ Q ⟷ R ⋆ S
  ⋆-assoc : Associative _⋆_
  ⋆-identity : Identity 𝟏 _⋆_
  ⋆-distrib : _⋆_ DistributesOver _∪_
  ⋆-zero : Zero ∅ _⋆_

open import Data.Product.Algebra

-- Predicates as semimodule
Pred-Semimodule : Set ℓ → Semimodule (×-⊎-commutativeSemiring ℓ) _ _
Pred-Semimodule A = semimodule A

module Pred-Semimodule {A} = Semimodule (Pred-Semimodule A)
open Pred-Semimodule

\end{code}

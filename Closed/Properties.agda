-- Star semirings properties

{-# OPTIONS --safe #-}
{-# OPTIONS --without-K #-}

open import Closed.Bundles

module Closed.Properties {c ℓ} (R : ClosedSemiring c ℓ) where

-- If I want to prove properties of closed *commutative* semirings, then move
-- the R parameter to a local module, and add another.

open import Function using (_↔_)

-- open import Isomorphisms using (module ↔R)
open import Closed.Structures

open ClosedSemiring R renaming (Carrier to A)

open import Relation.Binary.Reasoning.Setoid setoid

-- if `x ≈ a * x + b` then `x ≈ a ✯ * b`.

private
  variable
    x a b : A

_isFixpointOf_ : A → (A → A) → Set _
a isFixpointOf f = a ≈ f a

isFix : (a ✯ * b) isFixpointOf (λ x → b + a * x)
isFix {a}{b} =
  begin
    a ✯ * b
  ≈⟨ *-congʳ (star _) ⟩
    (1# + a * a ✯) * b
  ≈⟨ distribʳ _ _ _ ⟩
    1# * b + (a * a ✯) * b
  ≈⟨ +-cong (*-identityˡ _) (*-assoc _ _ _) ⟩
    b + a * (a ✯ * b)
  ∎

-- TODO: Is there a general form of Arden's rule for arbitrary closed semirings?
-- This rule says that `a ✯ * b` is the *least* fixpoint of `λ x → b + a * x`.

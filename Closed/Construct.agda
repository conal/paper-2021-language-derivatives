-- Closed semiring constructions
{-# OPTIONS --safe --without-K #-}

module Closed.Construct where

open import Level
open import Algebra

open import Closed.Structures
open import Closed.Bundles
open import Existential ; open Inj

private variable b c ℓ : Level

module _ (r : ClosedSemiring c ℓ) (f : ClosedSemiring.Carrier r → Set b) where
  open ClosedSemiring r hiding (isSemiring) ; open Dop f
  mkClosedSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1# → D₁ _✯
                   → ClosedSemiring (c ⊔ b) ℓ
  mkClosedSemiring _+′_ _*′_ 0#′ 1#′ _✯′ = record
    { _✯ =  inj₁ _✯′
    ; isClosedSemiring = record { isSemiring = isSemiring ; starˡ = prop₁ starˡ }
    } where open Semiring (mkSemiring semiring f _+′_ _*′_ 0#′ 1#′)

module _ (r : ClosedCommutativeSemiring c ℓ)
         (f : ClosedCommutativeSemiring.Carrier r → Set b) where
  open ClosedCommutativeSemiring r hiding (isCommutativeSemiring) ; open Dop f
  mkClosedCommutativeSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1# → D₁ _✯
                              → ClosedCommutativeSemiring (c ⊔ b) ℓ
  mkClosedCommutativeSemiring _+′_ _*′_ 0#′ 1#′ _✯′ = record
    { _✯ =  inj₁ _✯′
    ; isClosedCommutativeSemiring = record
        { isCommutativeSemiring = isCommutativeSemiring
        ; starˡ = prop₁ starˡ
        }
    } where open CommutativeSemiring
              (mkCommutativeSemiring commutativeSemiring f _+′_ _*′_ 0#′ 1#′)

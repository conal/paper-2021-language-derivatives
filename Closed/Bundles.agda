-- Star semirings bundles

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles

module Closed.Bundles where

open import Level
open import Relation.Binary using (Rel)
open import Algebra.Core

open import Closed.Structures

record ClosedSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 10 _✯
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier
    _✯         : Op₁ Carrier
    isClosedSemiring : IsClosedSemiring _≈_ _+_ _*_ 0# 1# _✯

  open IsClosedSemiring isClosedSemiring public

  semiring : Semiring _ _
  semiring = record { isSemiring = isSemiring }

record ClosedCommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 10 _✯
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ
    _+_        : Op₂ Carrier
    _*_        : Op₂ Carrier
    0#         : Carrier
    1#         : Carrier
    _✯         : Op₁ Carrier
    isClosedCommutativeSemiring : IsClosedCommutativeSemiring _≈_ _+_ _*_ 0# 1# _✯

  open IsClosedCommutativeSemiring isClosedCommutativeSemiring public

  commutativeSemiring : CommutativeSemiring _ _
  commutativeSemiring = record { isCommutativeSemiring = isCommutativeSemiring }

  closedSemiring : ClosedSemiring _ _
  closedSemiring = record { isClosedSemiring = isClosedSemiring }

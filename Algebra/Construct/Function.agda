-- Some algebraic properties of functions

{-# OPTIONS --without-K --safe #-}

-- Following the style of Algebra.Construct.DirectProduct, except that our
-- domain is a type rather than a setoid.

open import Level using (Level; _⊔_)

module Algebra.Construct.Function {a} (A : Set a) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra

open import Closed

private
  variable
    b ℓ : Level

magma : Magma b ℓ → Magma (a ⊔ b) (a ⊔ ℓ)
magma M = record
  { Carrier = A → Carrier
  ; _≈_     = λ f g → ∀ {x} → f x ≈ g x
  ; _∙_     = λ f g → λ x → f x ∙ g x
  ; isMagma = record
      { isEquivalence = record
          { refl = refl
          ; sym = λ f≡g → sym f≡g
          ; trans = λ f≡g g≡h → trans f≡g g≡h
          }
      ; ∙-cong = λ f≡h g≡i → ∙-cong f≡h g≡i
      }
  } where open Magma M

semigroup : Semigroup b ℓ → Semigroup (a ⊔ b) (a ⊔ ℓ)
semigroup G = record
  { isSemigroup = record
     { isMagma = Magma.isMagma (magma magma-G)
     ; assoc = λ f g h {x} → assoc (f x) (g x) (h x)
     -- ; assoc = λ _ _ _ → assoc _ _ _  -- also works throughout
     }
  } where open Semigroup G renaming (magma to magma-G)

band : Band b ℓ → Band (a ⊔ b) _
band B = record
  { isBand = record
    { isSemigroup = Semigroup.isSemigroup (semigroup semigroup-B)
    ; idem = λ f {x} → idem (f x)
    }
  } where open Band B renaming (semigroup to semigroup-B)

commutativeSemigroup : CommutativeSemigroup b ℓ →
                       CommutativeSemigroup (a ⊔ b) _
commutativeSemigroup G = record
  { isCommutativeSemigroup = record
    { isSemigroup = Semigroup.isSemigroup (semigroup semigroup-G)
    ; comm = λ f g {x} → comm (f x) (g x)
    }
  } where open CommutativeSemigroup G renaming (semigroup to semigroup-G)

semilattice : Semilattice b ℓ → Semilattice (a ⊔ b) _
semilattice L = record
  { isSemilattice = record
    { isBand = Band.isBand (band band-L)
    ; comm = λ f g {x} → comm (f x) (g x)
    }
  } where open Semilattice L renaming (band to band-L)

monoid : Monoid b ℓ → Monoid (a ⊔ b) _
monoid M = record
  { ε = λ _ → ε
  ; isMonoid = record
    { isSemigroup = Semigroup.isSemigroup (semigroup semigroup-M)
    ; identity = (λ f {x} → identityˡ (f x)) , (λ f {x} → identityʳ (f x))
    }
  } where open Monoid M renaming (semigroup to semigroup-M)

commutativeMonoid : CommutativeMonoid b ℓ → CommutativeMonoid (a ⊔ b) _
commutativeMonoid M = record
  { isCommutativeMonoid = record
    { isMonoid = Monoid.isMonoid (monoid monoid-M)
    ; comm = λ f g {x} → comm (f x) (g x)
    }
  } where open CommutativeMonoid M renaming (monoid to monoid-M)

-- TODO: IdempotentCommutativeMonoid, Group, AbelianGroup, Lattice,
-- DistributiveLattice, NearSemiring, SemiringWithoutOne,
-- CommutativeSemiringWithoutOne, SemiringWithoutOne,
-- SemiringWithoutAnnihilatingZero

semiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero b ℓ
                                → SemiringWithoutAnnihilatingZero (b ⊔ a) (a ⊔ ℓ)
semiringWithoutAnnihilatingZero R = record
  { isSemiringWithoutAnnihilatingZero = record
     { +-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
                                 (commutativeMonoid +-commutativeMonoid)
     ; *-isMonoid = Monoid.isMonoid (monoid (*-monoid))
     ; distrib = (λ f g h {x} → distribˡ (f x) (g x) (h x))
               , (λ f g h {x} → distribʳ (f x) (g x) (h x))
     }
  } where open SemiringWithoutAnnihilatingZero R

semiring : Semiring b ℓ → Semiring (a ⊔ b) _
semiring R = record
  { isSemiring = record
     { isSemiringWithoutAnnihilatingZero =
         SemiringWithoutAnnihilatingZero.isSemiringWithoutAnnihilatingZero
           (semiringWithoutAnnihilatingZero semiringWithoutAnnihilatingZero-R)
     ; zero = (λ f {x} → zeroˡ (f x)) , (λ f {x} → zeroʳ (f x)) }
     } where open Semiring R renaming
              (semiringWithoutAnnihilatingZero to semiringWithoutAnnihilatingZero-R)

commutativeSemiring : CommutativeSemiring b ℓ → CommutativeSemiring (a ⊔ b) _
commutativeSemiring M = record
  { isCommutativeSemiring = record
    { isSemiring = Semiring.isSemiring (semiring semiring-M)
    ; *-comm = λ f g {x} → *-comm (f x) (g x)
    }
  } where open CommutativeSemiring M renaming (semiring to semiring-M)

closedSemiring : ClosedSemiring b ℓ → ClosedSemiring (a ⊔ b) _
closedSemiring M = record
  { _✯ = λ f a → f a ✯
  ; isClosedSemiring = record
    { isSemiring = Semiring.isSemiring (semiring semiring-M)
    ; star = λ f {x} → star (f x)
    }
  } where open ClosedSemiring M renaming (semiring to semiring-M)

closedCommutativeSemiring : ClosedCommutativeSemiring b ℓ
                          → ClosedCommutativeSemiring (a ⊔ b) _
closedCommutativeSemiring M = record
  { isClosedCommutativeSemiring = record
    { isCommutativeSemiring = CommutativeSemiring.isCommutativeSemiring
                               (commutativeSemiring commutativeSemiring-M)
    ; star = λ f {x} → star (f x)
    }
  } where open ClosedCommutativeSemiring M renaming
                 (commutativeSemiring to commutativeSemiring-M)


----- Module flavors, e.g., a module from a ring.

-- We're going straight from semiring to semimodule here. Now I think a better
-- design is to lift a semimodule, which might come from a semiring via
-- Algebra.Module.Construct.TensorUnit.

open import Algebra.Module.Bundles

leftSemimodule : ∀ {r ℓr} {R : Semiring r ℓr} → LeftSemimodule R (a ⊔ r) (a ⊔ ℓr)
leftSemimodule {R = R} = record
  { isLeftSemimodule = record
     { +ᴹ-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
                                  (commutativeMonoid +-commutativeMonoid)
     ; isPreleftSemimodule = record
         { *ₗ-cong      = λ x~y f~g   → *-cong x~y f~g
         ; *ₗ-zeroˡ     = λ f {a}     → proj₁ zero (f a)
         ; *ₗ-distribʳ  = λ f s t {a} → distribʳ (f a) s t
         ; *ₗ-identityˡ = λ f {a}     → *-identityˡ (f a)
         ; *ₗ-assoc     = λ s t f {a} → *-assoc s t (f a)
         ; *ₗ-zeroʳ     = λ s         → zeroʳ s
         ; *ₗ-distribˡ  = λ s f g {a} → distribˡ s (f a) (g a)
         }
     }
  } where open Semiring R

rightSemimodule : ∀ {r ℓr} {R : Semiring r ℓr} → RightSemimodule R (a ⊔ r) (a ⊔ ℓr)
rightSemimodule {R = R} = record
  { isRightSemimodule = record
     { +ᴹ-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
                                  (commutativeMonoid +-commutativeMonoid)
     ; isPrerightSemimodule = record
         { *ᵣ-cong      = λ x~y f~g   → *-cong x~y f~g
         ; *ᵣ-zeroʳ     = λ f {a}     → proj₂ zero (f a)
         ; *ᵣ-distribˡ  = λ f s t {a} → distribˡ (f a) s t
         ; *ᵣ-identityʳ = λ f {a}     → *-identityʳ (f a)
         ; *ᵣ-assoc     = λ f s t {a} → *-assoc (f a) s t
         ; *ᵣ-zeroˡ     = λ s         → zeroˡ s
         ; *ᵣ-distribʳ  = λ f g s {a} → distribʳ f (g a) (s a)
         }
     }
  } where open Semiring R

leftModule : ∀ {r ℓr} {R : Ring r ℓr} → LeftModule R (a ⊔ r) (a ⊔ ℓr)
leftModule {R = R} = record
  { isLeftModule = record
      { isLeftSemimodule = LeftSemimodule.isLeftSemimodule leftSemimodule
      ; -ᴹ‿cong = λ f~g {a} → -‿cong (f~g {a})
      ; -ᴹ‿inverse = (λ f {a} → proj₁ -‿inverse (f a))
                    , (λ f {a} → proj₂ -‿inverse (f a))
      }
  } where open Ring R

semimodule : ∀ {r ℓr} {R : CommutativeSemiring r ℓr} → Semimodule R (a ⊔ r) (a ⊔ ℓr)
semimodule {R = R} = record
  { isSemimodule = record
     { isBisemimodule = record
         { +ᴹ-isCommutativeMonoid = CommutativeMonoid.isCommutativeMonoid
                 (commutativeMonoid +-commutativeMonoid)
         ; isPreleftSemimodule =
             LeftSemimodule.isPreleftSemimodule leftSemimodule
         ; isPrerightSemimodule =
             RightSemimodule.isPrerightSemimodule rightSemimodule
         ; *ₗ-*ᵣ-assoc = λ s f t {a} → *-assoc s (f a) t
         }
     }
  } where open CommutativeSemiring R


-- TODO: more module flavors

 

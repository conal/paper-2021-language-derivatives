\begin{code}

-- Algebraic bundles for existentially quantified types, with equivalence
-- defined as equivalence on proj₁. Status: coverage for all bundles in
-- Algebra.Bundles and none in Algebra.Module.Bundles.

{-# OPTIONS --safe --without-K #-}
open import Level

module Existential where

open import Algebra
open import Data.Product
open import Function using (_on_)
import Relation.Binary.Construct.On as On

private variable b c ℓ : Level

module Inj {A : Set c} {f : A → Set ℓ} where

  -- Mostly work with 2nd projections, ignoring and inferring 1st projections.
  pattern inj b = (_ , b)

  inj₁ : ∀ {∙_ : Op₁ A} (∙′_ : ∀ {x} → f x → f (∙ x)) → Op₁ (∃ f)
  inj₁ ∙′_ (inj x) = inj (∙′ x)

  inj₂ : ∀ {_∙_ : Op₂ A} (_∙′_ : ∀ {x y} → f x → f y → f (x ∙ y)) → Op₂ (∃ f)
  inj₂ _∙′_ (inj x) (inj y) = inj (x ∙′ y)

  prop₁ : ∀ {B : A → Set b} → (∀ x → B x) → (∀ (p : ∃ f) → B (proj₁ p))
  prop₁ P (x , _) = P x

  prop₂ : ∀ {B : A → A → Set b} → (∀ x y → B x y)
        → (∀ (p q : ∃ f) → B (proj₁ p) (proj₁ q))
  prop₂ P (x , _) (y , _) = P x y

  prop₃ : ∀ {B : A → A → A → Set b} → (∀ x y z → B x y z)
        → (∀ (p q r : ∃ f) → B (proj₁ p) (proj₁ q) (proj₁ r))
  prop₃ P (x , _) (y , _) (z , _) = P x y z
  -- prop₃ P _ _ _ = P _ _ _

open Inj

module _ (m : Magma c ℓ) where
  open Magma m
  mkMagma : (f : Carrier → Set b)
          → (∀ {x y} → f x → f y → f (x ∙ y))
          → Magma (c ⊔ b) ℓ
  mkMagma f _∙′_ = record
    { Carrier = ∃ f
    ; _≈_ = _≈_ on proj₁
    ; _∙_ = inj₂ _∙′_
    ; isMagma = record
       { isEquivalence = On.isEquivalence proj₁ isEquivalence
       ; ∙-cong = ∙-cong
       }
    }

module _ (g : Semigroup c ℓ) where
  open Semigroup g hiding (isMagma)
  mkSemigroup : (f : Carrier → Set b)
              → (∀ {x y} → f x → f y → f (x ∙ y))
              → Semigroup (c ⊔ b) ℓ
  mkSemigroup f _∙′_ = record
    { isSemigroup = record
       { isMagma = isMagma
       ; assoc = prop₃ assoc
       }
    } where open Magma (mkMagma magma f _∙′_)

module _ (g : Monoid c ℓ) where
  open Monoid g hiding (isSemigroup)
  mkMonoid : (f : Carrier → Set b)
           → (∀ {x y} → f x → f y → f (x ∙ y))
           → f ε
           → Monoid (c ⊔ b) ℓ
  mkMonoid f _∙′_ ε′ = record
      { ε = inj ε′
      ; isMonoid = record { isSemigroup = isSemigroup
                          ; identity = (λ (x , _) → identityˡ x)
                                     , (λ (x , _) → identityʳ x) }
      } where open Semigroup (mkSemigroup semigroup f _∙′_)

module _ (g : CommutativeMonoid c ℓ) where
  open CommutativeMonoid g hiding (isMonoid)
  mkCommutativeMonoid : (f : Carrier → Set b)
                      → (∀ {x y} → f x → f y → f (x ∙ y)) → f ε
                      → CommutativeMonoid (c ⊔ b) ℓ
  mkCommutativeMonoid f _∙′_ ε′ = record
    { isCommutativeMonoid = record { isMonoid = isMonoid ; comm = prop₂ comm }
    } where open Monoid (mkMonoid monoid f _∙′_ ε′)

module _ (g : Group c ℓ) where
  open Group g hiding (isMonoid)
  mkGroup : (f : Carrier → Set b)
          → (∀ {x y} → f x → f y → f (x ∙ y))
          → f ε
          → (∀ {x} → f x → f (x ⁻¹))
          → Group (c ⊔ b) ℓ
  mkGroup f _∙′_ ε′ _⁻¹′ = record
     { _⁻¹ = inj₁ _⁻¹′
     ; isGroup = record { isMonoid = isMonoid
                        ; inverse = prop₁ inverseˡ , prop₁ inverseʳ
                        ; ⁻¹-cong = ⁻¹-cong }
     } where open Monoid (mkMonoid monoid f _∙′_ ε′)

module _ (g : AbelianGroup c ℓ) where
  open AbelianGroup g hiding (isGroup)
  mkAbelianGroup : (f : Carrier → Set b)
                 → (∀ {x y} → f x → f y → f (x ∙ y))
                 → f ε
                 → (∀ {x} → f x → f (x ⁻¹))
                 → AbelianGroup (c ⊔ b) ℓ
  mkAbelianGroup f _∙′_ ε′ _⁻¹′ = record
    { isAbelianGroup = record { isGroup = isGroup ; comm = prop₂ comm }
    } where open Group (mkGroup group f _∙′_ ε′ _⁻¹′)

module _ (l : Lattice c ℓ) where
  open Lattice l hiding ()
  mkLattice : (f : Carrier → Set b)
            → (∀ {x y} → f x → f y → f (x ∨ y))
            → (∀ {x y} → f x → f y → f (x ∧ y))
            → Lattice (c ⊔ b) ℓ
  mkLattice f _∨′_ _∧′_ = record
    { Carrier = ∃ f
    ; _≈_ = _≈_ on proj₁
    ; _∨_ = inj₂ _∨′_
    ; _∧_ = inj₂ _∧′_
    ; isLattice = record
        { isEquivalence = On.isEquivalence proj₁ isEquivalence
        ; ∨-comm = prop₂ ∨-comm
        ; ∨-assoc = prop₃ ∨-assoc
        ; ∨-cong = ∨-cong
        ; ∧-comm = prop₂ ∧-comm
        ; ∧-assoc = prop₃ ∧-assoc
        ; ∧-cong = ∧-cong
        ; absorptive = prop₂ (proj₁ absorptive) , prop₂ (proj₂ absorptive)
        }
    }

module _ (g : DistributiveLattice c ℓ) where
  open DistributiveLattice g hiding (isLattice)
  mkDistributiveLattice : (f : Carrier → Set b)
                        → (∀ {x y} → f x → f y → f (x ∨ y))
                        → (∀ {x y} → f x → f y → f (x ∧ y))
                        → DistributiveLattice (c ⊔ b) ℓ
  mkDistributiveLattice f _∨′_ _∧′_ = record
    { isDistributiveLattice = record
        { isLattice = isLattice
        ; ∨-distribʳ-∧ = prop₃ ∨-distribʳ-∧
        }
    } where open Lattice (mkLattice lattice f _∨′_ _∧′_)

module _ (r : NearSemiring c ℓ) where
  open NearSemiring r hiding (+-isMonoid; *-isSemigroup)
  mkNearSemiring : (f : Carrier → Set b)
                 → (∀ {x y} → f x → f y → f (x + y))
                 → (∀ {x y} → f x → f y → f (x * y))
                 → f 0#
                 → NearSemiring (c ⊔ b) ℓ
  mkNearSemiring f _+′_ _*′_ 0#′ = record
    { isNearSemiring = record
        { +-isMonoid = +-isMonoid
        ; *-isSemigroup = *-isSemigroup
        ; distribʳ = prop₃ distribʳ
        ; zeroˡ = prop₁ zeroˡ
        }
    } where open Monoid (mkMonoid +-monoid f _+′_ 0#′)
               renaming (isMonoid to +-isMonoid)
            open Semigroup (mkSemigroup *-semigroup f _*′_)
               renaming (isSemigroup to *-isSemigroup)

module _ (r : SemiringWithoutOne c ℓ) where
  open SemiringWithoutOne r hiding (+-isCommutativeMonoid; *-isSemigroup)
  mkSemiringWithoutOne : (f : Carrier → Set b)
                       → (∀ {x y} → f x → f y → f (x + y))
                       → (∀ {x y} → f x → f y → f (x * y))
                       → f 0#
                       → SemiringWithoutOne (c ⊔ b) ℓ
  mkSemiringWithoutOne f _+′_ _*′_ 0#′ = record
    { isSemiringWithoutOne = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isSemigroup = *-isSemigroup
        ; distrib = prop₃ (proj₁ distrib) , prop₃ (proj₂ distrib)
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open CommutativeMonoid
                   (mkCommutativeMonoid +-commutativeMonoid f _+′_ 0#′)
               renaming (isCommutativeMonoid to +-isCommutativeMonoid)
            open Semigroup (mkSemigroup *-semigroup f _*′_)
               renaming (isSemigroup to *-isSemigroup)

module _ (r : CommutativeSemiringWithoutOne c ℓ) where
  open CommutativeSemiringWithoutOne r hiding (isSemiringWithoutOne)
  mkCommutativeSemiringWithoutOne
    : (f : Carrier → Set b)
    → (∀ {x y} → f x → f y → f (x + y))
    → (∀ {x y} → f x → f y → f (x * y))
    → f 0#
    → CommutativeSemiringWithoutOne (c ⊔ b) ℓ
  mkCommutativeSemiringWithoutOne f _+′_ _*′_ 0#′ = record
    { isCommutativeSemiringWithoutOne = record
        { isSemiringWithoutOne = isSemiringWithoutOne
        ; *-comm = prop₂ *-comm
        }
    } where open SemiringWithoutOne
                   (mkSemiringWithoutOne semiringWithoutOne f _+′_ _*′_ 0#′)

module _ (r : SemiringWithoutAnnihilatingZero c ℓ) where
  open SemiringWithoutAnnihilatingZero r hiding
         (+-isCommutativeMonoid; *-isMonoid)
  mkSemiringWithoutAnnihilatingZero
    : (f : Carrier → Set b)
    → (∀ {x y} → f x → f y → f (x + y))
    → (∀ {x y} → f x → f y → f (x * y))
    → f 0#
    → f 1#
    → SemiringWithoutAnnihilatingZero (c ⊔ b) ℓ
  mkSemiringWithoutAnnihilatingZero f _+′_ _*′_ 0#′ 1#′ = record
    { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isMonoid = *-isMonoid
        ; distrib = prop₃ (proj₁ distrib) , prop₃ (proj₂ distrib)
        }
    } where open CommutativeMonoid
                   (mkCommutativeMonoid +-commutativeMonoid f _+′_ 0#′)
               renaming (isCommutativeMonoid to +-isCommutativeMonoid)
            open Monoid (mkMonoid *-monoid f _*′_ 1#′)
               renaming (isMonoid to *-isMonoid)

module _ (r : Semiring c ℓ) where
  open Semiring r hiding (isSemiringWithoutAnnihilatingZero)
  mkSemiring : (f : Carrier → Set b)
             → (∀ {x y} → f x → f y → f (x + y))
             → (∀ {x y} → f x → f y → f (x * y))
             → f 0#
             → f 1#
             → Semiring (c ⊔ b) ℓ
  mkSemiring f _+′_ _*′_ 0#′ 1#′ = record
    { isSemiring = record
        { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open SemiringWithoutAnnihilatingZero
                    (mkSemiringWithoutAnnihilatingZero
                       semiringWithoutAnnihilatingZero f _+′_ _*′_ 0#′ 1#′)

module _ (r : CommutativeSemiring c ℓ) where
  open CommutativeSemiring r hiding (isSemiring)
  mkCommutativeSemiring : (f : Carrier → Set b)
                        → (∀ {x y} → f x → f y → f (x + y))
                        → (∀ {x y} → f x → f y → f (x * y))
                        → f 0#
                        → f 1#
                        → CommutativeSemiring (c ⊔ b) ℓ
  mkCommutativeSemiring f _+′_ _*′_ 0#′ 1#′ = record
    { isCommutativeSemiring =
        record { isSemiring = isSemiring
               ; *-comm = prop₂ *-comm
               }
    } where open Semiring (mkSemiring semiring f _+′_ _*′_ 0#′ 1#′)

module _ (r : CancellativeCommutativeSemiring c ℓ) where
  open CancellativeCommutativeSemiring r hiding (isCommutativeSemiring)
  mkCancellativeCommutativeSemiring
    : (f : Carrier → Set b)
    → (∀ {x y} → f x → f y → f (x + y))
    → (∀ {x y} → f x → f y → f (x * y))
    → f 0#
    → f 1#
    → CancellativeCommutativeSemiring (c ⊔ b) ℓ
  mkCancellativeCommutativeSemiring f _+′_ _*′_ 0#′ 1#′ = record
    { isCancellativeCommutativeSemiring = record
        { isCommutativeSemiring = isCommutativeSemiring
        ; *-cancelˡ-nonZero = λ (y , _) (z , _) q r → *-cancelˡ-nonZero y z q r
        }
    } where open CommutativeSemiring
                   (mkCommutativeSemiring commutativeSemiring f _+′_ _*′_ 0#′ 1#′)

module _ (r : Ring c ℓ) where
  open Ring r hiding (+-isAbelianGroup; *-isMonoid)
  mkRing : (f : Carrier → Set b)
         → (∀ {x y} → f x → f y → f (x + y))
         → (∀ {x y} → f x → f y → f (x * y))
         → (∀ {x} → f x → f (- x))
         → f 0#
         → f 1#
         → Ring (c ⊔ b) ℓ
  mkRing f _+′_ _*′_ -′_ 0#′ 1#′ = record
    { isRing = record
        { +-isAbelianGroup = +-isAbelianGroup
        ; *-isMonoid = *-isMonoid
        ; distrib = prop₃ (proj₁ distrib) , prop₃ (proj₂ distrib)
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open AbelianGroup (mkAbelianGroup +-abelianGroup f _+′_ 0#′ -′_)
               renaming (isAbelianGroup to +-isAbelianGroup)
            open Monoid (mkMonoid *-monoid f _*′_ 1#′)
               renaming (isMonoid to *-isMonoid)

module _ (r : CommutativeRing c ℓ) where
  open CommutativeRing r hiding (isRing)
  mkCommutativeRing : (f : Carrier → Set b)
                    → (∀ {x y} → f x → f y → f (x + y))
                    → (∀ {x y} → f x → f y → f (x * y))
                    → (∀ {x} → f x → f (- x))
                    → f 0#
                    → f 1#
                    → CommutativeRing (c ⊔ b) ℓ
  mkCommutativeRing f _+′_ _*′_ _-′ 0#′ 1#′ = record
    { isCommutativeRing = record { isRing = isRing  ; *-comm = prop₂ *-comm }
    } where open Ring (mkRing ring f _+′_ _*′_ _-′ 0#′ 1#′)

\end{code}

\begin{code}
open import Closed

module _ (r : ClosedSemiring c ℓ) where
  open ClosedSemiring r hiding (isSemiring)
  mkClosedSemiring : (f : Carrier → Set b)
             → (∀ {x y} → f x → f y → f (x + y))
             → (∀ {x y} → f x → f y → f (x * y))
             → f 0#
             → f 1#
             → (∀ {x} → f x → f (x ✯))
             → ClosedSemiring (c ⊔ b) ℓ
  mkClosedSemiring f _+′_ _*′_ 0#′ 1#′ _✯′ = record
    { _✯ =  λ { (inj x) → inj (x ✯′) }
    ; isClosedSemiring = record { isSemiring = isSemiring ; starˡ = prop₁ starˡ }
    } where open Semiring (mkSemiring semiring f _+′_ _*′_ 0#′ 1#′)

module _ (r : ClosedCommutativeSemiring c ℓ) where
  open ClosedCommutativeSemiring r hiding (isCommutativeSemiring)
  mkClosedCommutativeSemiring : (f : Carrier → Set b)
             → (∀ {x y} → f x → f y → f (x + y))
             → (∀ {x y} → f x → f y → f (x * y))
             → f 0#
             → f 1#
             → (∀ {x} → f x → f (x ✯))
             → ClosedCommutativeSemiring (c ⊔ b) ℓ
  mkClosedCommutativeSemiring f _+′_ _*′_ 0#′ 1#′ _✯′ = record
    { _✯ =  λ { (inj x) → inj (x ✯′) }
    ; isClosedCommutativeSemiring = record
        { isCommutativeSemiring = isCommutativeSemiring
        ; starˡ = prop₁ starˡ
        }
    } where open CommutativeSemiring
              (mkCommutativeSemiring commutativeSemiring f _+′_ _*′_ 0#′ 1#′)

\end{code}

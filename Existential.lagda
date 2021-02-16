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

-- Lift operations to dependent products
\end{code}
%<*Dop>
\begin{AgdaAlign}
\begin{code}[hide]
module Dop {A : Set c} (f : A → Set ℓ) where
  D₀ : A → Set ℓ
  D₁ : Op₁ A → Set (c ⊔ ℓ)
  D₂ : Op₂ A → Set (c ⊔ ℓ)
\end{code}
\begin{code}
  D₀ ∙  = f ∙
  D₁ ∙_ = ∀ {x} → f x → f (∙ x)
  D₂ _∙_  = ∀ {x y} → f x → f y → f (x ∙ y)
\end{code}
\end{AgdaAlign}
%</Dop>

\begin{code}
module Inj {A : Set c} {f : A → Set ℓ} where

  open Dop f
  
  -- Mostly work with 2nd projections, ignoring and inferring 1st projections.
  pattern inj b = (_ , b)

  inj₁ : ∀ {∙_ : Op₁ A} (∙′_ : D₁ ∙_) → Op₁ (∃ f)
  inj₁ ∙′_ (inj x) = inj (∙′ x)

  inj₂ : ∀ {_∙_ : Op₂ A} (_∙′_ : D₂ _∙_) → Op₂ (∃ f)
  inj₂ _∙′_ (inj x) (inj y) = inj (x ∙′ y)

  prop₁ : ∀ {B : A → Set b} → (∀ x → B x) → (∀ (p : ∃ f) → B (proj₁ p))
  prop₁ P (x , _) = P x

  prop₂ : ∀ {B : A → A → Set b} → (∀ x y → B x y)
        → (∀ (p q : ∃ f) → B (proj₁ p) (proj₁ q))
  prop₂ P (x , _) (y , _) = P x y

  prop₃ : ∀ {B : A → A → A → Set b} → (∀ x y z → B x y z)
        → (∀ (p q r : ∃ f) → B (proj₁ p) (proj₁ q) (proj₁ r))
  prop₃ P (x , _) (y , _) (z , _) = P x y z

  -- -- The propᵢ definitions can be mostly inferred, e.g.,
  -- prop₃ P _ _ _ = P _ _ _

open Inj

module _ (m : Magma c ℓ) (f : Magma.Carrier m → Set b) where
  open Magma m ; open Dop f
  mkMagma : D₂ _∙_ → Magma (c ⊔ b) ℓ
  mkMagma _∙′_ = record
    { Carrier = ∃ f
    ; _≈_ = _≈_ on proj₁
    ; _∙_ = inj₂ _∙′_
    ; isMagma = record
       { isEquivalence = On.isEquivalence proj₁ isEquivalence
       ; ∙-cong = ∙-cong
       }
    }

module _ (g : Semigroup c ℓ) (f : Semigroup.Carrier g → Set b) where
  open Semigroup g hiding (isMagma) ; open Dop f
  mkSemigroup : D₂ _∙_ → Semigroup (c ⊔ b) ℓ
  mkSemigroup _∙′_ = record
    { isSemigroup = record
       { isMagma = isMagma
       ; assoc = prop₃ assoc
       }
    } where open Magma (mkMagma magma f _∙′_)

module _ (g : Monoid c ℓ) (f : Monoid.Carrier g → Set b) where
  open Monoid g hiding (isSemigroup) ; open Dop f
  mkMonoid : D₂ _∙_ → D₀ ε → Monoid (c ⊔ b) ℓ
  mkMonoid _∙′_ ε′ = record
      { ε = inj ε′
      ; isMonoid = record { isSemigroup = isSemigroup
                          ; identity = prop₁ identityˡ , prop₁ identityʳ }
      } where open Semigroup (mkSemigroup semigroup f _∙′_)

module _ (g : CommutativeMonoid c ℓ) (f : CommutativeMonoid.Carrier g → Set b) where
  open CommutativeMonoid g hiding (isMonoid) ; open Dop f
  mkCommutativeMonoid : D₂ _∙_ → D₀ ε → CommutativeMonoid (c ⊔ b) ℓ
  mkCommutativeMonoid _∙′_ ε′ = record
    { isCommutativeMonoid = record { isMonoid = isMonoid ; comm = prop₂ comm }
    } where open Monoid (mkMonoid monoid f _∙′_ ε′)

module _ (g : Group c ℓ) (f : Group.Carrier g → Set b) where
  open Group g hiding (isMonoid) ; open Dop f
  mkGroup : D₂ _∙_ → D₀ ε → D₁ _⁻¹ → Group (c ⊔ b) ℓ
  mkGroup _∙′_ ε′ _⁻¹′ = record
     { _⁻¹ = inj₁ _⁻¹′
     ; isGroup = record { isMonoid = isMonoid
                        ; inverse = prop₁ inverseˡ , prop₁ inverseʳ
                        ; ⁻¹-cong = ⁻¹-cong }
     } where open Monoid (mkMonoid monoid f _∙′_ ε′)

module _ (g : AbelianGroup c ℓ) (f : AbelianGroup.Carrier g → Set b) where
  open AbelianGroup g hiding (isGroup) ; open Dop f
  mkAbelianGroup : D₂ _∙_ → D₀ ε → D₁ _⁻¹ → AbelianGroup (c ⊔ b) ℓ
  mkAbelianGroup _∙′_ ε′ _⁻¹′ = record
    { isAbelianGroup = record { isGroup = isGroup ; comm = prop₂ comm }
    } where open Group (mkGroup group f _∙′_ ε′ _⁻¹′)

module _ (l : Lattice c ℓ) (f : Lattice.Carrier l → Set b) where
  open Lattice l hiding () ; open Dop f
  mkLattice : D₂ _∨_ → D₂ _∧_ → Lattice (c ⊔ b) ℓ
  mkLattice _∨′_ _∧′_ = record
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

module _ (g : DistributiveLattice c ℓ) (f : DistributiveLattice.Carrier g → Set b) where
  open DistributiveLattice g hiding (isLattice) ; open Dop f
  mkDistributiveLattice : D₂ _∨_ → D₂ _∧_ → DistributiveLattice (c ⊔ b) ℓ
  mkDistributiveLattice _∨′_ _∧′_ = record
    { isDistributiveLattice = record
        { isLattice = isLattice
        ; ∨-distribʳ-∧ = prop₃ ∨-distribʳ-∧
        }
    } where open Lattice (mkLattice lattice f _∨′_ _∧′_)

module _ (r : NearSemiring c ℓ) (f : NearSemiring.Carrier r → Set b) where
  open NearSemiring r hiding (+-isMonoid; *-isSemigroup) ; open Dop f
  mkNearSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → NearSemiring (c ⊔ b) ℓ
  mkNearSemiring _+′_ _*′_ 0#′ = record
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

module _ (r : SemiringWithoutOne c ℓ) (f : SemiringWithoutOne.Carrier r → Set b) where
  open SemiringWithoutOne r hiding (+-isCommutativeMonoid; *-isSemigroup) ; open Dop f
  mkSemiringWithoutOne : D₂ _+_ → D₂ _*_ → D₀ 0# → SemiringWithoutOne (c ⊔ b) ℓ
  mkSemiringWithoutOne _+′_ _*′_ 0#′ = record
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

module _ (r : CommutativeSemiringWithoutOne c ℓ)
         (f : CommutativeSemiringWithoutOne.Carrier r → Set b) where
  open CommutativeSemiringWithoutOne r hiding (isSemiringWithoutOne)
  open Dop f
  mkCommutativeSemiringWithoutOne : D₂ _+_ → D₂ _*_ → D₀ 0#
                                  → CommutativeSemiringWithoutOne (c ⊔ b) ℓ
  mkCommutativeSemiringWithoutOne _+′_ _*′_ 0#′ = record
    { isCommutativeSemiringWithoutOne = record
        { isSemiringWithoutOne = isSemiringWithoutOne
        ; *-comm = prop₂ *-comm
        }
    } where open SemiringWithoutOne
                   (mkSemiringWithoutOne semiringWithoutOne f _+′_ _*′_ 0#′)

module _ (r : SemiringWithoutAnnihilatingZero c ℓ) 
         (f : SemiringWithoutAnnihilatingZero.Carrier r → Set b) where
  open SemiringWithoutAnnihilatingZero r hiding (+-isCommutativeMonoid; *-isMonoid)
  open Dop f
  mkSemiringWithoutAnnihilatingZero : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1#
                                    → SemiringWithoutAnnihilatingZero (c ⊔ b) ℓ
  mkSemiringWithoutAnnihilatingZero _+′_ _*′_ 0#′ 1#′ = record
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
\end{code}

%<*Semiring>
\begin{code}
module _ (r : Semiring c ℓ) (f : Semiring.Carrier r → Set b) where
  open Semiring r hiding (isSemiringWithoutAnnihilatingZero) ; open Dop f
  mkSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1# → Semiring (c ⊔ b) ℓ
  mkSemiring _+′_ _*′_ 0#′ 1#′ = record
    { isSemiring = record
        { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open SemiringWithoutAnnihilatingZero
                    (mkSemiringWithoutAnnihilatingZero
                       semiringWithoutAnnihilatingZero f _+′_ _*′_ 0#′ 1#′)
\end{code}
%</Semiring>

\begin{code}
module _ (r : CommutativeSemiring c ℓ) (f : CommutativeSemiring.Carrier r → Set b) where
  open CommutativeSemiring r hiding (isSemiring) ; open Dop f
  mkCommutativeSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1#
                        → CommutativeSemiring (c ⊔ b) ℓ
  mkCommutativeSemiring _+′_ _*′_ 0#′ 1#′ = record
    { isCommutativeSemiring =
        record { isSemiring = isSemiring
               ; *-comm = prop₂ *-comm
               }
    } where open Semiring (mkSemiring semiring f _+′_ _*′_ 0#′ 1#′)

module _ (r : CancellativeCommutativeSemiring c ℓ) 
         (f : CancellativeCommutativeSemiring.Carrier r → Set b) where
  open CancellativeCommutativeSemiring r hiding (isCommutativeSemiring)
  open Dop f
  mkCancellativeCommutativeSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1#
                                    → CancellativeCommutativeSemiring (c ⊔ b) ℓ
  mkCancellativeCommutativeSemiring _+′_ _*′_ 0#′ 1#′ = record
    { isCancellativeCommutativeSemiring = record
        { isCommutativeSemiring = isCommutativeSemiring
        ; *-cancelˡ-nonZero = λ (y , _) (z , _) q r → *-cancelˡ-nonZero y z q r
        }
    } where open CommutativeSemiring
                   (mkCommutativeSemiring commutativeSemiring f _+′_ _*′_ 0#′ 1#′)

module _ (r : Ring c ℓ) (f : Ring.Carrier r → Set b) where
  open Ring r hiding (+-isAbelianGroup; *-isMonoid) ; open Dop f
  mkRing : D₂ _+_ → D₂ _*_ → D₁ (-_) → D₀ 0# → D₀ 1# → Ring (c ⊔ b) ℓ
  mkRing _+′_ _*′_ -′_ 0#′ 1#′ = record
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

module _ (r : CommutativeRing c ℓ) (f : CommutativeRing.Carrier r → Set b) where
  open CommutativeRing r hiding (isRing) ; open Dop f
  mkCommutativeRing : D₂ _+_ → D₂ _*_ → D₁ (-_) → D₀ 0# → D₀ 1#
                    → CommutativeRing (c ⊔ b) ℓ
  mkCommutativeRing _+′_ _*′_ _-′ 0#′ 1#′ = record
    { isCommutativeRing = record { isRing = isRing  ; *-comm = prop₂ *-comm }
    } where open Ring (mkRing ring f _+′_ _*′_ _-′ 0#′ 1#′)

\end{code}

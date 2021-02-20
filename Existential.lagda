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
module Dop {A : Set c} (F : A → Set ℓ) where
  D₀ : A → Set ℓ
  D₁ : Op₁ A → Set (c ⊔ ℓ)
  D₂ : Op₂ A → Set (c ⊔ ℓ)
\end{code}
\begin{code}
  D₀ s  = F s
  D₁ g = ∀ {a} → F a → F (g a)
  D₂ h  = ∀ {a b} → F a → F b → F (h a b)
\end{code}
\end{AgdaAlign}
%</Dop>

An equivalent, less factored version for the paper:
%<*inj>
\begin{code}[hide]
module InjPaper {A : Set c} {F : A → Set ℓ} where
  open Dop F
\end{code}
\begin{code}
  inj₀ : ∀ {s : A} (s′ : F s) → ∃ F
  inj₀ {s} s′ = s , s′

  inj₁ : ∀ {g : A → A} (g′ : ∀ {a} → F a → F (g a)) → (∃ F → ∃ F)
  inj₁ {g} g′ (a , x) = g a , g′ x

  inj₂ : ∀ {h : A → A → A} (h′ : ∀ {a b} → F a → F b → F (h a b)) → (∃ F → ∃ F → ∃ F)
  inj₂ {h} h′ (a , x) (b , y) = h a b , h′ x y
\end{code}
%</inj>

\begin{code}
module Inj {A : Set c} {F : A → Set ℓ} where

  open Dop F
  
  -- Mostly work with 2nd projections, ignoring and inferring 1st projections.
  pattern inj b = (_ , b)

  inj₁ : ∀ {∙_ : Op₁ A} (∙′_ : D₁ ∙_) → Op₁ (∃ F)
  inj₁ ∙′_ (inj x) = inj (∙′ x)

  inj₂ : ∀ {_∙_ : Op₂ A} (_∙′_ : D₂ _∙_) → Op₂ (∃ F)
  inj₂ _∙′_ (inj x) (inj y) = inj (x ∙′ y)
\end{code}

%<*prop>
\begin{code}[hide]
  private
    variable
      h : Level
      P : A → Set h
      Q : A → A → Set h
      R : A → A → A → Set h
\end{code}
\begin{code}
  prop₁ : (∀ a → P a) → ∀ ((a , _) : ∃ F) → P a
  prop₁ P (a , _) = P a

  prop₂ : (∀ a b → Q a b) → ∀ ((a , _) (b , _) : ∃ F) → Q a b
  prop₂ Q (a , _) (b , _) = Q a b

  prop₃ : (∀ a b c → R a b c) → ∀ ((a , _) (b , _) (c , _) : ∃ F) → R a b c
  prop₃ R (a , _) (b , _) (c , _) = R a b c
\end{code}
%</prop>

%<*prop₃′>
\begin{code}[hide]
  prop₃′ : (∀ a b c → R a b c) → ∀ ((a , _) (b , _) (c , _) : ∃ F) → R a b c
\end{code}
\begin{code}[inline]
  prop₃′ R _ _ _ = R _ _ _
\end{code}
%</prop₃′>

\begin{code}
  -- -- The propᵢ definitions can be mostly inferred, e.g.,
  -- prop₃ P _ _ _ = P _ _ _

open Inj

module _ (m : Magma c ℓ) (F : Magma.Carrier m → Set b) where
  open Magma m ; open Dop F
  mkMagma : D₂ _∙_ → Magma (c ⊔ b) ℓ
  mkMagma _∙′_ = record
    { Carrier = ∃ F
    ; _≈_ = _≈_ on proj₁
    ; _∙_ = inj₂ _∙′_
    ; isMagma = record
       { isEquivalence = On.isEquivalence proj₁ isEquivalence
       ; ∙-cong = ∙-cong
       }
    }

module _ (g : Semigroup c ℓ) (F : Semigroup.Carrier g → Set b) where
  open Semigroup g hiding (isMagma) ; open Dop F
  mkSemigroup : D₂ _∙_ → Semigroup (c ⊔ b) ℓ
  mkSemigroup _∙′_ = record
    { isSemigroup = record
       { isMagma = isMagma
       ; assoc = prop₃ assoc
       }
    } where open Magma (mkMagma magma F _∙′_)

module _ (g : Monoid c ℓ) (F : Monoid.Carrier g → Set b) where
  open Monoid g hiding (isSemigroup) ; open Dop F
  mkMonoid : D₂ _∙_ → D₀ ε → Monoid (c ⊔ b) ℓ
  mkMonoid _∙′_ ε′ = record
      { ε = inj ε′
      ; isMonoid = record { isSemigroup = isSemigroup
                          ; identity = prop₁ identityˡ , prop₁ identityʳ }
      } where open Semigroup (mkSemigroup semigroup F _∙′_)

module _ (g : CommutativeMonoid c ℓ) (F : CommutativeMonoid.Carrier g → Set b) where
  open CommutativeMonoid g hiding (isMonoid) ; open Dop F
  mkCommutativeMonoid : D₂ _∙_ → D₀ ε → CommutativeMonoid (c ⊔ b) ℓ
  mkCommutativeMonoid _∙′_ ε′ = record
    { isCommutativeMonoid = record { isMonoid = isMonoid ; comm = prop₂ comm }
    } where open Monoid (mkMonoid monoid F _∙′_ ε′)

module _ (g : Group c ℓ) (F : Group.Carrier g → Set b) where
  open Group g hiding (isMonoid) ; open Dop F
  mkGroup : D₂ _∙_ → D₀ ε → D₁ _⁻¹ → Group (c ⊔ b) ℓ
  mkGroup _∙′_ ε′ _⁻¹′ = record
     { _⁻¹ = inj₁ _⁻¹′
     ; isGroup = record { isMonoid = isMonoid
                        ; inverse = prop₁ inverseˡ , prop₁ inverseʳ
                        ; ⁻¹-cong = ⁻¹-cong }
     } where open Monoid (mkMonoid monoid F _∙′_ ε′)

module _ (g : AbelianGroup c ℓ) (F : AbelianGroup.Carrier g → Set b) where
  open AbelianGroup g hiding (isGroup) ; open Dop F
  mkAbelianGroup : D₂ _∙_ → D₀ ε → D₁ _⁻¹ → AbelianGroup (c ⊔ b) ℓ
  mkAbelianGroup _∙′_ ε′ _⁻¹′ = record
    { isAbelianGroup = record { isGroup = isGroup ; comm = prop₂ comm }
    } where open Group (mkGroup group F _∙′_ ε′ _⁻¹′)

module _ (l : Lattice c ℓ) (F : Lattice.Carrier l → Set b) where
  open Lattice l hiding () ; open Dop F
  mkLattice : D₂ _∨_ → D₂ _∧_ → Lattice (c ⊔ b) ℓ
  mkLattice _∨′_ _∧′_ = record
    { Carrier = ∃ F
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

module _ (g : DistributiveLattice c ℓ) (F : DistributiveLattice.Carrier g → Set b) where
  open DistributiveLattice g hiding (isLattice) ; open Dop F
  mkDistributiveLattice : D₂ _∨_ → D₂ _∧_ → DistributiveLattice (c ⊔ b) ℓ
  mkDistributiveLattice _∨′_ _∧′_ = record
    { isDistributiveLattice = record
        { isLattice = isLattice
        ; ∨-distribʳ-∧ = prop₃ ∨-distribʳ-∧
        }
    } where open Lattice (mkLattice lattice F _∨′_ _∧′_)

module _ (r : NearSemiring c ℓ) (F : NearSemiring.Carrier r → Set b) where
  open NearSemiring r hiding (+-isMonoid; *-isSemigroup) ; open Dop F
  mkNearSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → NearSemiring (c ⊔ b) ℓ
  mkNearSemiring _+′_ _*′_ 0#′ = record
    { isNearSemiring = record
        { +-isMonoid = +-isMonoid
        ; *-isSemigroup = *-isSemigroup
        ; distribʳ = prop₃ distribʳ
        ; zeroˡ = prop₁ zeroˡ
        }
    } where open Monoid (mkMonoid +-monoid F _+′_ 0#′)
               renaming (isMonoid to +-isMonoid)
            open Semigroup (mkSemigroup *-semigroup F _*′_)
               renaming (isSemigroup to *-isSemigroup)

module _ (r : SemiringWithoutOne c ℓ) (F : SemiringWithoutOne.Carrier r → Set b) where
  open SemiringWithoutOne r hiding (+-isCommutativeMonoid; *-isSemigroup) ; open Dop F
  mkSemiringWithoutOne : D₂ _+_ → D₂ _*_ → D₀ 0# → SemiringWithoutOne (c ⊔ b) ℓ
  mkSemiringWithoutOne _+′_ _*′_ 0#′ = record
    { isSemiringWithoutOne = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isSemigroup = *-isSemigroup
        ; distrib = prop₃ (proj₁ distrib) , prop₃ (proj₂ distrib)
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open CommutativeMonoid
                   (mkCommutativeMonoid +-commutativeMonoid F _+′_ 0#′)
               renaming (isCommutativeMonoid to +-isCommutativeMonoid)
            open Semigroup (mkSemigroup *-semigroup F _*′_)
               renaming (isSemigroup to *-isSemigroup)

module _ (r : CommutativeSemiringWithoutOne c ℓ)
         (F : CommutativeSemiringWithoutOne.Carrier r → Set b) where
  open CommutativeSemiringWithoutOne r hiding (isSemiringWithoutOne)
  open Dop F
  mkCommutativeSemiringWithoutOne : D₂ _+_ → D₂ _*_ → D₀ 0#
                                  → CommutativeSemiringWithoutOne (c ⊔ b) ℓ
  mkCommutativeSemiringWithoutOne _+′_ _*′_ 0#′ = record
    { isCommutativeSemiringWithoutOne = record
        { isSemiringWithoutOne = isSemiringWithoutOne
        ; *-comm = prop₂ *-comm
        }
    } where open SemiringWithoutOne
                   (mkSemiringWithoutOne semiringWithoutOne F _+′_ _*′_ 0#′)

module _ (r : SemiringWithoutAnnihilatingZero c ℓ) 
         (F : SemiringWithoutAnnihilatingZero.Carrier r → Set b) where
  open SemiringWithoutAnnihilatingZero r hiding (+-isCommutativeMonoid; *-isMonoid)
  open Dop F
  mkSemiringWithoutAnnihilatingZero : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1#
                                    → SemiringWithoutAnnihilatingZero (c ⊔ b) ℓ
  mkSemiringWithoutAnnihilatingZero _+′_ _*′_ 0#′ 1#′ = record
    { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = +-isCommutativeMonoid
        ; *-isMonoid = *-isMonoid
        ; distrib = prop₃ (proj₁ distrib) , prop₃ (proj₂ distrib)
        }
    } where open CommutativeMonoid
                   (mkCommutativeMonoid +-commutativeMonoid F _+′_ 0#′)
               renaming (isCommutativeMonoid to +-isCommutativeMonoid)
            open Monoid (mkMonoid *-monoid F _*′_ 1#′)
               renaming (isMonoid to *-isMonoid)
\end{code}

%<*Semiring>
\begin{code}
module _ (r : Semiring c ℓ) (F : Semiring.Carrier r → Set b) where
  open Semiring r hiding (isSemiringWithoutAnnihilatingZero) ; open Dop F
  mkSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1# → Semiring (c ⊔ b) ℓ
  mkSemiring _+′_ _*′_ 0#′ 1#′ = record
    { isSemiring = record
        { isSemiringWithoutAnnihilatingZero = isSemiringWithoutAnnihilatingZero
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open SemiringWithoutAnnihilatingZero
                    (mkSemiringWithoutAnnihilatingZero
                       semiringWithoutAnnihilatingZero F _+′_ _*′_ 0#′ 1#′)
\end{code}
%</Semiring>

\begin{code}
module _ (r : CommutativeSemiring c ℓ) (F : CommutativeSemiring.Carrier r → Set b) where
  open CommutativeSemiring r hiding (isSemiring) ; open Dop F
  mkCommutativeSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1#
                        → CommutativeSemiring (c ⊔ b) ℓ
  mkCommutativeSemiring _+′_ _*′_ 0#′ 1#′ = record
    { isCommutativeSemiring =
        record { isSemiring = isSemiring
               ; *-comm = prop₂ *-comm
               }
    } where open Semiring (mkSemiring semiring F _+′_ _*′_ 0#′ 1#′)

module _ (r : CancellativeCommutativeSemiring c ℓ) 
         (F : CancellativeCommutativeSemiring.Carrier r → Set b) where
  open CancellativeCommutativeSemiring r hiding (isCommutativeSemiring)
  open Dop F
  mkCancellativeCommutativeSemiring : D₂ _+_ → D₂ _*_ → D₀ 0# → D₀ 1#
                                    → CancellativeCommutativeSemiring (c ⊔ b) ℓ
  mkCancellativeCommutativeSemiring _+′_ _*′_ 0#′ 1#′ = record
    { isCancellativeCommutativeSemiring = record
        { isCommutativeSemiring = isCommutativeSemiring
        ; *-cancelˡ-nonZero = λ (y , _) (z , _) q r → *-cancelˡ-nonZero y z q r
        }
    } where open CommutativeSemiring
                   (mkCommutativeSemiring commutativeSemiring F _+′_ _*′_ 0#′ 1#′)

module _ (r : Ring c ℓ) (F : Ring.Carrier r → Set b) where
  open Ring r hiding (+-isAbelianGroup; *-isMonoid) ; open Dop F
  mkRing : D₂ _+_ → D₂ _*_ → D₁ (-_) → D₀ 0# → D₀ 1# → Ring (c ⊔ b) ℓ
  mkRing _+′_ _*′_ -′_ 0#′ 1#′ = record
    { isRing = record
        { +-isAbelianGroup = +-isAbelianGroup
        ; *-isMonoid = *-isMonoid
        ; distrib = prop₃ (proj₁ distrib) , prop₃ (proj₂ distrib)
        ; zero = prop₁ zeroˡ , prop₁ zeroʳ
        }
    } where open AbelianGroup (mkAbelianGroup +-abelianGroup F _+′_ 0#′ -′_)
               renaming (isAbelianGroup to +-isAbelianGroup)
            open Monoid (mkMonoid *-monoid F _*′_ 1#′)
               renaming (isMonoid to *-isMonoid)

module _ (r : CommutativeRing c ℓ) (F : CommutativeRing.Carrier r → Set b) where
  open CommutativeRing r hiding (isRing) ; open Dop F
  mkCommutativeRing : D₂ _+_ → D₂ _*_ → D₁ (-_) → D₀ 0# → D₀ 1#
                    → CommutativeRing (c ⊔ b) ℓ
  mkCommutativeRing _+′_ _*′_ _-′ 0#′ 1#′ = record
    { isCommutativeRing = record { isRing = isRing  ; *-comm = prop₂ *-comm }
    } where open Ring (mkRing ring F _+′_ _*′_ _-′ 0#′ 1#′)

\end{code}

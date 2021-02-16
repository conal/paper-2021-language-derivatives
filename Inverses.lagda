\sectionl{Some isomorphism properties}

\note{Not to be included in the paper other than for testing.}

\begin{code}

{-# OPTIONS --safe #-}
-- {-# OPTIONS --without-K #-}  -- See f⁻¹∘f∘f⁻¹ below.

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
module ↔Eq {ℓ} = IsEquivalence {ℓ = ℓ} ↔-isEquivalence
import Relation.Binary.Reasoning.Setoid as SetoidR
module ↔R {ℓ} = SetoidR {s₂ = ℓ} (record {isEquivalence = ↔-isEquivalence})

open import Misc {ℓ}

open import Predicate {ℓ}

private
  variable
    A B C D : Set ℓ
    P Q R S : Pred A

---- Basics

-- Function-lifted _↔_
\end{code}
%<*isoFun>
\AgdaTarget{\_⟷\_, ⟷}
\begin{code}
infix 3 _⟷_
_⟷_ : Rel (Pred A) ℓ
P ⟷ Q = ∀ {w} → P w ↔ Q w
\end{code}
%</isoFun>

\begin{code}
infix 3 _⟺_
_⟺_ : Rel (Pred A) ℓ
P ⟺ Q = ∀ {w} → P w ⇔ Q w
\end{code}

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

\begin{code}
≡↔ : A ≡ B → A ↔ B
≡↔ refl = ↔Eq.refl

sym↔ : ∀ {a b : A} → a ≡ b ↔ b ≡ a
sym↔ = mk↔′ sym sym (λ {refl → refl}) (λ {refl → refl})

-- Maybe give this one a more specific name and add ?? : a ≡ b → b ≡ c ↔ a ≡ c
trans↔ : ∀ {a b c : A} → b ≡ c → a ≡ b ↔ a ≡ c
trans↔ refl =
  mk↔′ (λ {refl → refl}) (λ {refl → refl}) (λ {refl → refl}) (λ {refl → refl})
\end{code}

\subsection{Products and sums}

%<*xCongRSig>
\begin{code}
×-congʳ : A ↔ B → (A × C) ↔ (B × C)
\end{code}
%</xCongRSig>
\begin{code}
×-congʳ A↔B = ×-cong A↔B ↔Eq.refl

×-congˡ : C ↔ D → (A × C) ↔ (A × D)
×-congˡ C↔D = ×-cong ↔Eq.refl C↔D
\end{code}

%<*uCongRSig>
\begin{code}
⊎-congʳ : A ↔ B → (A ⊎ C) ↔ (B ⊎ C)
\end{code}
%</uCongRSig>
\begin{code}
⊎-congʳ A↔B = ⊎-cong A↔B ↔Eq.refl

⊎-congˡ : C ↔ D → (A ⊎ C) ↔ (A ⊎ D)
⊎-congˡ C↔D = ⊎-cong ↔Eq.refl C↔D

∃-distrib-⟨×⟩ : ∃ (P ⟨×⟩ Q) ↔ (∃ P × ∃ Q)
∃-distrib-⟨×⟩ {P = P}{Q = Q} = mk↔′
  (λ ((a , b) , (Pa , Qb)) → ((a , Pa) , (b , Qb)))
  (λ ((a , Pa) , (b , Qb)) → ((a , b) , (Pa , Qb)))
  (λ _ → refl)
  (λ _ → refl)

×-transpose : ((A × B) × (C × D)) ↔ ((A × C) × (B × D))
×-transpose = ∃-distrib-⟨×⟩

∃-distrib-∪ : ∃ (P ∪ Q) ↔ (∃ P ⊎ ∃ Q)
∃-distrib-∪ {P = P}{Q} = mk↔′
  (λ {(a , inj₁ p) → inj₁ (a , p) ; (a , inj₂ q) → inj₂ (a , q)})
  (λ {(inj₁ (a , p)) → a , inj₁ p ; (inj₂ (a , q)) → a , inj₂ q})
  (λ {(inj₁ (a , p)) → refl ; (inj₂ (a , q)) → refl})
  (λ {(a , inj₁ p) → refl ; (a , inj₂ q) → refl})

∃-distrib-∅ : Σ A (λ _ → ⊥) ↔ ⊥
∃-distrib-∅ = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

∃-distrib-⊤ : Σ A (λ _ → ⊤) ↔ A
∃-distrib-⊤ = ×-identityʳ _ _

∃-distrib-∩ : ∃ (λ (a , b) → P a × Q b) ↔ (∃ P × ∃ Q)
∃-distrib-∩ = mk↔′
 (λ ((a , b) , (Pa , Qb)) → (a , Pa) , (b , Qb))
 (λ ((a , Pa) , (b , Qb)) → (a , b) , (Pa , Qb))
 (λ ((a , Pa) , (b , Qb)) → refl)
 (λ ((a , b) , (Pa , Qb)) → refl)

∃-×-constˡ : ∃ (λ z → A × Q z) ↔ (A × ∃ Q)
∃-×-constˡ = mk↔′
  (λ (z , (a , Qz)) → a , (z , Qz))
  (λ (a , (z , Qz)) → z , (a , Qz))
  (λ (a , (z , Qz)) → refl)
  (λ (z , (a , Qz)) → refl)

∃-×-constʳ : ∃ (λ z → P z × B) ↔ (∃ P × B)
∃-×-constʳ = mk↔′
  (λ (z , (Pz , b)) → (z , Pz) , b)
  (λ ((z , Pz) , b) → z , (Pz , b))
  (λ ((z , Pz) , b) → refl)
  (λ (z , (Pz , b)) → refl)

×-distrib-∃ˡ : (A × ∃ Q) ↔ ∃ (λ v → A × Q v)
×-distrib-∃ˡ = mk↔′
  (λ (a , b , Qb) → b , a , Qb)
  (λ (b , a , Qb) → a , b , Qb)
  (λ (b , a , Qb) → refl)
  (λ (a , b , Qb) → refl)

×-distrib-∃ʳ : (∃ P × B) ↔ ∃ (λ u → P u × B)
×-distrib-∃ʳ = mk↔′
  (λ ((a , Pa) , b) →  a , Pa  , b)
  (λ ( a , Pa  , b) → (a , Pa) , b)
  (λ ( a , Pa  , b) → refl)
  (λ ((a , Pa) , b) → refl)

\end{code}

\subsection{Existential quantification}
%<*exCongSig>
\begin{code}
∃-cong : (∀ {w} → P w ↔ Q w) → (∃ P ↔ ∃ Q)
\end{code}
%</exCongSig>
\begin{code}
∃-cong P↔Q = mk↔′ (map₂ J.f) (map₂ J.f⁻¹)
  (λ (a , d) → Inverse.f Σ-≡,≡↔≡ (refl , J.inverseˡ d) )
  (λ (a , c) → Inverse.f Σ-≡,≡↔≡ (refl , J.inverseʳ c) )
 where
   module J {t} = Inverse (P↔Q {t} )
\end{code}

\begin{code}
∃₂-cong : ∀ {f g : A → B → Set ℓ} → (∀ {a b} → f a b ↔ g a b) → ∃₂ f ↔ ∃₂ g
∃₂-cong f↔g = ∃-cong (∃-cong f↔g)

∃₃ : ∀ {A : Set ℓ} {B : A → Set ℓ} {C : (x : A) → B x → Set ℓ}
       (D : (x : A) (y : B x) → C x y → Set ℓ) → Set ℓ
∃₃ D = ∃ λ a → ∃₂ λ b c → D a b c

∃₃-cong : ∀ {D E : A → B → C → Set ℓ} → (∀ {a b c} → D a b c ↔ E a b c) → ∃₃ D ↔ ∃₃ E
∃₃-cong D↔E = ∃-cong (∃₂-cong D↔E)
\end{code}

Existentials with various domain shapes:
\begin{code}
∃⊥ : ∀ {P : ⊥ → Set ℓ} → ∃ P ↔ ⊥
∃⊥ = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

∃⊎ : ∀ {P : A ⊎ B → Set ℓ} → ∃ P ↔ (∃ (P ∘ inj₁) ⊎ ∃ (P ∘ inj₂))
∃⊎ = mk↔′
  (λ { (inj₁ b , z) → inj₁ (b , z) ; (inj₂ c , z) → inj₂ (c , z) })
  (λ { (inj₁ (b , z)) → inj₁ b , z ; (inj₂ (c , z)) → inj₂ c , z })
  (λ { (inj₁ _) → refl ; (inj₂ _) → refl })
  (λ { (inj₁ _ , _) → refl ; (inj₂ _ , _) → refl })

∃⊤ : ∀ {P : ⊤ → Set ℓ} → ∃ P ↔ P tt
∃⊤ = mk↔′
  (λ { (tt , Ptt) → Ptt })
  (λ { Ptt → tt , Ptt })
  (λ { Ptt → refl })
  (λ { (tt , Ptt) → refl })

open import Data.Bool

∃Bool : ∀ {P : Bool → Set ℓ} → ∃ P ↔ (P false ⊎ P true)
∃Bool = mk↔′
  (λ { (false , Pfalse) → inj₁ Pfalse ; (true , Ptrue) → inj₂ Ptrue })
  (λ { (inj₁ Pfalse) → false , Pfalse ; (inj₂ Ptrue) → true , Ptrue })
  (λ { (inj₁ Pfalse) → refl ; (inj₂ Ptrue) → refl })
  (λ { (false , Pfalse) → refl ; (true , Ptrue) → refl })

\end{code}

\begin{code}
∃sub : ∀ {f : A → B} {P : B → Set ℓ}
      → (∃ λ b → P (f b)) ↔ (∃ λ c → P c × ∃ λ b → c ≡ f b)
∃sub {f = f}{P} = mk↔′
  (λ { (b , Pc) → f b , Pc , b , refl })
  (λ { (.(f b) , Pc , b , refl) → b , Pc })
  (λ { (.(f b) , Pc , b , refl) → refl })
  (λ { (b , Pc) → refl })

∃×↔∃∃ : ∀ {P : A × B → Set ℓ} → ∃ P ↔ ∃₂ (curry P)
∃×↔∃∃ = mk↔′
  (λ {((b , c) , Pb,c) → b , c , Pb,c})
  (λ {(b , c , Pb,c) → (b , c) , Pb,c})
  (λ {(b , c , Pb,c) → refl})
  (λ {((b , c) , Pb,c) → refl})

∃× : ∃⇃ (λ (a , b) → P a × Q b) ↔ (∃ P × ∃ Q)
∃× = mk↔′
  (λ {((a , b) , (fa , gb)) → (a , fa) , (b , gb)})
  (λ {((a , fa) , (b , gb)) → (a , b) , (fa , gb)})
  (λ _ → refl)
  (λ _ → refl)

∃≡proj₁ : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁} {B : A → Set ℓ₂} {a : A}
        → ∃ (λ (ab : Σ A B) → a ≡ proj₁ ab) ↔ B a
∃≡proj₁ {a = a} = mk↔′
  (λ { ((.a , b) , refl) → b })
  (λ { b → (a , b) , refl })
  (λ { b → refl })
  (λ { ((.a , b) , refl) → refl })

∃≡ : ∀ {x : A} → ∃ (x ≡_) ↔ ⊤
∃≡ {x = x} = mk↔′ (λ {(.x , refl) → tt}) (λ {tt → x , refl})
                  (λ {tt → refl}) (λ {(.x , refl) → refl})
\end{code}

%<*exElimSig>
\begin{code}
∃≡ˡ : ∀ {z} → (∃ λ u → u ≡ z × P u) ↔ P z
\end{code}
%</exElimSig>
\begin{code}
∃≡ˡ {z = z} = mk↔′ (λ {(.z , refl , Pz) → Pz} ) (λ Pz → z , refl , Pz)
                   (λ _ → refl) (λ {(.z , refl , Pz) → refl})

-- Where should ∃¹ and ∃² go?

∃¹ : (A → Pred B) → Pred B
∃¹ f y = ∃ λ x → f x y

∃² : (A → B → Pred C) → Pred C
∃² f z = ∃₂ λ x y → f x y z

∃¹-cong : ∀ {f g : A → Pred B} → (∀ {a} → f a ⟷ g a) → ∃¹ f ⟷ ∃¹ g
∃¹-cong f⟷g = ∃-cong f⟷g

-- ∃¹-cong {D = D}{E} D⟷E {z} =
--   begin
--     ∃¹ D z
--   ≡⟨⟩
--     (∃ λ x → D x z)
--   ≈⟨ ∃-cong D⟷E ⟩
--     (∃ λ x → E x z)
--   ≡⟨⟩
--     ∃¹ E z
--   ∎
--  where open ↔R

-- ∃≡ʳ′ : ∀ {A : Set ℓ} {P : A → Set ℓ} {z} → (∃ λ u → P u × u ≡ z) ↔ P z
-- ∃≡ʳ′ {P = P} {z = z} =
--   begin
--     (∃ λ u → P u × u ≡ z)
--   ≈⟨ ∃-cong (×-comm _ _) ⟩
--     (∃ λ u → u ≡ z × P u)
--   ≈⟨ ∃≡ˡ ⟩
--     P z
--   ∎
--  where open ↔R

-- I'd rather let A and B and the result of P have different sorts, but I got a
-- type error. If and when motivated, try again. Meanwhile, the following
-- version is level-polymorphic.

∃≡ʳ : ∀ {P : A → Set ℓ} {z} → (∃ λ u → P u × u ≡ z) ↔ P z
∃≡ʳ {z = z} = mk↔′
 (λ {(u , Pz , refl) → Pz})
 (λ Pz → z , Pz , refl)
 (λ _ → refl)
 (λ {(u , Pz , refl) → refl})

-- -- I think the level limitations are coming from the IsEquivalence fields
-- -- limiting levels in sym and trans. Can we do equational-style reasoning
-- -- without these limitations?

-- ∃₂≡ˡ′ : ∀ {A : Set ℓ} {B : Set ℓ} {P : A → B → Set ℓ} {y z}
--      → (∃₂ λ u v → (u ≡ y × v ≡ z) × P u v) ↔ P y z
-- ∃₂≡ˡ′ {a = a} {b} {P = P} {y = y} {z} =
--   begin
--     (∃₂ λ u v → (u ≡ y × v ≡ z) × P u v)
--   ≈⟨ ∃₂-cong (×-assoc _ _ _ _) ⟩
--     (∃₂ λ u v → u ≡ y × (v ≡ z × P u v))
--   ≈⟨ ∃∃↔∃∃ _ ⟩
--     (∃₂ λ v u → u ≡ y × (v ≡ z × P u v))
--   ≈⟨ ∃-cong ∃≡ˡ ⟩
--     (∃ λ v → v ≡ z × P y v)
--   ≈⟨ ∃≡ˡ ⟩
--     P y z
--   ∎
--  where open ↔R

-- -- I'd rather let A and B and the result of P have different sorts, but I got a
-- -- type error. If and when motivated, try again. Meanwhile, the following
-- -- version is level-polymorphic.

-- ∃₂≡ˡ : ∀ {A : Set ℓ} {B : Set ℓ} {P : A → B → Set c} {y z}
--      → (∃₂ λ u v → (u ≡ y × v ≡ z) × P u v) ↔ P y z
-- ∃₂≡ˡ {y = y} {z} = mk↔′
--  (λ {(.y , .z , (refl , refl) , Pyz) → Pyz})
--  (λ Pyz → y , z , (refl , refl) , Pyz)
--  (λ Pyz → refl)
--  (λ {(.y , .z , (refl , refl) , Pyz) → refl})

-- ∃₂≡ʳ : ∀ {A : Set ℓ} {B : Set ℓ} {P : A → B → Set c} {y z}
--      → (∃₂ λ u v → P u v × (u ≡ y × v ≡ z)) ↔ P y z
-- ∃₂≡ʳ {y = y} {z} = mk↔′
--  (λ {(.y , .z , Pyz , (refl , refl)) → Pyz})
--  (λ Pyz → y , z , Pyz , (refl , refl))
--  (λ Pyz → refl)
--  (λ {(.y , .z , Pyz , (refl , refl)) → refl})

∃≡² : ∀ {P Q : A → Set ℓ} {v} → (∃ λ p → P p × p ≡ v × Q p) ↔ (P v × Q v)
∃≡² {v = v} = mk↔′
 (λ {(p , Pp , refl , Qp) → Pp , Qp})
 (λ {(Pv , Qv) → v , Pv , refl , Qv})
 (λ {(Pv , Qv) → refl})
 (λ {(p , Pp , refl , Qp) → refl})

-- distrib-∃ˡ : ∀ {A : Set ℓ}{G : Set d → Set ℓ} → (A × ∃ G) ↔ ∃ (λ u → A × G u)   -- ∃ (A *ₗ G)
-- distrib-∃ˡ {A = A}{G = G} = mk↔′
--   (λ (a , u , b) → u , a , b)
--   (λ (u , a , b) → a , u , b)
--   (λ _ → refl)
--   (λ _ → refl)

-- -- TODO: Maybe redefine distrib-∃ˡ via ∃∃↔∃∃

\end{code}

\subsection{Predicates}

\begin{code}

⟨×⟩-cong : ∀ {P R : Pred A} {Q S : Pred B} → P ⟷ R → Q ⟷ S → (P ⟨×⟩ Q) ⟷ (R ⟨×⟩ S)
-- ⟨×⟩-cong P⟷R Q⟷S = ×-cong P⟷R Q⟷S
⟨×⟩-cong P⟷R Q⟷S {a , b} = ×-cong (P⟷R {a}) (Q⟷S {b})

-- ⟨×⟩-cong {P = P}{R}{Q}{S} P⟷R Q⟷S {(a , b)} = let open ↔R in
--   begin
--     (P ⟨×⟩ Q) (a , b)
--   ≡⟨⟩
--     (P a × Q b)
--   ≈⟨ ×-cong P⟷R Q⟷S ⟩
--     (R a × S b)
--   ≡⟨⟩
--     (R ⟨×⟩ S) (a , b)
--   ∎

infixr  2 _⟪×⟫_
_⟪×⟫_ : (A → Pred C) → (B → Pred D) → ((A × B) → Pred (C × D))
(f ⟪×⟫ g) (a , b) = f a ⟨×⟩ g b

∃¹⟪×⟫ : ∀ {f : A → Pred C}{g : B → Pred D} → ∃¹ (f ⟪×⟫ g) ⟷ (∃¹ f ⟨×⟩ ∃¹ g)
∃¹⟪×⟫ = ∃-distrib-⟨×⟩
\end{code}

\begin{code}
module _ {P : A → Set ℓ} (A↔B : A ↔ B) where
  open Inverse A↔B
  open ≡-Reasoning
  private

    g : ∃ P → ∃ (P ∘ f⁻¹)
    g (a , Pa) = f a , subst P (sym (inverseʳ a)) Pa
    -- g (a , Pa) = f a , {!!}

    g⁻¹ : ∃ (P ∘ f⁻¹) → ∃ P
    g⁻¹ (b , Pf⁻¹b) = f⁻¹ b , Pf⁻¹b

    g⁻¹∘g : g⁻¹ ∘ g ≗ id
    g⁻¹∘g (a , Pa) = Inverse.f Σ-≡,≡↔≡ 
                       (inverseʳ a , subst-subst-sym (inverseʳ a))

    -- Two proofs of f⁻¹ (f (f⁻¹ b)) ≡ f⁻¹ b. Uses K.
    open import Axiom.UniquenessOfIdentityProofs.WithK
    f⁻¹∘f∘f⁻¹ : ∀ b → cong f⁻¹ (inverseˡ b) ≡ inverseʳ (f⁻¹ b)
    f⁻¹∘f∘f⁻¹ _ = uip _ _

    g∘g⁻¹ : g ∘ g⁻¹ ≗ id
    g∘g⁻¹ (b , Pf⁻¹b) =
      Inverse.f Σ-≡,≡↔≡
        ( inverseˡ b
        , (begin
             subst (P ∘ f⁻¹) (inverseˡ b)
               (subst P (sym (inverseʳ (f⁻¹ b))) Pf⁻¹b)
           ≡⟨ subst-∘ (inverseˡ b) ⟩
             subst P (cong f⁻¹ (inverseˡ b))
               (subst P (sym (inverseʳ (f⁻¹ b))) Pf⁻¹b)
           ≡⟨ cong (λ z → subst P z _) (f⁻¹∘f∘f⁻¹ b) ⟩
             subst P (inverseʳ (f⁻¹ b))
               (subst P (sym (inverseʳ (f⁻¹ b))) Pf⁻¹b)
           ≡⟨ subst-subst-sym (inverseʳ (f⁻¹ b)) ⟩
             Pf⁻¹b
           ∎)
        )

    -- Phew! Is there an easier proof? And maybe one that doesn't assume K?
    -- Maybe define specialized versions instead. See ∃✶ below.

  ∃dom : ∃ P ↔ ∃ (P ∘ f⁻¹)
  ∃dom = mk↔′ g g⁻¹ g∘g⁻¹ g⁻¹∘g

-- Lists
module _ {X : Set ℓ} where

  private
    variable
      x y : X
      u v w : X ✶

  ∷≡[]↔ : x ∷ w ≡ [] ↔ ⊥
  ∷≡[]↔ = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

  []≡∷↔ : [] ≡ x ∷ w ↔ ⊥
  []≡∷↔ = ↔Eq.trans sym↔ ∷≡[]↔

  ∷≡∷↔ : y ∷ u ≡ x ∷ w ↔ (y ≡ x × u ≡ w)
  ∷≡∷↔ = mk↔′ (λ {refl → refl , refl} ) (λ {(refl , refl) → refl})
              (λ {(refl , refl) → refl}) (λ {refl → refl})

\end{code}
%<*emptyAppend>
\begin{code}
  []≡++ : ([] ≡ u ++ v) ↔ (u , v) ≡ ([] , [])
\end{code}
%</emptyAppend>
\begin{code}[hide]
  []≡++ {u = []} {[]} =
    mk↔′ (λ {refl → refl}) (λ {refl → refl})
         (λ {refl → refl}) (λ {refl → refl})
  []≡++ {u = []} {_ ∷ _} = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())
  []≡++ {u = _ ∷ _}  {_} = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

  module _ where
    open import Closed.Instances using (module Types)
    open Types {ℓ}
    iso = ✶-starˡ X
    open Inverse iso
    open ↔R

    ∃✶A : ∀ {P} → ∃ P ↔ ∃ (P ∘ f⁻¹)
    ∃✶A = ∃dom iso

    -- ∃✶ : ∀ {P} → ∃ P ↔ (P [] ⊎ ∃⇃ (λ (x , xs) → P (x ∷ xs)))
    -- ∃✶ {P = P} =
    --   begin
    --     ∃ P
    --   ≈⟨ ∃dom {A↔B = iso} ⟩
    --     ∃ (P ∘ f⁻¹)
    --   ≡⟨⟩
    --     Σ (⊤ ⊎ X × X ✶)
    --       (λ z → P ((λ { (inj₁ _) → [] ; (inj₂ (x , xs)) → x ∷ xs }) z))
    --   ≈⟨ {!!} ⟩
    --     (P [] ⊎ ∃⇃ (λ (x , xs) → P (x ∷ xs)))
    --   ∎

∃✶ : ∀ {X} {P : X ✶ → Set ℓ} → ∃ P ↔ (P [] ⊎ ∃⇃ λ (x , xs) → P (x ∷ xs))
∃✶ {P = P} = mk↔′
  (λ { ([] , P[]) → inj₁ P[] ; (x ∷ xs , Px∷xs) → inj₂ ((x , xs) , Px∷xs) })
  (λ { (inj₁ P[]) → [] , P[] ; (inj₂ ((x , xs) , Px∷xs)) → (x ∷ xs) , Px∷xs })
  (λ { (inj₁ P[]) → refl ; (inj₂ ((x , xs) , Px∷xs)) → refl })
  (λ { ([] , P[]) → refl ; (x ∷ xs , Px∷xs) → refl })

\end{code}

\begin{code}
---- Equivalence and decidability

module _ where

  open import Relation.Nullary           using (Dec)
  open import Relation.Nullary.Decidable using () renaming (map to map?⇔)
  open import Relation.Unary             using (Decidable)

  ↔→⇔ : (A ↔ B) → (A ⇔ B)
  ↔→⇔ A↔B = equivalence f f⁻¹ where open Inverse A↔B

\end{code}
%<*mapDec>
\begin{code}
  map?↔ : A ↔ B → Dec A → Dec B
\end{code}
%</mapDec>
\begin{code}
  map?↔ = map?⇔ ∘ ↔→⇔
\end{code}
%<*mapDecInv>
\AgdaTarget{map?⁻¹}
\begin{code}
  map?⁻¹ : B ↔ A → Dec A → Dec B
\end{code}
%</mapDecInv>
\begin{code}
  map?⁻¹ = map?↔ ∘ ↔Eq.sym

  -- map?⁻¹∘ : {X : Set ℓ} → B ↔ A → (X → Dec A) → (X → Dec B)
  map?⁻¹∘ : {W : Set ℓ}{A B : W → Set ℓ}
          → (B ⟷ A) → ((s : W) → Dec (A s)) → ((s : W) → Dec (B s))
  map?⁻¹∘ iso f x = map?⁻¹ iso (f x)

\end{code}

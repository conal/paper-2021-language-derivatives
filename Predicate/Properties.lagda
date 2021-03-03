\section{Predicate Properties}

\begin{code}
{-# OPTIONS --safe #-}

-- Some properties of predicates

open import Level

module Predicate.Properties {ℓ : Level} where

open import Data.Unit.Polymorphic   using (⊤)
open import Data.Product
open import Data.Product.Properties using (×-≡,≡↔≡; ∃∃↔∃∃)
open import Data.Product.Algebra
open import Data.Sum                using (inj₁; inj₂)
open import Algebra.Core
open import Algebra.Definitions
open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≗_; cong; module ≡-Reasoning) renaming (refl to refl≡; sym to sym≡)
open import Function using (id; _∘_; const; flip; _↔_; Inverse; mk↔′)
open import Relation.Unary using (_⊢_)

open import Data.Product.Algebra using (Σ-assoc)

-- Local
open import Misc {ℓ}
open import Inverses {ℓ} -- using (module ↔Eq; module ↔R; ∃≡ˡ)
import Algebra.Construct.Function as C
open import Closed ; open Closed.Types {ℓ}

open ClosedCommutativeSemiring ×-⊎-closedCommutativeSemiring

-- Pred as semimodule
Pred-Semimodule : Set ℓ → Semimodule (×-⊎-commutativeSemiring ℓ) _ _
Pred-Semimodule A = C.semimodule A

module Pred-Semimodule {A} = Semimodule (Pred-Semimodule A)
open Pred-Semimodule

open import Predicate {ℓ}

-- Most of these attempts fail in the presence of level polymorphism, because
-- equational reasoning and sym require before & after to have the same type,
-- while type isomorphisms often change levels.

private
  variable
    A B C D : Set ℓ
    a b c d : A
    p q r s : Set ℓ
    P Q R S : Pred A


infixr 2 _↦_
_↦_ : A → Set ℓ → Pred A
(a ↦ b) w = (w ≡ a) × b

infixr 2 _⤇_   -- or ⇰
_⤇_ : (B → A) → (B → Set ℓ) → B → Pred A
(f ⤇ g) a = f a ↦ g a

infixr 2 _⇐_
_⇐_ : (A → B) → (Pred A → Pred B)
_⇐_ = mapⱽ

pred-decomp : P ⟷ (∃¹ λ a → a ↦ P a)
-- pred-decomp = sym (trans (∃-cong (×-congʳ ≡↔)) ∃≡ˡ) where open ↔Eq

pred-decomp {P = P} {w} =
  begin
    P w
  ≈˘⟨ ∃≡ˡ ⟩
    (∃ λ a → a ≡ w × P a)
  ≈⟨ ∃-cong (×-congʳ sym↔) ⟩
    (∃ λ a → w ≡ a × P a)
  ≡⟨⟩
    (∃ λ a → (a ↦ P a) w)
  ≡⟨⟩
    (∃¹ λ a → a ↦ P a) w
  ∎
 where open ↔R

-- TODO: rename ∃¹ to ∑ᴹ

pureⱽ-cong : a ≡ b → pureⱽ a ⟷ pureⱽ b
pureⱽ-cong refl≡ = ↔Eq.refl

pureⱽ, : ∀ {a : A}{b : B} → pureⱽ (a , b) ⟷ (pureⱽ a ⟨×⟩ pureⱽ b)
pureⱽ, = ↔Eq.sym ×-≡,≡↔≡

-- pureⱽ, {a = a}{b = b}{w = (u , v)} = let open ↔R in
--   begin
--     pureⱽ (a , b) (u , v)
--   ≡⟨⟩
--     (u , v) ≡ (a , b)
--   ≈˘⟨ ×-≡,≡↔≡ ⟩
--     (u ≡ a × v ≡ b)
--   ≡⟨⟩
--     (pureⱽ a ⟨×⟩ pureⱽ b) (u , v)
--   ∎

↦-cong : a ≡ b → p ↔ q → (a ↦ p) ⟷ (b ↦ q)
↦-cong refl≡ = *ᵣ-congˡ

↦-congˡ : p ↔ q → (a ↦ p) ⟷ (a ↦ q)
↦-congˡ = ↦-cong refl≡

↦-congʳ : a ≡ b → (a ↦ p) ⟷ (b ↦ p)
↦-congʳ = flip ↦-cong ↔Eq.refl

↦-distrib-+ : (a ↦ p + q) ⟷ ((a ↦ p) +ᴹ (a ↦ q))
↦-distrib-+ {a = a}{p}{q} = let open ⟷R in
  begin
    (a ↦ p + q)
  ≡⟨⟩
    pureⱽ a *ᵣ (p + q)
  ≈⟨ *ᵣ-distribˡ (pureⱽ a) p q ⟩
    pureⱽ a *ᵣ p +ᴹ pureⱽ a *ᵣ q
  ≡⟨⟩
    (a ↦ p) +ᴹ (a ↦ q)
  ∎

*ᵣ-distrib-∃ˡ : (P *ᵣ ∃ Q) ⟷ ∃¹ (λ u → P *ᵣ Q u)
*ᵣ-distrib-∃ˡ = ×-distrib-∃ˡ

-- *ᵣ-distrib-∃ˡ {P = P} {Q = Q} {w} = let open ↔R in
--   begin
--     (P *ᵣ ∃ Q) w
--   ≡⟨⟩
--     P w * ∃ Q
--   ≈⟨ ×-distrib-∃ˡ ⟩
--     ∃ (λ u → P w * Q u)   -- ≡⟨⟩ ∃ (P w ·ₗ Q)
--   ≡⟨⟩
--     ∃¹ (λ u → P *ᵣ Q u) w
--   ∎

-- ↦-distrib-∃ˡ : (a ↦ ∃ Q) ⟷ ∃¹ (λ u → a ↦ Q u)
↦-distrib-∃ˡ : (a ↦ ∃ Q) ⟷ ∃¹ (const a ⤇ Q)
↦-distrib-∃ˡ = ×-distrib-∃ˡ

-- ↦-distrib-∃ˡ {a = a} = *ᵣ-distrib-∃ˡ {P = pureⱽ a}

-- ↦-distrib-∃ˡ {a = a}{Q = Q} = let open ⟷R in
--   begin
--     (a ↦ ∃ Q)
--   ≡⟨⟩
--     pureⱽ a *ᵣ ∃ Q
--   ≈⟨ *ᵣ-distrib-∃ˡ {P = pureⱽ a} ⟩
--     ∃¹ (λ u → pureⱽ a *ᵣ Q u)
--   ≡⟨⟩
--     ∃¹ (λ u → a ↦ Q u)
--   ∎

-- TODO: try replacing explicit extensional equality with implicit.

mapⱽ-cong : ∀ {f g : A → B} → f ≗ g → P ⟷ Q → mapⱽ f P ⟷ mapⱽ g Q
-- mapⱽ-cong f≗g P⟷Q = ∃-cong (*-cong (trans↔ (f≗g _)) P⟷Q)

mapⱽ-cong {P = P}{Q} {f = f}{g} f≗g P⟷Q {w} = let open ⟷R in
  begin
    mapⱽ f P
  ≡⟨⟩
    ∃¹ (λ u → f u ↦ P u)
  ≈⟨ ∃-cong (↦-cong (f≗g _) P⟷Q) ⟩
    ∃¹ (λ u → g u ↦ Q u)
  ≡⟨⟩
    mapⱽ g Q
  ∎

mapⱽ-congʳ : ∀ {f g : A → B} → f ≗ g → mapⱽ f P ⟷ mapⱽ g P
mapⱽ-congʳ f≗g {w} = mapⱽ-cong f≗g (⟷Eq.refl {w = w})

mapⱽ-congˡ : ∀ {f : A → B} → P ⟷ Q → mapⱽ f P ⟷ mapⱽ f Q
mapⱽ-congˡ P⟷Q {w} = mapⱽ-cong (λ _ → refl≡) P⟷Q

mapⱽ₂-cong : ∀ {f g : A → B → C} → (∀ a b → f a b ≡ g a b) → P ⟷ R → Q ⟷ S
           → mapⱽ₂ f P Q ⟷ mapⱽ₂ g R S
mapⱽ₂-cong {A = A}{B = B} f∼g P∼R Q∼S =
  mapⱽ-cong (uncurry f∼g) (λ {(a , b)} → ⟨×⟩-cong (P∼R {w = a}) (Q∼S {w = b}) {w = a , b})

mapⱽ₂-congˡ : ∀ {f : A → B → C} → P ⟷ R → Q ⟷ S
            → mapⱽ₂ f P Q ⟷ mapⱽ₂ f R S
mapⱽ₂-congˡ = mapⱽ₂-cong (λ _ _ → refl≡)

mapⱽ₂-congʳ : ∀ {f g : A → B → C} → (∀ a b → f a b ≡ g a b)
            → mapⱽ₂ f P Q ⟷ mapⱽ₂ g P Q
mapⱽ₂-congʳ f∼g = mapⱽ-congʳ (uncurry f∼g)
-- mapⱽ₂-congʳ f∼g = mapⱽ₂-cong f∼g ⟷Eq.refl ⟷Eq.refl

-- mapⱽ₃-congʳ : ∀ {f g : A → B → C → D} → (∀ a b c → f a b c ≡ g a b c)
--             → mapⱽ₃ f P Q R ⟷ mapⱽ₃ g P Q R
-- mapⱽ₃-congʳ f∼g = mapⱽ-congʳ (uncurry₃ʳ f∼g)

-- mapⱽ is a (covariant) functor

mapⱽ-id : mapⱽ id P ⟷ P
mapⱽ-id {P = P} =
  begin
    mapⱽ id P
  ≡⟨⟩
    (∃¹ λ a → id a ↦ P a)
  ≡⟨⟩
    (∃¹ λ a → a ↦ P a)
  ≈˘⟨ pred-decomp ⟩
    P
  ∎
 where open ⟷R

-- mapⱽ-id {w = w} = ⟷Eq.sym (pred-decomp {w = w}) {w = w}

mapⱽ-∘ : ∀ {f : A → B} {g : B → C} → mapⱽ (g ∘ f) P ⟷ mapⱽ g (mapⱽ f P)
mapⱽ-∘ {A = A} {B = B} {C = C}{P = P}{f}{g} {w = w} =
  begin
    mapⱽ (g ∘ f) P w
  ≡⟨⟩
    (∃ λ a → w ≡ g (f a) × P a)
  ≈˘⟨ ∃-cong ∃≡² ⟩
    (∃₂ λ a b → w ≡ g b × b ≡ f a × P a)
  ≈⟨ ∃∃↔∃∃ _ ⟩
    (∃₂ λ b a → w ≡ g b × b ≡ f a × P a)
  ≈⟨ ∃-cong (∃∃↔∃∃ _) ⟩
    (∃ λ b → w ≡ g b × ∃ λ a → b ≡ f a × P a)
  ≡⟨⟩
    (∃ λ b → w ≡ g b × mapⱽ f P b)
  ≡⟨⟩
    (∃¹ λ b → g b ↦ mapⱽ f P b) w
  ≡⟨⟩
    mapⱽ g (mapⱽ f P) w
  ∎
 where open ↔R

-- Try mapⱽ-∘ with ⟷R instead of ↔R (dropping w):

-- (a ↦ p) *ᵣ q ⟷ (a ↦ p * q)
-- p ·ₗ (a ↦ q) ⟷ (a ↦ p * q)

↦-↦ : ∀ {g : B → A} → ∃¹ (λ b′ → g b′ ↦ (b ↦ p) b′) ⟷ (g b ↦ p)
↦-↦ {b = b}{p = p}{g = g} {w = w} = let open ↔R in
  begin 
    ∃¹ (λ b′ → g b′ ↦ (b ↦ p) b′) w
  ≡⟨⟩
    ∃ (λ b′ → (g b′ ↦ (b ↦ p) b′) w)
  ≡⟨⟩
    ∃ (λ b′ → (g b′ ↦ pureⱽ b b′ * p) w)
  ≡⟨⟩
    ∃ (λ b′ → pureⱽ (g b′) w * (pureⱽ b b′ * p))
  ≈⟨ ∃≡² ⟩
    pureⱽ (g b) w * p
  ≡⟨⟩
    (g b ↦ p) w
  ∎

mapⱽ-∘₂ : ∀ {f : A → B} {g : B → C} → mapⱽ (g ∘ f) P ⟷ mapⱽ g (mapⱽ f P)
mapⱽ-∘₂ {A = A} {B = B} {C = C}{P = P}{f}{g} = let open ⟷R in
  begin
    mapⱽ (g ∘ f) P
  ≡⟨⟩
    ∃¹ (λ a → g (f a) ↦ P a)
  ≈˘⟨ ∃-cong ↦-↦ ⟩
    ∃² (λ a b → g b ↦ (f a ↦ P a) b)
  ≈⟨ ∃∃↔∃∃ _ ⟩
    ∃² (λ b a → g b ↦ (f a ↦ P a) b)
  ≡⟨⟩
    ∃¹ (λ b → ∃¹ λ a → g b ↦ (f a ↦ P a) b) 
  ≈˘⟨ ∃-cong ↦-distrib-∃ˡ ⟩
    ∃¹ (λ b → g b ↦ ∃ (λ a → (f a ↦ P a) b))
  ≡⟨⟩
    ∃¹ (λ b → g b ↦ ∃¹ (λ a → f a ↦ P a) b)
  ≡⟨⟩
    ∃¹ (λ b → g b ↦ ∃¹ (f ⤇ P) b)
  ≡⟨⟩
    ∃¹ (λ b → g b ↦ mapⱽ f P b)
  ≡⟨⟩
    ∃¹ (g ⤇ mapⱽ f P)
  ≡⟨⟩
    mapⱽ g (mapⱽ f P)
  ∎

mapⱽ-⁻¹ : ∀ {f : A → B} {g : B → A} → (g ∘ f ≗ id) → mapⱽ g (mapⱽ f P) ⟷ P
mapⱽ-⁻¹ {P = P}{f = f}{g = g} g∘f≗id = let open ⟷R in
  begin
    mapⱽ g (mapⱽ f P)
  ≈˘⟨ mapⱽ-∘ ⟩  
    mapⱽ (g ∘ f) P
  ≈⟨ mapⱽ-congʳ g∘f≗id ⟩  
    mapⱽ id P
  ≈⟨ mapⱽ-id ⟩  
    P
  ∎

-- Note similarity to the proof that 𝒟 (f⁻¹) ≡ (𝒟 f)⁻¹ via the chain rule.

-- TODO: define _⟺_ or similar for function-lifted _⟷_. Use in mapⱽ-id, mapⱽ-∘,
-- and mapⱽ-⁻¹, eg mapⱽ g ∘ mapⱽ f ⟺ id .

-- TODO: Tidy mapⱽ-id and mapⱽ-∘ proofs using _⤇_ .

-- TODO: can we prove mapⱽ-∘ without introducing w? I tried and failed.

-- *ᵣ⟨×⟩*ᵣ : (P *ᵣ p ⟨×⟩ Q *ᵣ q) ⟷ (P ⟨×⟩ Q) *ᵣ (p × q)
-- *ᵣ⟨×⟩*ᵣ = ×-transpose

-- *ᵣ⟨×⟩*ᵣ {P = P}{p = p}{Q = Q}{q = q} {w = u , v} = let open ↔R in
--   begin
--     (P *ᵣ p ⟨×⟩ Q *ᵣ q) (u , v)
--   ≡⟨⟩
--     ((P *ᵣ p) u × (Q *ᵣ q) v)
--   ≡⟨⟩
--     ((P u × p) × (Q v × q))
--   ≈⟨ ×-transpose ⟩
--     ((P u × Q v) × (p × q))
--   ≡⟨⟩
--     ((P ⟨×⟩ Q) *ᵣ (p × q)) (u , v)
--   ∎

,↦× :  {a : A} {b : B} {p q : Set ℓ} → ((a , b) ↦ (p × q)) ⟷ ((a ↦ p) ⟨×⟩ (b ↦ q))
,↦× {a = a}{b}{p}{q} = let open ⟷R in
  begin
    ((a , b) ↦ p × q)
  ≡⟨⟩
    pureⱽ (a , b) *ᵣ (p × q)
  ≈⟨ *ᵣ-cong {x = pureⱽ _} pureⱽ, ↔Eq.refl ⟩
    (pureⱽ a ⟨×⟩ pureⱽ b) *ᵣ (p × q)
  ≈⟨ ×-transpose ⟩
    ((pureⱽ a *ᵣ p) ⟨×⟩ (pureⱽ b *ᵣ q))
  ≡⟨⟩
    ((a ↦ p) ⟨×⟩ (b ↦ q))
  ∎

-- TODO: eliminate uses of ×-transpose, which is proved via ×-comm.
-- Maybe pureⱽ generally do commute because their values are 1 or 0.

-- TODO: I think _⟨×⟩_ is a direct product of semimodules. What about semidirect
-- products? IIRC, Brent Yorgey and Dan Piponi have each done something with
-- semidirect products.

infixr  2 _⊗_
_⊗_ : (A → C) → (B → D) → (A × B → C × D)
(f ⊗ g) (a , b) = (f a , g b)

mapⱽ-⊗ : ∀ {f : A → C} {g : B → D}
       → mapⱽ (f ⊗ g) (P ⟨×⟩ Q) ⟷ (mapⱽ f P ⟨×⟩ mapⱽ g Q)
mapⱽ-⊗ {P = P}{Q = Q}{f = f}{g} = let open ⟷R in
  begin
    ∃¹ ((f ⊗ g) ⤇ (P ⟨×⟩ Q))
  ≈⟨ ∃¹-cong {f = _ ⤇ _} ,↦× ⟩
    ∃¹ ((f ⤇ P) ⟪×⟫ (g ⤇ Q))
  ≈⟨ ∃-distrib-⟨×⟩ ⟩
    (∃¹ (f ⤇ P) ⟨×⟩ ∃¹ (g ⤇ Q))
  ∎

mapⱽ-map₁ : ∀ {f : A → C} → mapⱽ (map₁ f) (P ⟨×⟩ Q) ⟷ (mapⱽ f P ⟨×⟩ Q)
mapⱽ-map₁ {P = P}{Q = Q}{f = f} = let open ⟷R in
  begin
    mapⱽ (map₁ f) (P ⟨×⟩ Q)
  ≡⟨⟩
    mapⱽ (f ⊗ id) (P ⟨×⟩ Q)
  ≈⟨ mapⱽ-⊗ ⟩
    (mapⱽ f P ⟨×⟩ mapⱽ id Q)
  ≈⟨ *-congˡ mapⱽ-id ⟩
    (mapⱽ f P ⟨×⟩ Q)
  ∎

mapⱽ-map₂ : ∀ {g : B → D} → mapⱽ (map₂ g) (P ⟨×⟩ Q) ⟷ (P ⟨×⟩ mapⱽ g Q)
mapⱽ-map₂ {P = P}{Q = Q}{g = g} = let open ⟷R in
  begin
    mapⱽ (map₂ g) (P ⟨×⟩ Q)
  ≡⟨⟩
    mapⱽ (id ⊗ g) (P ⟨×⟩ Q)
  ≈⟨ mapⱽ-⊗ ⟩
    (mapⱽ id P ⟨×⟩ mapⱽ g Q)
  ≈⟨ *-congʳ mapⱽ-id ⟩
    (P ⟨×⟩ mapⱽ g Q)
  ∎

-- Connection between covariant and contravariant functors

module _ (A↔B : A ↔ B) where
  open Inverse A↔B
  -- TODO: Can we avoid K?
  open import Axiom.UniquenessOfIdentityProofs.WithK using (uip)

  ≡⁻¹ : b ≡ f a  ↔  a ≡ f⁻¹ b
  ≡⁻¹ {b = b}{a = a} = mk↔′
    (λ {refl≡ → sym≡ (inverseʳ a)})
    (λ {refl≡ → sym≡ (inverseˡ b)})
    (λ a≡f⁻¹b → uip _ a≡f⁻¹b)
    (λ a≡f⁻¹b → uip _ a≡f⁻¹b)

  -- ⇐-⊢ : ∀ {A↔B : A ↔ B} → mapⱽ f (P ∘ f) ⟷ P
  ⇐-⊢ : (f ⇐ (f ⊢ P)) ⟷ P
  ⇐-⊢ {P = P} = let open ⟷R in
    begin
      mapⱽ f (P ∘ f)
    ≡⟨⟩
      ∃¹ (f ⤇ P ∘ f)
    ≡⟨⟩
      ∃¹ (λ a → f a ↦ P (f a))
    ≡⟨⟩
      ∃¹ (λ a → pureⱽ (f a) *ᵣ P (f a))
    ≡⟨⟩
      ∃¹ (λ a b → b ≡ f a × P (f a))
    ≈⟨ ∃¹-cong (λ {a b} → *-congʳ (≡⁻¹ {b = b})) ⟩
      ∃¹ (λ a b → a ≡ f⁻¹ b × P (f a))
    ≡⟨⟩
      (λ b → ∃ λ a → a ≡ f⁻¹ b × P (f a))
    ≈⟨ ∃≡ˡ ⟩
      (λ b → P (f (f⁻¹ b)))
    ≈⟨ ≡↔ (cong P (inverseˡ _)) ⟩
      (λ b → P b)
    ≡⟨⟩
      P
    ∎

-- (f ⇐ (f ⊢ P)) ⟷ P
-- f ⇐_ ∘ f ⊢_ ⟺ id

-- TODO: Something about g ∘ f ≡ id → (g ⇐ P) ⟷ (f ⊢ P)
-- Rethink the operator names.

mapⱽ-comm : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → Commutative _≡_ _∙_ → Commutative _⟷_ (mapⱽ₂ _∙_)
mapⱽ-comm {A = A}{_∙_ = _∙_} ∙-comm P Q = let open ⟷R in
  begin
    mapⱽ ◻ (P ⟨×⟩ Q)
  ≈⟨ mapⱽ-cong (uncurry ∙-comm) (*-comm _ _) ⟩  -- ⟨×⟩-comm {P = P} {Q = Q}
    mapⱽ (◻ ∘ swap) ((Q ⟨×⟩ P) ∘ swap)
  ≈⟨ mapⱽ-∘ ⟩
    mapⱽ ◻ (mapⱽ swap ((Q ⟨×⟩ P) ∘ swap))
  ≈⟨ mapⱽ-congˡ (⇐-⊢ (*-comm A A)) ⟩
    mapⱽ ◻ (Q ⟨×⟩ P)
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_
       ◻ = uncurry _∙_

-- TODO: consider using converse from Relation.Unary:
-- 
-- _~ : Pred (A × B) ℓ → Pred (B × A) ℓ
-- P ~ = P ∘ swap

mapⱽ-assoc : ∀ {A : Set ℓ} {∙ : Op₂ A} → Associative _≡_ ∙ → Associative _⟷_ (mapⱽ₂ ∙)
mapⱽ-assoc {A = A}{∙ = ∙} ∙-assoc P Q R = let open ⟷R in
  begin
    (P ⋆ Q) ⋆ R
  ≡⟨⟩
    mapⱽ₂ ∙ (mapⱽ₂ ∙ P Q) R
  ≡⟨⟩
    mapⱽ ◻ (mapⱽ ◻ (P ⟨×⟩ Q) ⟨×⟩ R)
  ≈˘⟨ mapⱽ-congˡ mapⱽ-map₁ ⟩
    mapⱽ ◻ (mapⱽ (map₁ ◻) ((P ⟨×⟩ Q) ⟨×⟩ R))
  ≈˘⟨ mapⱽ-∘ ⟩
    mapⱽ (◻ ∘ map₁ ◻) ((P ⟨×⟩ Q) ⟨×⟩ R)
  ≈⟨ mapⱽ-cong (uncurry₃ˡ ∙-assoc) (*-assoc _ _ _) ⟩
    mapⱽ (◻ ∘ map₂ ◻ ∘ assocʳ) ((P ⟨×⟩ (Q ⟨×⟩ R)) ∘ assocʳ)
  ≈⟨ mapⱽ-∘ ⟩
    mapⱽ (◻ ∘ map₂ ◻) (mapⱽ assocʳ ((P ⟨×⟩ (Q ⟨×⟩ R)) ∘ assocʳ))
  ≈⟨ mapⱽ-congˡ (⇐-⊢ (*-assoc A A A)) ⟩
    mapⱽ (◻ ∘ map₂ ◻) (P ⟨×⟩ (Q ⟨×⟩ R)) 
  ≈⟨ mapⱽ-∘ ⟩
    mapⱽ ◻ (mapⱽ (map₂ ◻) (P ⟨×⟩ (Q ⟨×⟩ R))) 
  ≈⟨ mapⱽ-congˡ mapⱽ-map₂ ⟩
    mapⱽ ◻ (P ⟨×⟩ mapⱽ ◻ (Q ⟨×⟩ R))
  ≡⟨⟩
    mapⱽ₂ ∙ P (mapⱽ₂ ∙ Q R)
  ≡⟨⟩
    P ⋆ (Q ⋆ R)
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ ∙
       ◻ = uncurry ∙

-- TODO: Simplify mapⱽ-comm and mapⱽ-assoc

mapⱽ-identityˡ : ∀ {A : Set ℓ} {∙ : Op₂ A} {ε : A}
               → LeftIdentity _≡_ ε ∙ → LeftIdentity _⟷_ (pureⱽ ε) (mapⱽ₂ ∙)
mapⱽ-identityˡ {∙ = _∙_}{ε = ε} identityˡ Q {w} = let open ↔R in
  begin
    (pureⱽ ε ⋆ Q) w
  ≡⟨⟩
    (∃ λ (u , v) → w ≡ u ∙ v × pureⱽ ε u × Q v)
  ≈⟨ Σ-assoc ⟩
    (∃₂ λ u v → w ≡ u ∙ v × u ≡ ε × Q v)
  ≈⟨ ∃∃↔∃∃ _ ⟩
    (∃₂ λ v u → w ≡ u ∙ v × u ≡ ε × Q v)
  ≈⟨ ∃-cong ∃≡² ⟩
    (∃ λ v → w ≡ ε ∙ v × Q v)
  ≈⟨ ∃-cong (*-congʳ (trans↔ (identityˡ _))) ⟩
    (∃ λ v → w ≡ v × Q v)
  ≈⟨ ∃-cong (*-congʳ sym↔) ⟩
    (∃ λ v → v ≡ w × Q v)
  ≈⟨ ∃≡ˡ ⟩
    Q w
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_

mapⱽ-identityʳ : ∀ {A : Set ℓ} {∙ : Op₂ A} {ε : A}
               → RightIdentity _≡_ ε ∙ → RightIdentity _⟷_ (pureⱽ ε) (mapⱽ₂ ∙)
mapⱽ-identityʳ {∙ = _∙_}{ε = ε} identityʳ P {w} = let open ↔R in
  begin
    (P ⋆ pureⱽ ε) w
  ≡⟨⟩
    (∃ λ (u , v) → w ≡ u ∙ v × P u × pureⱽ ε v)
  ≡⟨⟩
    (∃ λ (u , v) → w ≡ u ∙ v × P u × v ≡ ε)
  ≈˘⟨ ∃-cong (*-assoc _ _ _) ⟩
    (∃ λ (u , v) → (w ≡ u ∙ v × P u) × v ≡ ε)
  ≈⟨ Σ-assoc ⟩
    (∃₂ λ u v → (w ≡ u ∙ v × P u) × v ≡ ε)
  ≈⟨ ∃-cong ∃≡ʳ ⟩
    (∃ λ u → w ≡ u ∙ ε × P u)
  ≈⟨ ∃-cong (*-congʳ (trans↔ (identityʳ _))) ⟩
    (∃ λ u → w ≡ u × P u)
  ≈⟨ ∃-cong (*-congʳ sym↔) ⟩
    (∃ λ u → u ≡ w × P u)
  ≈⟨ ∃≡ˡ ⟩
    P w
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_

mapⱽ-identity : ∀ {A : Set ℓ} {∙ : Op₂ A} {ε : A}
              → Identity _≡_ ε ∙ → Identity _⟷_ (pureⱽ ε) (mapⱽ₂ ∙)
mapⱽ-identity (identityˡ , identityʳ) = mapⱽ-identityˡ identityˡ , mapⱽ-identityʳ identityʳ


mapⱽ-distribˡ : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → _DistributesOverˡ_ _⟷_ (mapⱽ₂ _∙_) _+ᴹ_
mapⱽ-distribˡ {_∙_ = _∙_} P Q R = let open ⟷R in
  begin
    P ⋆ (Q +ᴹ R)
  ≡⟨⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ P u * (Q v + R v))
  ≈⟨ ∃-cong (↦-congˡ (distribˡ _ _ _)) ⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ (P u * Q v + P u * R v))
  ≈⟨ ∃-cong ↦-distrib-+ ⟩
    ∃¹ (λ (u , v) → (u ∙ v ↦ P u * Q v) +ᴹ (u ∙ v ↦ P u * R v))
  ≈⟨ ∃-distrib-∪ ⟩
    P ⋆ Q +ᴹ P ⋆ R
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_

mapⱽ-distribʳ : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → _DistributesOverʳ_ _⟷_ (mapⱽ₂ _∙_) _+ᴹ_
mapⱽ-distribʳ {_∙_ = _∙_} R P Q = let open ⟷R in
  begin
    (P +ᴹ Q) ⋆ R
  ≡⟨⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ (P u + Q u) * R v)
  ≈⟨ ∃-cong (↦-congˡ (distribʳ _ _ _)) ⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ (P u * R v + Q u * R v))
  ≈⟨ ∃-cong ↦-distrib-+ ⟩
    ∃¹ (λ (u , v) → (u ∙ v ↦ P u * R v) +ᴹ (u ∙ v ↦ Q u * R v))
  ≈⟨ ∃-distrib-∪ ⟩
    P ⋆ R +ᴹ Q ⋆ R
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_

mapⱽ-distrib : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → _DistributesOver_ _⟷_ (mapⱽ₂ _∙_) _+ᴹ_
mapⱽ-distrib = mapⱽ-distribˡ , mapⱽ-distribʳ

↦-0# : (a ↦ 0#) ⟷ 0ᴹ
↦-0# = *ᵣ-zeroʳ (pureⱽ _)

-- ↦-0# {a = a} = let open ⟷R in
--   begin
--     (a ↦ 0#)
--   ≡⟨⟩
--     pureⱽ a *ᵣ 0#
--   ≈⟨ *ᵣ-zeroʳ (pureⱽ a) ⟩
--     0ᴹ
--   ∎

mapⱽ-zeroˡ : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → LeftZero _⟷_ 0ᴹ (mapⱽ₂ _∙_)
mapⱽ-zeroˡ {A = A}{_∙_ = _∙_} P = let open ⟷R in
  begin
    0ᴹ ⋆ P
  ≡⟨⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ 0ᴹ u * P v)
  ≈⟨ ∃-cong (↦-congˡ (zeroˡ _)) ⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ 0#)
  ≈⟨ ∃-cong ↦-0# ⟩
    ∃¹ (const 0ᴹ)
  ≡⟨⟩
    const (∃ 0ᴹ)
  ≡⟨⟩
    const ((A × A) * 0#)
  ≈⟨ zeroʳ (A × A) ⟩
    const 0#
  ≡⟨⟩
    0ᴹ
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_

mapⱽ-zeroʳ : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → RightZero _⟷_ 0ᴹ (mapⱽ₂ _∙_)
mapⱽ-zeroʳ {A = A}{_∙_ = _∙_} P = let open ⟷R in
  begin
    P ⋆ 0ᴹ
  ≡⟨⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ P u * 0ᴹ v)
  ≡⟨⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ P u * 0ᴹ v)
  ≡⟨⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ P u * 0#)
  ≈⟨ ∃-cong (↦-congˡ (zeroʳ _)) ⟩
    ∃¹ (λ (u , v) → u ∙ v ↦ 0#)
  ≈⟨ ∃-cong ↦-0# ⟩
    const ((A × A) * 0#)
  ≈⟨ zeroʳ (A × A) ⟩
    0ᴹ
  ∎
 where infixl 7 _⋆_
       _⋆_ = mapⱽ₂ _∙_

mapⱽ-zero : ∀ {A : Set ℓ} {_∙_ : Op₂ A} → Zero _⟷_ 0ᴹ (mapⱽ₂ _∙_)
mapⱽ-zero = mapⱽ-zeroˡ , mapⱽ-zeroʳ

import Algebra.Structures as S

module MonoidSemiringProperties {M : Set ℓ} {_∙_ : Op₂ M} {ε : M}
                                (isMonoid-M : S.IsMonoid _≡_ _∙_ ε) where
  open S.IsMonoid isMonoid-M

  open import Algebra.Structures {suc ℓ} {ℓ} {Pred M} _⟷_

  open MonoidOps _∙_ ε

  ⋆-cong : P ⟷ R → Q ⟷ S → P ⋆ Q ⟷ R ⋆ S
  ⋆-cong = mapⱽ₂-congˡ

  ⋆-congˡ : Q ⟷ S → P ⋆ Q ⟷ P ⋆ S
  ⋆-congˡ {P = P} = ⋆-cong (⟷Eq.refl {x = P})

  ⋆-congʳ : P ⟷ R → P ⋆ Q ⟷ R ⋆ Q
  ⋆-congʳ {Q = Q} = flip ⋆-cong (⟷Eq.refl {x = Q})

  -- ⋆-cong {P}{R}{Q}{S} P⟷R Q⟷S {w} =
  --   begin
  --     (∃ λ (p , q) → w ≡ p ∙ q × P p × Q q)
  --   ≈⟨ ∃-cong (↦-congˡ (*-cong P⟷R Q⟷S)) ⟩
  --     (∃ λ (r , s) → w ≡ r ∙ s × R r × S s)
  --   ∎
  --  where open ↔R
  --  -- TODO: try again without w

  open import Data.List
  open import Data.List.Relation.Unary.All

  ☆-star : P ☆ ⟷ 𝟏 ∪ P ⋆ P ☆
  ☆-star {w = w} = mk↔′
    (λ { ([] , refl≡ , []) → inj₁ refl≡
       ; (p ∷ ps , refl≡ , Pp ∷ Pps) → inj₂ ((p , foldr _∙_ ε ps) , refl≡ , Pp , ps , refl≡ , Pps) })
    (λ { (inj₁ refl≡) → [] , refl≡ , []
       ; (inj₂ ((p , .(foldr _∙_ ε ps)) , refl≡ , Pp , ps , refl≡ , Pps)) → p ∷ ps , refl≡ , Pp ∷ Pps})
    (λ { (inj₁ refl≡) → refl≡
       ; (inj₂ ((p , .(foldr _∙_ ε ps)) , refl≡ , Pp , ps , refl≡ , Pps)) → refl≡ })
    (λ { ([] , refl≡ , []) → refl≡
       ; (p ∷ ps , refl≡ , Pp ∷ Pps) → refl≡ })

  ✪↔☆ : P ✪ ⟷ P ☆
  ✪↔☆ {P = P} = mk↔′ f f⁻¹ invˡ invʳ
   where
     f : ∀ {w} → (P ✪) w → (P ☆) w
     f zero✪ = [] , refl≡ , []
     f (suc✪ ((u , v) , refl≡ , Pu , P✪v)) with f P✪v
     ... | us , refl≡ , Pus = u ∷ us , refl≡ , Pu ∷ Pus

     f⁻¹ : ∀ {w} → (P ☆) w → (P ✪) w
     f⁻¹ ([] , refl≡ , []) = zero✪
     f⁻¹ (u ∷ us , refl≡ , Pu ∷ Pus) =
       suc✪ ((u , foldr _∙_ ε us) , refl≡ , Pu , f⁻¹ (us , refl≡ , Pus))

     invˡ : ∀ {w} (z : (P ☆) w) → f (f⁻¹ z) ≡ z
     invˡ ([] , refl≡ , []) = refl≡
     invˡ (u ∷ us , refl≡ , Pu ∷ Pus) rewrite invˡ (us , refl≡ , Pus) = refl≡

     invʳ : ∀ {w} (z : (P ✪) w) → f⁻¹ (f z) ≡ z
     invʳ zero✪ = refl≡
     invʳ (suc✪ ((u , v) , refl≡ , Pu , P✪v)) with f P✪v | invʳ P✪v
     ... | us , refl≡ , Pus | refl≡ = refl≡

{-

  -- Miscellaneous other properties

  ↦-homo-ε : (ε ↦ ⊤) ⟷ 𝟏
  ↦-homo-ε = *-identityʳ _

  -- ↦-homo-ε {w} =
  --   begin
  --     (ε ↦ ⊤) w
  --   ≡⟨⟩
  --     (w ≡ ε × ⊤)
  --   ≈⟨ *-identityʳ _ ⟩
  --     w ≡ ε
  --   ≡⟨⟩
  --     𝟏 w
  --   ∎
  --  where open ↔R
  --        -- open Set-CommutativeSemiring

  ↦-homo-⋆ : ∀ {a b p q} → (a ∙ b ↦ p * q) ⟷ (a ↦ p) ⋆ (b ↦ q)
  ↦-homo-⋆ {a}{b}{p}{q} {w} =
    begin
      (a ∙ b ↦ p * q) w
    ≡⟨⟩
      (w ≡ a ∙ b × (p * q))
    ≈˘⟨ ∃≡² ⟩
      (∃ λ (u , v) → w ≡ u ∙ v × (u , v) ≡ (a , b) × (p × q))
    ≈˘⟨ ∃-cong (*-congˡ (*-congʳ ×-≡,≡↔≡)) ⟩
      (∃ λ (u , v) → w ≡ u ∙ v × (u ≡ a × v ≡ b) × (p × q))
    ≈⟨ ∃-cong (*-congˡ ×-transpose) ⟩
      (∃ λ (u , v) → w ≡ u ∙ v × (u ≡ a × p) × (v ≡ b × q))
    ≡⟨⟩
      (∃ λ (u , v) → w ≡ u ∙ v × (a ↦ p) u × (b ↦ q) v)
    ≡⟨⟩
      ((a ↦ p) ⋆ (b ↦ q)) w
    ∎
   where open ↔R

  -- TODO: Prove homomorphicity of ↦ compositionally from homomorphicity of
  -- pureⱽ and *ᵣ. If I can't, then at least prove pureⱽ-homo-⋆ via ↦-homo-⋆.

  ↦1# : (a ↦ 1#) ⟷ pureⱽ a
  ↦1# = *ᵣ-identityʳ (pureⱽ _)

  -- ↦1# {a = a} = let open ⟷R in
  --   begin
  --     (a ↦ 1#)
  --   ≡⟨⟩
  --     pureⱽ a *ᵣ 1#
  --   ≈⟨ *ᵣ-identityʳ (pureⱽ a) ⟩
  --     pureⱽ a
  --   ∎

  -- pureⱽ-homo-ε holds definitionally.
  pureⱽ-homo-ε : pureⱽ ε ⟷ 𝟏
  pureⱽ-homo-ε = ↔Eq.refl   -- ⟷Eq.refl {x = 𝟏}

  pureⱽ-homo-⋆ : pureⱽ (a ∙ b) ⟷ pureⱽ a ⋆ pureⱽ b
  pureⱽ-homo-⋆ {a}{b} = let open ⟷R in
    begin
      pureⱽ (a ∙ b)
    ≈˘⟨ ↦1# ⟩
      (a ∙ b ↦ 1#)
    ≈˘⟨ ↦-congˡ (*-identityʳ 1#) ⟩
      (a ∙ b ↦ 1# * 1#)
    ≈⟨ ↦-homo-⋆ ⟩
      (a ↦ 1#) ⋆ (b ↦ 1#)
    ≈⟨ ⋆-cong ↦1# ↦1# ⟩
      pureⱽ a ⋆ pureⱽ b
    ∎

  -- pureⱽ-homo-⋆ : pureⱽ (a ∙ b) ⟷ pureⱽ a ⋆ pureⱽ b
  -- pureⱽ-homo-⋆ {a}{b} {z} =
  --   begin
  --     z ≡ a ∙ b
  --   ≈˘⟨ ∃≡ʳ ⟩
  --     (∃ λ  (u , v) → z ≡ u ∙ v × (u , v) ≡ (a , b) )
  --   ≈˘⟨ ∃-cong (*-congˡ ×-≡,≡↔≡) ⟩
  --     (∃ λ  (u , v) → z ≡ u ∙ v × u ≡ a × v ≡ b )
  --   ∎
  --  where open ↔R
-}

\end{code}

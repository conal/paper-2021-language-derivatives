\begin{code}
-- {-# OPTIONS --safe #-}

module Language.Properties {ℓ} (A : Set ℓ) where

open import Algebra.Module.Bundles

open import Level

open import Data.Product
open import Data.Product.Algebra
open import Relation.Binary.PropositionalEquality
open import Function using (_↔_; mk↔′)
open import Data.List
open import Data.List.Properties

open import Misc {ℓ}
open import Language A
open import Inverses {ℓ}
open import Closed ; open Closed.Types {ℓ}
open import Algebra.Construct.Function

open import Algebra.Definitions {A = Lang} _⟷_

private
  variable
    P Q R S : Lang

-- (P ⋆ Q) pq = ∃⇃ λ (p ,  q) → (pq ≡ p ⊙ q) × P p × Q q

⋆-cong : P ⟷ R → Q ⟷ S → P ⋆ Q ⟷ R ⋆ S
⋆-cong PR QS = ∃-cong (×-congˡ (×-cong PR QS))

-- ⋆-cong {P}{R}{Q}{S} PR QS {pq} =
--   begin
--     (P ⋆ Q) pq
--   ≡⟨⟩
--     (∃⇃ λ (p ,  q) → (pq ≡ p ⊙ q) × P p × Q q)
--   ≈⟨ ∃-cong (×-congˡ (×-cong PR QS)) ⟩
--     (∃⇃ λ (r ,  s) → (rs ≡ r ⊙ s) × R r × S s)
--   ≡⟨⟩
--     (R ⋆ S) pq
--   ∎
--  pqhere open ↔R

-- ⋆-assoc : Associative _⋆_
-- ⋆-assoc P Q R {pqr} =
--   begin
--     ((P ⋆ Q) ⋆ R) pqr
--   ≡⟨⟩
--     (∃⇃ λ (pq ,  r) → (pqr ≡ pq ⊙ r) × (P ⋆ Q) pq × R r)
--   ≈⟨ {!!} ⟩
--     (P ⋆ (Q ⋆ R)) pqr
--   ∎ where open ↔R

-- ⋆-assoc : Associative _⋆_
-- ⋆-assoc P Q R {pqr} = mk↔′

--   (λ { ((.(p ⊙ q) , r) , refl , ((p , q) , refl , Pp , Qq) , Rr)
--      → (p , q ⊙ r) , ++-assoc p q r , Pp , (q , r) , refl , Qq , Rr })

--   (λ { ((p , .(q ⊙ r)) , refl , Pp , (q , r) , refl , Qq , Rr)
--      → (p ⊙ q , r) , sym (++-assoc p q r) , ((p , q) , refl , Pp , Qq) , Rr })

--   (λ { ((p , .(q ⊙ r)) , refl , Pp , (q , r) , refl , Qq , Rr)
--      → {!!} })

--   (λ { ((.(p ⊙ q) , r) , refl , ((p , q) , refl , Pp , Qq) , Rr)
--      → {!!} })


-- ⋆-assoc : Associative _⋆_
-- ⋆-assoc P Q R {pqr} = mk↔′ f f⁻¹ {!!} {!!}
--                       -- mk↔′ f f⁻¹ f∘f⁻¹ f⁻¹∘f
--  where
--    f : ((P ⋆ Q) ⋆ R) pqr → (P ⋆ (Q ⋆ R)) pqr
--    f ((.(p ⊙ q) , r) , refl , ((p , q) , refl , Pp , Qq) , Rr) =
--       (p , q ⊙ r) , ++-assoc p q r , Pp , (q , r) , refl , Qq , Rr

--    f⁻¹ : (P ⋆ (Q ⋆ R)) pqr → ((P ⋆ Q) ⋆ R) pqr
--    f⁻¹ ((p , .(q ⊙ r)) , refl , Pp , (q , r) , refl , Qq , Rr) =
--       (p ⊙ q , r) , sym (++-assoc p q r) , ((p , q) , refl , Pp , Qq) , Rr

   -- f∘f⁻¹ : ∀ z → f (f⁻¹ z) ≡ z
   -- -- f∘f⁻¹ ((p , .(q ⊙ r)) , refl , Pp , (q , r) , refl , Qq , Rr) rewrite ++-assoc p q r = {!!}


   -- f∘f⁻¹ : ∀ z → f (f⁻¹ z) ≡ z
   -- f∘f⁻¹ ((p , .(q ⊙ r)) , refl , Pp , (q , r) , refl , Qq , Rr) with ++-assoc p q r
   -- ... | x = {!!}

   -- f∘f⁻¹ = ?
   -- f⁻¹∘f = ?

   -- (λ { ((p , .(q ⊙ r)) , refl , Pp , (q , r) , refl , Qq , Rr)
   --    → {!!} })

   -- (λ { ((.(p ⊙ q) , r) , refl , ((p , q) , refl , Pp , Qq) , Rr)
   --    → {!!} })


-- trans-symˡ : ∀ {x y : A} (p : x ≡ y) → trans (sym p) p ≡ refl
-- trans-symʳ : ∀ {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl

⋆-identityˡ : LeftIdentity 𝟏 _⋆_
⋆-identityˡ Q {q} = mk↔′
  (λ { (([] , .q) , refl , refl , Qq) → Qq })
  (λ { Qq → ([] , q) , refl , refl , Qq })
  (λ { Qq → refl })
  (λ { (([] , .q) , refl , refl , Qq) → refl })

-- ⋆-identityʳ : RightIdentity 𝟏 _⋆_
-- ⋆-identityʳ P {p} = mk↔′

--   (λ { ((z , []) , refl , Pz , refl) → subst P (sym (++-identityʳ z)) Pz })

--   (λ { Pp → (p , []) , sym (++-identityʳ p) , Pp , refl })
  
--   (λ Pp → {!refl!})

--   (λ { ((z , []) , refl , Pz , refl) → {!refl!} })

-- ⋆-identityʳ : RightIdentity 𝟏 _⋆_
-- ⋆-identityʳ P {pq} =
--   begin
--     (P ⋆ 𝟏) pq
--   ≡⟨⟩
--     (∃⇃ λ (p ,  q) → (pq ≡ p ⊙ q) × P p × 𝟏 q)
--   ≡⟨⟩
--     (∃⇃ λ (p ,  q) → (pq ≡ p ⊙ q) × P p × q ≡ [])
--   ≈⟨ {!!} ⟩
--     P pq
--   ∎ where open ↔R

-- (P ⋆ Q) pq = ∃⇃ λ (p ,  q) → (pq ≡ p ⊙ q) × P p × Q q


postulate

  -- ⋆-assoc : Associative _⋆_
  -- ⋆-identity : Identity 𝟏 _⋆_
  ⋆-distrib : _⋆_ DistributesOver _∪_
  ⋆-zero : Zero ∅ _⋆_

open import Data.Product.Algebra

-- Predicates as semimodule
Pred-Semimodule : Set ℓ → Semimodule (×-⊎-commutativeSemiring ℓ) _ _
Pred-Semimodule A = semimodule A

module Pred-Semimodule {A} = Semimodule (Pred-Semimodule A)
open Pred-Semimodule

\end{code}

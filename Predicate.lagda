\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Level

module Predicate {ℓ : Level} where

open import Algebra.Core
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Misc {ℓ}
\end{code}

%<*Pred>
\AgdaTarget{Pred}
\begin{code}[hide]
Pred : Set⇃ → Set⇃₁
\end{code}
\begin{code}
Pred A = A → Set⇃
\end{code}
%</Pred>

\begin{code}
private
  variable
    A B C D : Set⇃
    P Q R S : Pred A
\end{code}

Let's now generalize from predicates over lists (``languages'') to arbitrary predicates.

First, we can transform types (predicate codomains) covariantly, with convenient nullary, unary, and binary variants:
%<*codomain-transformers>
\AgdaTarget{pureᵀ, mapᵀ, mapᵀ₂}
\begin{code}
pureᵀ : Set⇃ → Pred A
pureᵀ ∙ a = ∙

mapᵀ : (Set⇃ → Set⇃) → (Pred A → Pred A)
mapᵀ ∙_ P a = ∙ P a

mapᵀ₂ :  (Set⇃ → Set⇃ → Set⇃) →
         (Pred A  → Pred A  → Pred A)
mapᵀ₂ _∙_ P Q a = P a ∙ Q a
\end{code}
%</codomain-transformers>
With these generalizations, we can easily define union and intersection with their identities (the empty and universal predicates), as well as complement:\footnote{All of these operations are standard \stdlibCite{Relation.Unary}.}
%% \AgdaTarget{\_∪\_, ∪, ∅, \_∩\_, ∩, 𝒰, ∁}
\begin{code}[hide]
infixr 6 _∪_
infixr 7 _∩_
infixr 7 _·_

∅ : Pred A
𝒰 : Pred A
_∪_ : Op₂ (Pred A)
_∩_ : Op₂ (Pred A)
_·_ : Set⇃ → Op₁ (Pred A)
∁ : Op₁ (Pred A)
\end{code}
%<*codomain-ops>
\begin{code}
∅      = pureᵀ ⊥
𝒰      = pureᵀ ⊤
_∪_    = mapᵀ₂ _⊎_
_∩_    = mapᵀ₂ _×_
_·_ s  = mapᵀ (s ×_)
∁      = mapᵀ ¬_
\end{code}
%</codomain-ops>

Next, transform \emph{values} (predicate domains) covariantly:\footnote{Predicate product (\AF{\_⟨×⟩\_}) is standard \stdlibCite{Relation.Unary}.}\notefoot{I think I'll have to rework the \AF{mapⱽ} definition when I generalize from types to other (semi)rings.}
%<*domain-transformers>
\AgdaTarget{pureⱽ, mapⱽ, mapⱽ₂}
\begin{code}
pureⱽ : A → Pred A
pureⱽ x a = a ≡ x

mapⱽ : (A → B) → (Pred A → Pred B)
mapⱽ g P b = ∃ λ a → b ≡ g a × P a

mapⱽ₂ :  (A → B → C) →
         (Pred  A → Pred  B → Pred  C)
mapⱽ₂ g P Q c = ∃⇃ λ (a , b) → c ≡ g a b × P a × Q b
\end{code}
\begin{code}[hide]
-- Alternatively

infixr  2 _⟨×⟩_
_⟨×⟩_ : Pred A → Pred B → Pred (A × B)
(P ⟨×⟩ Q) (a , b) = P a × Q b

mapⱽ₂′ : (A → B → C) → (Pred A → Pred B → Pred C)
mapⱽ₂′ g P Q = mapⱽ (uncurry g) (P ⟨×⟩ Q)
\end{code}
%</domain-transformers>
Note that {\AF{mapⱽ} \AB{g} \AB{P}} is the image of the subset \AB{P} under the function \AB{g}.

These domain transformations generalize concatenation and its identity to arbitrary binary operations or even operations of any arity.
Rather than specialize all the way back to lists at this point, it will be useful to generalize to a binary operation \AB{\_∙\_} and an element \AB{ε}, which will form a monoid:
% \AgdaTarget{MonoidOps, 𝟏, _⋆_, ⋆, \_☆, ☆, zero☆, suc☆}
\begin{code}[hide]
module MonoidOps {M : Set⇃} (_∙_ : Op₂ M) (ε : M) where
  𝟏 : Pred M
  infixl 7 _⋆_
  _⋆_ : Op₂ (Pred M)
  infixl 10 _☆

  data _☆ (P : Pred M) : Pred M

  data _☆ʳ (P : Pred M) : Pred M

\end{code}
%<*domain-ops>
\begin{code}
  𝟏 = pureⱽ ε

  _⋆_ = mapⱽ₂ _∙_

  data _☆ P where
    zero☆  : (P ☆) ε
    suc☆   : ∀ {w} → (P ⋆ P ☆) w → (P ☆) w
\end{code}
%</domain-ops>
\begin{code}
  data _☆ʳ P where
    zero☆ʳ  : (P ☆ʳ) ε
    suc☆ʳ   : ∀ {w} → (P ☆ʳ ⋆ P) w → (P ☆ʳ) w
\end{code}

Further specialize to lists:
\begin{code}[hide]
module ListOps (A : Set⇃) where
  open import Data.List
  open MonoidOps {M = A ✶} _⊙_ [] public

  Lang : Set⇃₁
\end{code}
%<*Lang>
\begin{code}
  Lang = Pred (A ✶)
\end{code}
%</Lang>
\begin{code}
  ` : A → Lang
\end{code}
%<*list-ops>
\begin{code}
  ` c = pureⱽ [ c ]
\end{code}
%</list-ops>

\note{Experiment}
\begin{code}
module AltStar {M : Set⇃} (_∙_ : Op₂ M) (ε : M) where
  open import Data.List
  open import Data.List.Relation.Unary.All

  infixl 10 _✪
  _✪ : Op₁ (Pred M)
  (P ✪) w = ∃ λ ps → w ≡ foldr _∙_ ε ps × All P ps
  
\end{code}

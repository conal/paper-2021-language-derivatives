\begin{code}
{-# OPTIONS --safe #-}

open import Level

module Predicate {ℓ : Level} where

open import Algebra.Core
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Misc {ℓ}
\end{code}

%<*Pred>
\AgdaTarget{Pred}
\begin{code}[hide]
Pred : Set ℓ → Set (suc ℓ)
\end{code}
\begin{code}
Pred A = A → Set ℓ
\end{code}
%</Pred>

%<*Lang>
\begin{code}[hide]
module LangAsPred (A : Set ℓ) where
  Lang : Set (suc ℓ)
\end{code}
\begin{code}
  Lang = Pred (A ✶)
\end{code}
%</Lang>


\begin{code}
private
  variable
    A B C D : Set ℓ
    P Q R S : Pred A
\end{code}

Let's now generalize from predicates over lists (``languages'') to arbitrary predicates.

First, we can transform types (predicate codomains) covariantly, with convenient nullary, unary, and binary variants:
%<*codomain-transformers>
\AgdaTarget{pureᵀ, mapᵀ, mapᵀ₂}
\begin{code}
pureᵀ : Set ℓ → Pred A
pureᵀ ∙ a = ∙

mapᵀ : Op₁ (Set ℓ) → Op₁ (Pred A)
mapᵀ ∙_ P a = ∙ P a

mapᵀ₂ : Op₂ (Set ℓ) → Op₂ (Pred A)
mapᵀ₂ _∙_ P Q a = P a ∙ Q a
\end{code}
%</codomain-transformers>
With these generalizations, we can easily define union and intersection with their identities (the empty and universal predicates), as well as complement:\footnote{All of these operations are standard \stdlibCite{Relation.Unary}.}
%% \AgdaTarget{\_∪\_, ∪, ∅, \_∩\_, ∩, 𝒰, ∁}
\begin{code}[hide]
module SetOps where
  infixr 6 _∪_
  infixr 7 _∩_

  ∅ : Pred A
  𝒰 : Pred A
  _∪_ : Op₂ (Pred A)
  _∩_ : Op₂ (Pred A)
  ∁ : Op₁ (Pred A)
\end{code}
%<*codomain-ops>
\begin{code}
  ∅    = pureᵀ ⊥
  𝒰    = pureᵀ ⊤
  _∪_  = mapᵀ₂ _⊎_
  _∩_  = mapᵀ₂ _×_
  ∁    = mapᵀ ¬_
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

mapⱽ₂ : (A → B → C) → (Pred A → Pred B → Pred C)
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
module MonoidOps {M : Set ℓ} (_∙_ : Op₂ M) (ε : M) where
  𝟏 : Pred M
  infixl 7 _⋆_
  _⋆_ : Op₂ (Pred M)
  infixl 10 _☆
\end{code}
%<*domain-ops>
\begin{code}
  𝟏 = pureⱽ ε

  _⋆_ = mapⱽ₂ _∙_

  data _☆ (P : Pred M) : Pred M where
    zero☆  : (P ☆) ε
    suc☆   : ∀ {w} → (P ⋆ P ☆) w → (P ☆) w
\end{code}
%</domain-ops>

Or specialize to lists:
\begin{code}[hide]
module ListOps (A : Set ℓ) where
  open import Data.List

  𝟏 : Pred (A ✶)
  infixl 7 _⋆_
  _⋆_ : Op₂ (Pred (A ✶))
  infixl 10 _☆
\end{code}
%<*list-ops>
\begin{code}
  𝟏 = pureⱽ []

  _⋆_ = mapⱽ₂ _⊙_

  data _☆ (P : Pred (A ✶)) : Pred (A ✶) where
    zero☆  : (P ☆) []
    suc☆   : ∀ {w} → (P ⋆ P ☆) w → (P ☆) w
\end{code}
%</list-ops>

\begin{code}
{-# OPTIONS --safe --without-K #-}

module Language {ℓ} (A : Set ℓ) where

open import Level

open import Algebra.Core
-- open import Data.Empty
-- open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Misc {ℓ}

Lang : Set (suc ℓ)
∅ : Lang
𝒰 : Lang
_∪_ : Op₂ Lang
_∩_ : Op₂ Lang
_·_ : Set ℓ → Op₁ Lang
𝟏 : Lang
_⋆_ : Op₂ Lang
_✪ : Op₁ Lang
` : A → Lang

infixr 6 _∪_
infixr 6 _∩_
infixl 7 _·_
infixl 7 _⋆_
infixl 10 _✪
\end{code}

%<*Lang-ops>
{
\begin{center}
\mathindent-20ex
\begin{code}
Lang = A ✶ → Set ℓ
\end{code}
\end{center}
\ifacm\else
\vspace{-3ex}
\fi
\mathindent0ex
\hfill
\begin{minipage}[t]{20ex}
\begin{code}
∅ w = ⊥

𝒰 w = ⊤

𝟏 w = w ≡ []

` c w = w ≡ [ c ]

(s · P) w = s × P w
\end{code}
\end{minipage}
\hfill
\begin{minipage}[t]{48ex}
\begin{code}
(P ∪ Q) w = P w ⊎ Q w

(P ∩ Q) w = P w × Q w

(P ⋆ Q) w = ∃⇃ λ (u ,  v) → (w ≡ u ⊙ v) × P u × Q v

(P ✪) w = ∃ λ ws → (w ≡ concat ws) × All P ws
\end{code}
\end{minipage}
\hfill\;
}
%</Lang-ops>

\begin{code}
module AltStar where
  infixl 10 _☆
  data _☆ (P : Lang) : Lang where
    zero☆  : (P ☆) []
    suc☆   : ∀ {w} → (P ⋆ P ☆) w → (P ☆) w
\end{code}

\begin{code}
module Stuff where
  private variable B X : Set ℓ
\end{code}

%<*foldr-concat>
\begin{minipage}{16em}
\begin{code}
  concat⇂ : (A ✶) ✶ → A ✶
  concat⇂ = foldr _⊙_ []
\end{code}
\end{minipage}
%% where\hspace{3em}
\begin{minipage}{18em}
\begin{code}
  foldr⇂ : (B → X → X) → X → B ✶ → X
  foldr⇂ h x []        = x
  foldr⇂ h x (b ∷ bs)  = h b (foldr⇂ h x bs)
\end{code}
\end{minipage}
%</foldr-concat>

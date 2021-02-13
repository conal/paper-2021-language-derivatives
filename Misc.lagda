\begin{code}
{-# OPTIONS --safe #-}

module Misc where

\end{code}

\subsection{Lists}

For succinctness and consistency with algebraically related notions, use star for list types.
So that I can tweak the typesetting, rename append.

\begin{code}
open import Data.List

infixl 10 _✶
_✶ : Set → Set
_✶ = List

infixr 5 _⊙_
_⊙_ : ∀ {A} → A ✶ → A ✶ → A ✶
_⊙_ = _++_
\end{code}

\subsection{Functions}

\begin{code}
open import Data.Product
private variable A B : Set
\end{code}

Agda doesn't like ``∃ λ (a , b) → ...'', maybe because it can't sort out how \AB{b} could depends on \AB{a}.
I'd like to find a better solution.
\begin{code}
∃⇃ : (A × B → Set) → Set
∃⇃ = ∃
\end{code}

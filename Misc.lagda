\begin{code}
{-# OPTIONS --safe --without-K #-}

open import Level

module Misc {ℓ : Level} where

\end{code}

\subsection{Types}

I may want to say just ``\APT{Set}'' to mean ``{\APT Set \AB{ℓ}}'' in the slides and/or paper, but I really still want level polymorphism.
\begin{code}
Set⇃ = Set ℓ

Set⇃₁ = Set (suc ℓ)
\end{code}

\subsection{̄{⊥ and ⊤}

Make ⊥ and ⊤ level-monomorphic to simplify signatures elsewhere.
Doing so loses some generality, but that generality is already lost in equational reasoning on types.

\begin{code}
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥′)
open import Data.Empty.Polymorphic using (⊥-elim) public
open import Data.Unit.Polymorphic  using () renaming (⊤ to ⊤′)

⊥ : Set ℓ
⊥ = ⊥′

⊤ : Set ℓ
⊤ = ⊤′

import Data.Unit
pattern tt = lift Data.Unit.tt

infix 3 ¬_
¬_ : Set ℓ → Set ℓ
¬ X = X → ⊥

open import Data.Unit  using () renaming (tt to tt⇂) public
open import Data.Empty using () renaming (⊥-elim to ⊥-elim⇂) public
\end{code}

\subsection{Lists}

For succinctness and consistency with algebraically related notions, use star for list types.
So that I can tweak the typesetting, rename append.

\begin{code}
open import Data.List

infixl 10 _✶
_✶ : Set ℓ → Set ℓ
_✶ = List

infixr 5 _⊙_
_⊙_ : ∀ {A} → A ✶ → A ✶ → A ✶
_⊙_ = _++_
\end{code}

\subsection{Functions}

\begin{code}
open import Data.Product

uncurry₃ˡ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
            {D : Σ (Σ A B) (uncurry C) → Set d} →
            ((x : A) → (y : B x) → (z : C x y) → D ((x , y) , z)) →
            ((p : _) → D p)
uncurry₃ˡ f ((x , y) , z) = f x y z

\end{code}

\begin{code}
open import Data.Product
private variable A B : Set ℓ
\end{code}

Agda doesn't like ``∃ λ (a , b) → ...'', maybe because it can't sort out how \AB{b} could depends on \AB{a}.
I'd like to find a better solution.
\begin{code}
∃⇃ : (A × B → Set ℓ) → Set ℓ
∃⇃ = ∃
\end{code}

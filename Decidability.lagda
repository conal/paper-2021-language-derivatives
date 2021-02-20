%% \section{Decidability}

\begin{code}[hide]
{-# OPTIONS --safe #-}

open import Level

module Decidability {ℓ : Level} where

open import Function using (_∘_; _↔_; Inverse)
open import Data.List using ([])

open import Misc {ℓ}
open import Inverses {ℓ}

private
  variable
    A B : Set ℓ
    P Q : A → Set ℓ
\end{code}

%<*Dec>
\AgdaTarget{Dec; yes; no}
\begin{code}
data Dec (A : Set ℓ) : Set ℓ where
  yes  :     A → Dec A
  no   : ¬   A → Dec A
\end{code}%
%</Dec>

%<*¬>
\begin{code}[hide]
private
  module Stuff where
    ¬⇃_ : Set ℓ → Set ℓ
\end{code}
\begin{code}[inline]
    ¬⇃ A = A → ⊥
\end{code}
%</¬>

%<*Decidable>
\AgdaTarget{Decidable}
\begin{code}[hide]
Decidable : (A → Set ℓ) → Set ℓ
\end{code}
\begin{code}
Decidable P = ∀ x → Dec (P x)
\end{code}
%</Decidable>

\AgdaTarget{Decidable₂}
\begin{code}
Decidable₂ : (A → B → Set ℓ) → Set ℓ
Decidable₂ _∼_ = ∀ a b → Dec (a ∼ b)
\end{code}

%<*isomorphisms>
\begin{code}[hide]
open import Function.Equality using (Π) ; open Π
open import Function.Equivalence using (Equivalence; equivalence; _⇔_)

map′ : (A → B) → (B → A) → Dec A → Dec B
map′ A→B B→A (yes a) = yes (A→B a)
map′ A→B B→A (no ¬a) = no (¬a ∘ B→A)

map‽⇔ : A ⇔ B → Dec A → Dec B
map‽⇔ A⇔B = map′ (to ⟨$⟩_) (from ⟨$⟩_) where open Equivalence A⇔B
\end{code}
\AgdaTarget{\_▹\_, \_◃\_}
\begin{code}[hide]
infixr 9 _▹_
infixr 9 _◃_
infixr 9 _▸_
infixr 9 _◂_

_▹_ : A ↔ B → Dec A → Dec B
f ▹ a? = map‽⇔ (↔→⇔ f) a?

_▸_ : (P ⟷ Q) → Decidable P → Decidable Q
(f ▸ p?) w = f ▹ p? w
\end{code}
\begin{code}
_◃_ : B ↔ A → Dec A → Dec B

_◂_ : Q ⟷ P → Decidable P → Decidable Q
\end{code}
\begin{code}[hide]
g ◃ a? = ↔Eq.sym g ▹ a?

(g ◂ p?) w = g ◃ p? w
\end{code}
%</isomorphisms>

%<*compositional-dec>
{\mathindent0ex
\begin{code}[hide]
open import Data.Sum
open import Data.Product
open import Function using (id; _∘_)

infixr 1 _⊎‽_
infixr 2 _×‽_
\end{code}
\hfill\;
\begin{minipage}{37ex}
\begin{code}
⊥‽  : Dec ⊥
⊥‽  = no (λ ())


_⊎‽_  : Dec A → Dec B → Dec (A ⊎ B)
no ¬a  ⊎‽ no ¬b  = no [ ¬a , ¬b ]
yes a  ⊎‽ no ¬b  = yes (inj₁ a)
_      ⊎‽ yes b  = yes (inj₂ b)
\end{code}
\end{minipage}
\hfill
\begin{minipage}{37ex}
\begin{code}
⊤‽  : Dec ⊤
⊤‽  = yes tt


_×‽_  : Dec A → Dec B → Dec (A × B)
yes a  ×‽ yes b  = yes (a , b)
no ¬a  ×‽ yes b  = no (¬a ∘ proj₁)
_      ×‽ no ¬b  = no (¬b ∘ proj₂)
\end{code}
\end{minipage}
\hfill\;
\begin{code}[hide]
¬‽_   : Dec A → Dec (¬ A)
¬‽ yes a  = no  λ ¬a  → ¬a a
¬‽ no ¬a  = yes λ  a  → ¬a a
\end{code}
\begin{center}
\begin{code}
_✶‽ : Dec A → Dec (A ✶)
_ ✶‽ = yes []
\end{code}
\end{center}
}
%</compositional-dec>

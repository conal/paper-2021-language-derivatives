%% \section{Decidability}

\begin{code}[hide]
module Decidability where

open import Function using (_∘_; _↔_; Inverse)
open import Relation.Nullary using (¬_)
open import Data.List using ([])

open import Misc using (_✶)
open import Inverses

private
  variable
    X Y : Set
    P Q : X → Set
\end{code}

%<*Dec>
\AgdaTarget{Dec; yes; no}
\begin{code}
data Dec (X : Set) : Set where
  yes  :     X → Dec X
  no   : ¬   X → Dec X
\end{code}%
%</Dec>

%<*¬>
\begin{code}[hide]
private
  open import Data.Empty
  module Stuff where
    ¬⇃_ : Set → Set
\end{code}
\begin{code}[inline]
    ¬⇃ X = X → ⊥
\end{code}
%</¬>

%<*Decs>
\begin{code}[hide]
open import Algebra.Core

Dec¹ : Op₁ Set → Set₁
Dec² : Op₂ Set → Set₁
Decidable : (X → Set) → Set
Decidable₂ : (X → Y → Set) → Set
\end{code}
\AgdaTarget{Dec¹, Dec², Decidable, Decidable₂}
\begin{code}
Dec¹ ∙_ = ∀ {X} → Dec X → Dec (∙ X)

Dec² _∙_ = ∀ {X Y} → Dec X → Dec Y → Dec (X ∙ Y)

Decidable P = ∀ w → Dec (P w)
\end{code}
\begin{code}[hide]
Decidable₂ _∼_ = ∀ a b → Dec (a ∼ b)
\end{code}
%</Decs>

%<*isomorphisms>
\begin{code}[hide]
open import Function.Equality using (Π) ; open Π
open import Function.Equivalence using (Equivalence; equivalence; _⇔_)

map′ : (X → Y) → (Y → X) → Dec X → Dec Y
map′ X→Y Y→X (yes a) = yes (X→Y a)
map′ X→Y Y→X (no ¬a) = no (¬a ∘ Y→X)

map‽⇔ : X ⇔ Y → Dec X → Dec Y
map‽⇔ X⇔Y = map′ (to ⟨$⟩_) (from ⟨$⟩_) where open Equivalence X⇔Y

↔→⇔ : (X ↔ Y) → (X ⇔ Y)
↔→⇔ X↔Y = equivalence f f⁻¹ where open Inverse X↔Y
\end{code}
\AgdaTarget{\_▹\_, \_◃\_}
\begin{code}[hide]
infixr 9 _▹_
infixr 9 _◃_
infixr 9 _▸_
infixr 9 _◂_

_▹_ : X ↔ Y → Dec X → Dec Y
f ▹ a? = map‽⇔ (↔→⇔ f) a?

_▸_ : (P ⟷ Q) → Decidable P → Decidable Q
(f ▸ p?) w = f ▹ p? w
\end{code}
\begin{code}
_◃_ : Y ↔ X → Dec X → Dec Y
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
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function using (id; _∘_)

infixr 1 _⊎‽_
infixr 2 _×‽_
\end{code}
\hfill\;
\begin{minipage}{33ex}
\begin{code}
⊥‽  : Dec ⊥
⊥‽  = no (λ ())


_⊎‽_  : Dec² _⊎_
no ¬a  ⊎‽ no ¬b  = no [ ¬a , ¬b ]
yes a  ⊎‽ no ¬b  = yes (inj₁ a)
_      ⊎‽ yes b  = yes (inj₂ b)
\end{code}
\end{minipage}
\hfill
\begin{minipage}{33ex}
\begin{code}
⊤‽  : Dec ⊤
⊤‽  = yes tt


_×‽_  : Dec² _×_
yes a  ×‽ yes b  = yes (a , b)
no ¬a  ×‽ yes b  = no (¬a ∘ proj₁)
_      ×‽ no ¬b  = no (¬b ∘ proj₂)
\end{code}
%% -- no ¬a  ⊎‽ yes b  = yes (inj₂ b)
%% -- yes a  ⊎‽ _      = yes (inj₁ a)
%% -- yes a  ×‽ no ¬b  = no (¬b ∘ proj₂)
%% -- no ¬a  ×‽ _      = no (¬a ∘ proj₁)
\end{minipage}
\hfill\;
\begin{code}[hide]
¬‽_   : Dec¹ ¬_
¬‽ yes a  = no  λ ¬a  → ¬a a
¬‽ no ¬a  = yes λ  a  → ¬a a
\end{code}
\begin{center}
\begin{code}
_✶‽ : Dec¹ _✶
_ ✶‽ = yes []
\end{code}
\end{center}
}
%</compositional-dec>

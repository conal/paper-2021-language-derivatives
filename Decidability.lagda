%% \section{Decidability}

\begin{code}[hide]
module Decidability where

open import Function using (_∘_; _↔_; Inverse)
open import Relation.Nullary using (¬_)
open import Data.List using ([])

open import Misc using (_✶)
open import Inverses using (_⟷_; module ↔Eq)

private
  variable
    A B : Set
    P Q : A → Set
\end{code}

%<*Dec>
\begin{minipage}{2in}
\AgdaTarget{Dec; yes; no}
\begin{code}
data Dec (A : Set) : Set where
  yes  :     A → Dec A
  no   : ¬   A → Dec A
\end{code}%
\end{minipage}
\hfill
\begin{minipage}{2in}
\begin{code}[hide]
private
  open import Data.Empty
  module Stuff where
    ¬⇃_ : Set → Set
\end{code}
\vspace{6.3ex}
(\begin{code}[inline]
    ¬⇃ A = A → ⊥
\end{code})
\end{minipage}
%</Dec>

%<*Decs>
\begin{code}[hide]
open import Algebra.Core

Dec¹ : Op₁ Set → Set₁
Dec² : Op₂ Set → Set₁
Decidable : (A → Set) → Set
Decidable₂ : (A → B → Set) → Set
\end{code}
\AgdaTarget{Dec¹, Dec², Decidable, Decidable₂}
\begin{code}
Dec¹ ∙_ = ∀ {A} → Dec A → Dec (∙ A)

Dec² _∙_ = ∀ {A B} → Dec A → Dec B → Dec (A ∙ B)

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

map′ : (A → B) → (B → A) → Dec A → Dec B
map′ A→B B→A (yes a) = yes (A→B a)
map′ A→B B→A (no ¬a) = no (¬a ∘ B→A)

map‽⇔ : A ⇔ B → Dec A → Dec B
map‽⇔ A⇔B = map′ (to ⟨$⟩_) (from ⟨$⟩_) where open Equivalence A⇔B

↔→⇔ : (A ↔ B) → (A ⇔ B)
↔→⇔ A↔B = equivalence f f⁻¹ where open Inverse A↔B
\end{code}
\AgdaTarget{\_▹\_, \_◃\_}
\begin{code}[hide]
infixr 9 _▹_
infixr 9 _◃_
infixr 9 _▸_
infixr 9 _◂_

_▹_ : A ↔ B → Dec A → Dec B
f ▹ a? = map‽⇔ (↔→⇔ f) a?

_▸_ : P ⟷ Q → Decidable P → Decidable Q
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
\begin{code}[hide]
open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Function using (id; _∘_)

infixr 1 _⊎‽_
infixr 2 _×‽_
\end{code}
\begin{minipage}{2.75in}
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
\begin{minipage}{2.75in}
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
\hfill~
\begin{code}[hide]
¬‽_   : Dec¹ ¬_
¬‽ yes a  = no  λ ¬a  → ¬a a
¬‽ no ¬a  = yes λ  a  → ¬a a
\end{code}
\begin{center}
\begin{code}
_✶‽ : Dec A → Dec (A ✶)
_ ✶‽ = yes []
\end{code}
\end{center}
%</compositional-dec>

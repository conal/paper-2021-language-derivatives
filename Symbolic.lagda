\begin{code}[hide]

open import Relation.Binary.PropositionalEquality using (_≡_) ; open _≡_
open import Decidability hiding (_◂_)

module Symbolic {A : Set} (_≟_ : Decidable₂ {A = A} _≡_) where

open import Data.List using ([]; _∷_)

open import Inverses

module ◬ where
  open import Language A public
  open import Calculus A public

open ◬ using (ν⋆; δ⋆; ν☆; δ☆; ν𝟏; δ𝟏; ν`; δ`)

private
  variable
    P Q : ◬.Lang
    s : Set
\end{code}

%<*api>
{\mathindent0ex
\begin{center}
\begin{code}[hide]
infixr  6 _∪_
infixr  7 _∩_
infixl  7 _⋆_
infixr  7 _·_
infix   9 _◂_
infixl 10 _☆
\end{code}
\begin{code}
data Lang : ◬.Lang → Set₁ where
  ∅    : Lang  ◬.∅
  𝒰    : Lang  ◬.𝒰
  _∪_  : Lang  P  → Lang Q  → Lang (P  ◬.∪  Q)
  _∩_  : Lang  P  → Lang Q  → Lang (P  ◬.∩  Q)
  _·_  : Dec   s  → Lang P  → Lang (s  ◬.·  P)
  𝟏    : Lang (◬.𝟏)
  _⋆_  : Lang  P  → Lang Q  → Lang (P  ◬.⋆  Q)
  _☆   : Lang  P  → Lang (P ◬.☆)
  `    : (a : A) → Lang (◬.` a)
  _◂_  : (Q ⟷ P) → Lang P → Lang Q
\end{code}
%%   -- pureⱽ  : A ✴ → Lang 
\end{center}
\vspace{-5ex}
\hfill
\begin{minipage}[t]{33ex}
\begin{code}

ν  : Lang P → Dec (◬.ν P)
δ  : Lang P → (a : A) → Lang (◬.δ P a)
\end{code}
\end{minipage}
\hfill
\begin{minipage}[t]{25ex}
\begin{code}
⟦_⟧ : Lang P → Decidable P
⟦ p ⟧     []    = ν p
⟦ p ⟧ (a  ∷ w)  = ⟦ δ p a ⟧ w
\end{code}
\end{minipage}
\hfill\;
}
%</api>

%<*defs>
{\mathindent0ex
\begin{code}[hide]
private
  variable
    p : Lang P
    q : Lang Q

\end{code}
\setstretch{1.6}
\hfill
%\hspace{-1.2ex}%% To align with Automatic. Why different?
\begin{minipage}{30ex}
\begin{code}
ν ∅ = ⊥‽
ν 𝒰 = ⊤‽
ν (p ∪ q) = ν p ⊎‽ ν q
ν (p ∩ q) = ν p ×‽ ν q
ν (s · p) = s ×‽ ν p
ν 𝟏 = ν𝟏 ◃ ⊤‽
ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
ν (p ☆) = ν☆ ◃ (ν p ✶‽)
ν (` a) = ν` ◃ ⊥‽
ν (f ◂ p) = f ◃ ν p
\end{code}
\end{minipage}
\hfill
\begin{minipage}{38ex}
\begin{code}
δ ∅ a = ∅
δ 𝒰 a = 𝒰
δ (p ∪ q) a = δ p a ∪ δ q a
δ (p ∩ q) a = δ p a ∩ δ q a
δ (s · p) a = s · δ p a
δ 𝟏 a = δ𝟏 ◂ ∅
δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
δ (f ◂ p) a = f ◂ δ p a
\end{code}
\end{minipage}
\hfill\;
}
%</defs>

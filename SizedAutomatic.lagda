\begin{code}[hide]

open import Decidability hiding (_◂_)
open import Relation.Binary.PropositionalEquality using (_≡_) ; open _≡_

module SizedAutomatic {ℓ} {A : Set ℓ} (_≟_ : Decidable₂ {A = A} _≡_) where

open import Size
open import Data.List using ([]; _∷_)

open import Misc {ℓ}
open import Inverses {ℓ}

module ◬ where
  open import Language A public
  open import Calculus A public

open ◬ using (ν⋆; δ⋆; ν☆; δ☆; ν𝟏; δ𝟏; ν`; δ`)

private
  variable
    P Q : ◬.Lang
    s : Set ℓ
    i : Size
\end{code}

%<*api>
{\mathindent0ex
\hfill
\begin{minipage}[b]{52ex}
\begin{code}[hide]
infixr  6 _∪_
infixl  7 _∩_
infixl  7 _⋆_
infixr  7 _·_
infix   9 _◂_
infixl 10 _☆
\end{code}
\begin{code}
record Lang i (P : ◬.Lang) : Set⇃₁ where
  coinductive
  field
    ν : Dec (◬.ν P)
    δ : ∀ {j : Size< i} → (a : A) → Lang j (◬.δ P a)
\end{code}
\begin{code}[hide]
open Lang
\end{code}
\end{minipage}
\hfill
\begin{minipage}[b]{27ex}
\begin{code}
⟦_⟧ : Lang ∞ P → Decidable P
⟦ p ⟧     []    = ν p
⟦ p ⟧ (a  ∷ w)  = ⟦ δ p a ⟧ w
\end{code}
\end{minipage}
\hfill\;
\vspace{-3.5ex}
\begin{center}
\begin{code}
∅    : Lang i ◬.∅
𝒰    : Lang i ◬.𝒰
_∪_  : Lang i  P  → Lang i Q  → Lang i (P  ◬.∪  Q)
_∩_  : Lang i  P  → Lang i Q  → Lang i (P  ◬.∩  Q)
_·_  : Dec     s  → Lang i P  → Lang i (s  ◬.·  P)
𝟏    : Lang i (◬.𝟏)
_⋆_  : Lang i  P  → Lang i Q  → Lang i (P  ◬.⋆  Q)
_☆   : Lang i  P  → Lang i (P ◬.☆)
`    : (a : A) → Lang i (◬.` a)
_◂_  : (Q ⟷ P) → Lang i P → Lang i Q
\end{code}
\end{center}
}
%</api>

%<*defs>
{\mathindent0ex
\setstretch{1.6}
\rules{\begin{code}
ν ∅ = ⊥‽
\end{code}
}{\begin{code}
δ ∅ a = ∅
\end{code}}

\rules{\begin{code}
ν 𝒰 = ⊤‽
\end{code}
}{\begin{code}
δ 𝒰 a = 𝒰
\end{code}}

\rules{\begin{code}
ν (p ∪ q) = ν p ⊎‽ ν q
\end{code}
}{\begin{code}
δ (p ∪ q) a = δ p a ∪ δ q a
\end{code}}

\rules{\begin{code}
ν (p ∩ q) = ν p ×‽ ν q
\end{code}
}{\begin{code}
δ (p ∩ q) a = δ p a ∩ δ q a
\end{code}}

\rules{\begin{code}
ν (s · p) = s ×‽ ν p
\end{code}
}{\begin{code}
δ (s · p) a = s · δ p a
\end{code}}

\rules{\begin{code}
ν 𝟏 = ν𝟏 ◃ ⊤‽
\end{code}
}{\begin{code}
δ 𝟏 a = δ𝟏 ◂ ∅
\end{code}}

\rules{\begin{code}
ν (p ⋆ q) = ν⋆ ◃ (ν p ×‽ ν q)
\end{code}
}{\begin{code}
δ (p ⋆ q) a = δ⋆ ◂ (ν p · δ q a ∪ δ p a ⋆ q)
\end{code}}

\rules{\begin{code}
ν (p ☆) = ν☆ ◃ (ν p ✶‽)
\end{code}
}{\begin{code}
δ (p ☆) a = δ☆ ◂ (ν p ✶‽ · (δ p a ⋆ p ☆))
\end{code}}

\rules{\begin{code}
ν (` a) = ν` ◃ ⊥‽
\end{code}
}{\begin{code}
δ (` c) a = δ` ◂ ((a ≟ c) · 𝟏)
\end{code}}

\rules{\begin{code}
ν (f ◂ p) = f ◃ ν p
\end{code}
}{\begin{code}
δ (f ◂ p) a = f ◂ δ p a
\end{code}}
}
%</defs>

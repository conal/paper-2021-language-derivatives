\begin{code}[hide]
module Reflections {ℓ} (A : Set ℓ) where
\end{code}

\begin{comment}
\begin{frame}{Where are we?}
\begin{itemize}\itemsep3ex
\item Simple formulation of languages with membership proofs (parsings).
%% \item Algebraic properties from standard constructions.
\item Recursive decomposition lemmas.
\item Recursive decidability lemmas.
\end{itemize}
\vspace{4ex}
Next: Assemble lemmas into implementations.
\end{frame}
\end{comment}

\begin{code}[hide]
open import Level
open import Function using (_∘_;_↔_)
open import Relation.Binary.PropositionalEquality using (_≗_)
open import Data.Product using (_×_)
open import Data.List using (foldl)

open import Misc {ℓ}
open import Language A
open import Calculus A
open import Decidability {ℓ}
open import Inverses {ℓ}

private
  variable
    a : A
    b : Level
    B : Set b
    P Q : Lang

private
  module Stuff where
\end{code}

%<*summary-a>
\begin{code}
    ν⇂ : Lang → Set ℓ
    δ⇂ : Lang → A → Lang

    ν∘foldlδ⇂ : ν ∘ foldl δ P ≗ P
\end{code}
\begin{code}[hide]
    ν⇂ = ν⇃
    δ⇂ = δ⇃
    ν∘foldlδ⇂ = ν∘foldlδ
\end{code}
%</summary-a>

%<*summary-b>
\begin{code}
    ν⋆⇂  : ν (P ⋆ Q)    ↔  (ν P × ν Q)
    δ⋆⇂  : δ (P ⋆ Q) a  ⟷  ν P · δ Q a  ∪  δ P a ⋆ Q
    -- etc
\end{code}
\begin{code}[hide]
    ν⋆⇂ = ν⋆
    δ⋆⇂ = δ⋆
\end{code}
%</summary-b>

\sectionl{Star Semirings Structures}

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)
\end{code}


%<*closed>
\begin{code}
module Closed.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where
\end{code}
\begin{code}[hide]
open import Level
open import Algebra.Core
open import Algebra.Structures _≈_
\end{code}
\vspace{-5ex}
\AgdaTarget{Starˡ, IsClosedSemiring, starˡ, isSemiring}
\begin{code}
Starˡ : (_+_ _✲_ : Op₂ A) (𝟘 𝟙 : A) (_✯ : Op₁ A) → Set (a ⊔ ℓ)
Starˡ _+_ _✲_ 𝟘 𝟙 _✯ = ∀ {x} → (x ✯) ≈ (𝟙 + (x ✲ (x ✯)))

record IsClosedSemiring (_+_ _✲_ : Op₂ A) (𝟘 𝟙 : A) (_✯ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isSemiring : IsSemiring _+_ _✲_ 𝟘 𝟙
    starˡ : Starˡ _+_ _✲_ 𝟘 𝟙 _✯
\end{code}
%</closed>
\begin{code}[hide]
  open IsSemiring isSemiring public

record IsClosedCommutativeSemiring (_+_ _✲_ : Op₂ A) (𝟘 𝟙 : A) (_✯ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isCommutativeSemiring : IsCommutativeSemiring _+_ _✲_ 𝟘 𝟙
    starˡ : Starˡ _+_ _✲_ 𝟘 𝟙 _✯

  open IsCommutativeSemiring isCommutativeSemiring public
  
  isClosedSemiring : IsClosedSemiring _+_ _✲_ 𝟘 𝟙 _✯
  isClosedSemiring = record { isSemiring = isSemiring ; starˡ = starˡ }

\end{code}

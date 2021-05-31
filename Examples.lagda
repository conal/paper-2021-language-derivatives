\begin{code}
module Examples where

open import Data.Product
open import Data.Sum hiding ([_,_])
open import Data.Char
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.All

open import Language Char

-- pattern [_,_]     x y      =  x ∷ y ∷ []
-- pattern [_,_,_]   x y z    =  x ∷ y ∷ z ∷ []
-- pattern [_,_,_,_] x y z w  =  x ∷ y ∷ z ∷ w ∷ []

\end{code}

%<*examples>
\begin{center}
\begin{minipage}[t]{20ex}
\begin{code}
a∪b : Lang
a∪b = ` 'a' ∪ ` 'b'

a⋆b : Lang
a⋆b = ` 'a' ⋆ ` 'b'

a∪b☆ : Lang
a∪b☆ = a∪b ☆
\end{code}
\end{minipage}
\hspace{8ex}
\begin{minipage}[t]{40ex}
\begin{code}
_ : a∪b [ 'b' ]
_ = inj₂ refl

_ : a⋆b ('a' ∷ 'b' ∷ [])
_ = ([ 'a' ] , [ 'b' ]) , refl , refl , refl

_ : a∪b☆ ('a' ∷ 'b' ∷ 'a' ∷ [])
_ = [ 'a' ] ∷ [ 'b' ] ∷ [ 'a' ] ∷ []
  , refl
  , inj₁ refl ∷ inj₂ refl ∷ inj₁ refl ∷ []
\end{code}
\end{minipage}
\end{center}
%</examples>

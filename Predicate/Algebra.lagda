\sectionl{Predicate Algebra}

\begin{code}[hide]
{-# OPTIONS --safe #-}
-- {-# OPTIONS --without-K #-}

open import Level
open import Algebra.Core
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≗_; cong; subst) renaming (refl to refl≡; sym to sym≡)
import Algebra.Structures as S

module Predicate.Algebra {ℓ : Level} {M : Set ℓ} {_∙_ : Op₂ M} {ε : M}
                         (isMonoid-M : S.IsMonoid _≡_ _∙_ ε) where

private
  variable
    A B C : Set ℓ
\end{code}

\note{Consider postponing this entire section to better engage readers who are not into algebra for its own sake.}

The basic building blocks of predicates---and formal languages in particular---form the vocabulary of a \emph{closed semiring} in two different ways\out{, as reflected in the structure of regular expressions \needcite{}}.
The semiring abstraction has three aspects: (a) a commutative monoid providing ``zero'' and ``addition'', (b) a (possibly non-commutative) monoid providing ``one'' and ``multiplication'', and (c) the relationship between them, namely that multiplication distributes over addition and zero.\footnote{Distributing of multiplication over zero is also known as ``annihilation''.}
In the first predicate semiring, which is \emph{commutative} (i.e., multiplication commutes), zero and addition are \AF ∅ and \AF{\_∪\_}, while one and multiplication are \AF 𝒰 and \AF{\_∩\_}.

\begin{code}[hide]
open import Function using (mk↔′)
open import Algebra.Definitions
open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Data.Product.Algebra using (×-⊎-commutativeSemiring)

-- Local
open import Algebra.Construct.Function using (semimodule)
open import Inverses {ℓ}
open import Predicate {ℓ}

open S.IsMonoid isMonoid-M

open import Algebra.Structures {suc ℓ} {ℓ} {Pred M} _⟷_

open MonoidOps _∙_ ε

open import Predicate.Properties {ℓ}
open SetOps
open Pred-Semimodule

open MonoidSemiringProperties isMonoid-M

⋆-isMagma : IsMagma _⋆_
⋆-isMagma = record { isEquivalence = ⟷-isEquivalence ; ∙-cong = ⋆-cong }

⋆-isSemigroup : IsSemigroup _⋆_
⋆-isSemigroup = record { isMagma = ⋆-isMagma ; assoc = mapⱽ-assoc assoc }

⋆-isMonoid : IsMonoid _⋆_ 𝟏
⋆-isMonoid = record
  { isSemigroup = ⋆-isSemigroup
  ; identity = mapⱽ-identity identity
  }

⋆-∪-isSemiringWithoutAnnihilatingZero :
  IsSemiringWithoutAnnihilatingZero _∪_ _⋆_ ∅ 𝟏
⋆-∪-isSemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +ᴹ-isCommutativeMonoid {M}
  ; *-isMonoid = ⋆-isMonoid
  ; distrib = mapⱽ-distrib
  }

⋆-∪-isSemiring : IsSemiring _∪_ _⋆_ ∅ 𝟏
⋆-∪-isSemiring = record
  { isSemiringWithoutAnnihilatingZero = ⋆-∪-isSemiringWithoutAnnihilatingZero
  ; zero = mapⱽ-zero
  }

⋆-∪-isCommutativeSemiring :
  Commutative _≡_ _∙_ → IsCommutativeSemiring _∪_ _⋆_ ∅ 𝟏 
⋆-∪-isCommutativeSemiring ∙-comm = record
  { isSemiring = ⋆-∪-isSemiring
  ; *-comm = mapⱽ-comm ∙-comm
  }

-- TODO: consider parametrizing each algebraic structure by the corresponding
-- algebraic structure on M.
\end{code}

Closure adds the star operation.
Following existing conventions\out{ \stdlibCitep{Algebra.Structures}}, extend the semiring operations and laws with star and its law, parametrized over an arbitrary type \AB{A} and equivalence relation \AB{\_≈\_}:\notefoot{To do: add (right-associated) \AF{starʳ}.}
\ExecuteMetaData[Closed/Structures.tex]{closed}
The \AF{ClosedSemiring} algebraic structure is similarly extended to \AF{ClosedCommutativeSemiring}.

Conveniently, booleans and types form commutative semirings with all necessary definitions already in the standard library.
(The equivalence relation used for types is isomorphism rather than equality.)
Both are also closed.
For booleans, closure maps both \AIC{false} and \AIC{true} to \AIC{true}, with the \AF{starˡ} law holding definitionally.
For types, the closure of \AB{A} is {\AB{A} ✶} (the usual inductive list type) with a simple, non-inductive proof of \AF{starˡ}.

\begin{code}[hide]
open import Closed ; open Closed.Types {ℓ}
\end{code}

This first closed semiring for predicates follows from a much more general pattern.
Given any two types \AB{A} and \AB{B}, if \AB{B} is a monoid then {\AB A \AS → \AB B} is as well.
The monoid operation {\AB{\_∙\_} \AS : \AF{Op₂} \AB{B}} lifts to the function-level binary operation {\AS λ (\AB{f} \AB{g} : \AB{A} \AS → \AB{B}) \AS → \AS λ \AB a \AS → \AB f \AB a \AB ∙ \AB g \AB a}.
The monoid identity {\AB ε \AS : \AB{B}} lifts to the identity {\AS λ \AB a \AS → \AB ε}.
All of the laws transfer from \AB{B} to {\AB A \AS → \AB B}.
Likewise for other algebraic structures.

Looking more closely, additional algebraic structure emerges on predicates: (full) \emph{semimodules} generalize vector spaces by relaxing the associated types of ``scalars'' from fields to commutative semirings, i.e., dropping the requirements of multiplicative and additive inverses \needcite{}.
Left and right semimodules further generalize scalars to arbitrary semirings, dropping the commutativity requirement for scalar multiplication.
Again, nothing is needed from the codomain type \AB{B} beyond the properties of a semiring, so again predicates get these algebraic structures for free (already paid for by types).
For every {\AB{P} \AS : \AF{Pred} \AB{A}}, \AB{P} is a vector in the semimodule {\AF{Pred} \AB{A}}, including the special case of ``languages'', for which \AB{A} is a list type.
The dimension of the semimodule is the cardinality of the domain type \AB{A} (typically infinite), with ``basis vectors'' having the form {\AF{pureⱽ} \AB{a}} for {\AB{a} \AS : \AB{A}}.
A general vector (predicate) is a linear combination (often infinite) of these basis vectors, with addition being union and scaling conjoining membership proofs.

\begin{code}
⋆-∪-isClosedSemiring : IsClosedSemiring _⟷_ _∪_ _⋆_ ∅ 𝟏  _☆
⋆-∪-isClosedSemiring = record { isSemiring = ⋆-∪-isSemiring
                              ; starˡ = λ _ → ☆-starˡ }

⋆-∪-isClosedCommutativeSemiring :
  Commutative _≡_ _∙_ → IsClosedCommutativeSemiring _⟷_ _∪_ _⋆_ ∅ 𝟏 _☆
⋆-∪-isClosedCommutativeSemiring ∙-comm = record
  { isCommutativeSemiring = ⋆-∪-isCommutativeSemiring ∙-comm
  ; starˡ = λ _ → ☆-starˡ
  }

⋆-∪-ClosedSemiring : ClosedSemiring _ _
⋆-∪-ClosedSemiring = record { isClosedSemiring =  ⋆-∪-isClosedSemiring }

⋆-∪-ClosedCommutativeSemiring : Commutative _≡_ _∙_ → ClosedCommutativeSemiring _ _
⋆-∪-ClosedCommutativeSemiring ∙-comm =
  record { isClosedCommutativeSemiring = ⋆-∪-isClosedCommutativeSemiring ∙-comm }
\end{code}

There is still more algebraic structure to be found and exploited.
When our \AB{domain} type \AB{A} is a monoid (as with languages, infinite streams and grids, and functions of continuous space and time), predicates over \AB{A} form a second semiring, known as ``the monoid semiring'' \needcite{}, in which zero and addition are as in the first predicate commutative semiring and semimodule, while one and multiplication are \AF{𝟏} and \AF{\_⋆\_}, defined in \secref{Languages, Predicates, and Types}.
In this setting, language concatenation is subsumed by a very general form of \emph{convolution} \needcite{}.
The semimodule structure of predicates provides the additive aspect and is built entirely from the \emph{codomain}-transforming predicate operations defined in \secref{Languages, Predicates, and Types}.
The multiplicative aspect (convolution) comes entirely from the \emph{domain}-transforming operations, applied to any domain monoid.
The two needed distributive properties hold for \emph{any} domain-transforming operation, whether associative or not.
The proofs of these properties, while not terribly complex, are beyond the scope of this paper but are available in the paper's Agda source code.\notefoot{There will be short and long forms of this paper. Perhaps the long form will contain narrated parts of the monoid semiring proof.}

Not only do types form a closed semiring, the \emph{only} properties needed from types in the monoid semiring come from the laws of closed semirings.
We can thus apply the ideas in this paper to many other useful semirings as well, including natural numbers (e.g., number of parses), probability distributions, and the tropical semirings (max/plus and min/plus) for optimization.
\out{We will explore this generality in \secref{Beyond Predicates}.}
As a bonus, when the domain monoid commutes (multiplicatively)---e.g., for functions of space and time rather than languages---the monoid semiring does as well .

\note{I don't expect the semimodule and semiring stuff to be central to the paper, so postpone further discussion at least until after decidability and efficient computation.
Then point out that algebraic properties of tries and other language implementations are harder to prove than proving the same properties of functions (including predicates), and yet we can transfer the properties from functions to operationally motivated representations.}

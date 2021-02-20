\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Level

module Calculus {ℓ} (A : Set ℓ) where

-- open import Data.Empty
-- open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List
open import Function using (id; _∘_; _↔_; mk↔′)
open import Relation.Binary.PropositionalEquality

open import Misc {ℓ}
open import Inverses {ℓ}

-- open import Language A
open import Predicate ; open ListOps A

private
  variable
    a c : A
    s : Set ℓ
    b x : Level
    B : Set b
    X : Set x
    P Q : Lang

\end{code}

%<*νδ>
\AgdaTarget{ν, δ}
\begin{code}
ν : (A ✶ → B) → B              -- “nullable”
ν f = f []

δ : (A ✶ → B) → A → (A ✶ → B)  -- “derivative”
δ f a = f ∘ (a ∷_)
\end{code}
%% δ f a as = f (a ∷ as)
%</νδ>

%<*foldl>
\begin{code}[hide]
private
  module Stuff where
\end{code}
\begin{code}
    foldl⇃ : (X → A → X) → X → A ✶ → X
    foldl⇃ h x []        = x
    foldl⇃ h x (a ∷ as)  = foldl⇃ h (h x a) as
\end{code}
%</foldl>

%<*ν∘foldlδ>
\AgdaTarget{ν∘foldlδ}
%% ν∘foldlδ : ∀ w → P w ≡ ν (foldl δ P w)
\begin{code}
ν∘foldlδ : ν ∘ foldl δ P ≗ P
ν∘foldlδ []        = refl
ν∘foldlδ (a ∷ as)  = ν∘foldlδ as
\end{code}
%</ν∘foldlδ>

\begin{code}
open import Algebra.Core
private
  variable
    g : Op₁ (Set ℓ)
    h : Op₂ (Set ℓ)
\end{code}

%<*νδ-codomain>
{\mathindent0ex
\hfill
\begin{minipage}{18em}
\AgdaTarget{νpureᵀ, νmapᵀ, νmapᵀ₂}
\begin{code}
νpureᵀ  : ν (pureᵀ  s)      ≡ s
νmapᵀ   : ν (mapᵀ   g P)    ≡ g  (ν P)
νmapᵀ₂  : ν (mapᵀ₂  h P Q)  ≡ h  (ν P) (ν Q)
\end{code}
\end{minipage}
\hfill
\begin{minipage}{22em}
\AgdaTarget{δpureᵀ, δmapᵀ, δmapᵀ₂}
\begin{code}
δpureᵀ  : δ (pureᵀ  s)      a ≡ pureᵀ  s
δmapᵀ   : δ (mapᵀ   g P)    a ≡ mapᵀ   g (δ P a)
δmapᵀ₂  : δ (mapᵀ₂  h P Q)  a ≡ mapᵀ₂  h (δ P a) (δ Q a)
\end{code}
\end{minipage}
\hfill\;}
\begin{code}[hide]
νpureᵀ = refl
δpureᵀ = refl
νmapᵀ  = refl
δmapᵀ  = refl
νmapᵀ₂ = refl
δmapᵀ₂ = refl
\end{code}
%</νδ-codomain>

%<*νδ-lemmas>
{\mathindent0ex
\hfill
\setstretch{1.7}
\begin{minipage}{28ex}
\AgdaTarget{ν∅, ν∪, ν𝟏, ν⋆, ν☆, δ∅, δ∪, δ𝟏, δ⋆, δ☆}
\begin{code}
ν∅  : ν ∅ ≡ ⊥
ν𝒰  : ν 𝒰 ≡ ⊤
ν∪  : ν (P ∪ Q) ≡ (ν P ⊎ ν Q)
ν∩  : ν (P ∩ Q) ≡ (ν P × ν Q)
ν·  : ν (s · P) ≡ (s × ν P)
ν𝟏  : ν 𝟏 ↔ ⊤
ν⋆  : ν (P ⋆ Q) ↔ (ν P × ν Q)
ν☆  : ν (P ☆) ↔ (ν P) ✶
ν`  : ν (` c) ↔ ⊥
\end{code}
\end{minipage}
\hfill
\begin{minipage}{38ex}
\begin{code}
δ∅  : δ ∅ a ≡ ∅
δ𝒰  : δ 𝒰 a ≡ 𝒰
δ∪  : δ (P ∪ Q) a ≡ δ P a ∪ δ Q a
δ∩  : δ (P ∩ Q) a ≡ δ P a ∩ δ Q a
δ·  : δ (s · P) a ≡ s · δ P a
δ𝟏  : δ 𝟏 a ⟷ ∅
δ⋆  : δ (P ⋆ Q) a ⟷ ν P · δ Q a ∪ δ P a ⋆ Q
δ☆  : δ (P ☆) a ⟷ (ν P) ✶ · (δ P a ⋆ P ☆)
δ`  : δ (` c) a ⟷ (a ≡ c) · 𝟏
\end{code}
\end{minipage}
\hfill\;
}
%</νδ-lemmas>

\begin{code}[hide]

δ· = refl
δ∅ = refl
δ∩ = refl
δ∪ = refl
δ𝒰 = refl
ν· = refl
ν∅ = refl
ν∩ = refl
ν∪ = refl
ν𝒰 = refl

ν𝟏 = mk↔′
  (λ { refl → tt })
  (λ { tt → refl })
  (λ { tt → refl })
  (λ { refl → refl })

δ𝟏 = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

ν` = mk↔′ (λ ()) (λ ()) (λ ()) (λ ())

δ` = mk↔′
  (λ { refl → refl , refl })
  (λ { (refl , refl) → refl })
  (λ { (refl , refl) → refl })
  (λ { refl → refl })

ν⋆ = mk↔′
  (λ { (([] , []) , refl , νP , νQ) → νP , νQ })
  (λ { (νP , νQ) → ([] , []) , refl , νP , νQ })
  (λ { (νP , νQ) → refl } )
  (λ { (([] , []) , refl , νP , νQ) → refl})

δ⋆ {a = a} {w = w} = mk↔′
  (λ { (([] , .(a ∷ w)) , refl , νP , Qaw) → inj₁ (νP , Qaw)
     ; ((.a ∷ u , v) , refl , Pu , Qv) → inj₂ ((u , v) , refl , Pu , Qv) })
  (λ { (inj₁ (νP , Qaw)) → ([] , a ∷ w) , refl , νP , Qaw
     ; (inj₂ ((u , v) , refl , Pu , Qv)) → ((a ∷ u , v) , refl , Pu , Qv) })
  (λ { (inj₁ (νP , Qaw)) → refl
     ; (inj₂ ((u , v) , refl , Pu , Qv)) → refl })
  (λ { (([] , .(a ∷ w)) , refl , νP , Qaw) → refl
     ; ((.a ∷ u , v) , refl , Pu , Qv) → refl })

ν☆ {P = P} = mk↔′ f f⁻¹ invˡ invʳ
 where
   f : ν (P ☆) → (ν P) ✶
   f zero☆ = []
   f (suc☆ (([] , []) , refl , (νP , νP☆))) = νP ∷ f νP☆

   f⁻¹ : (ν P) ✶ → ν (P ☆)
   f⁻¹ [] = zero☆
   f⁻¹ (νP ∷ νP✶) = suc☆ (([] , []) , refl , (νP , f⁻¹ νP✶))

   invˡ : ∀ (νP✶ : (ν P) ✶) → f (f⁻¹ νP✶) ≡ νP✶
   invˡ [] = refl
   invˡ (νP ∷ νP✶) rewrite invˡ νP✶ = refl

   invʳ : ∀ (νP☆ : ν (P ☆)) → f⁻¹ (f νP☆) ≡ νP☆
   invʳ zero☆ = refl
   invʳ (suc☆ (([] , []) , refl , (νP , νP☆))) rewrite invʳ νP☆ = refl

δ☆ {P}{a} {w} = mk↔′ f f⁻¹ invˡ invʳ
 where
   f : δ (P ☆) a w → ((ν P) ✶ · (δ P a ⋆ P ☆)) w
   f (suc☆ (([] , .(a ∷ w)) , refl , (νP , P☆a∷w))) with f P☆a∷w
   ... |            νP✶  , etc
       = νP ∷ νP✶ , etc
   f (suc☆ ((.a ∷ u , v) , refl , (Pa∷u , P☆v))) = [] , (u , v) , refl , (Pa∷u , P☆v)

   f⁻¹ : ((ν P) ✶ · (δ P a ⋆ P ☆)) w → δ (P ☆) a w
   f⁻¹ ([] , (u , v) , refl , (Pa∷u , P☆v)) = (suc☆ ((a ∷ u , v) , refl , (Pa∷u , P☆v)))
   f⁻¹ (νP ∷ νP✶ , etc) = (suc☆ (([] , a ∷ w) , refl , (νP , f⁻¹ (νP✶ , etc))))

   invˡ : (s : ((ν P) ✶ · (δ P a ⋆ P ☆)) w) → f (f⁻¹ s) ≡ s
   invˡ ([] , (u , v) , refl , (Pa∷u , P☆v)) = refl
   invˡ (νP ∷ νP✶ , etc) rewrite invˡ (νP✶ , etc) = refl

   invʳ : (s : δ (P ☆) a w) → f⁻¹ (f s) ≡ s
   invʳ (suc☆ (([] , .(a ∷ w)) , refl , (νP , P☆a∷w))) rewrite invʳ P☆a∷w = refl
   invʳ (suc☆ ((.a ∷ u , v) , refl , (Pa∷u , P☆v))) = refl

\end{code}

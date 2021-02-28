\begin{code}[hide]
{-# OPTIONS --safe #-}
open import Level

module Calculus {ℓ} (A : Set ℓ) where

-- open import Data.Empty
-- open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Properties using (++-identityʳ)
open import Function using (id; _∘_; _↔_; mk↔′)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Misc {ℓ}
open import Inverses {ℓ}

-- open import Language A
open import Predicate ; open ListOps A

private
  variable
    a c : A
    s x : Set ℓ
    b : Level
    B : Set b
    X : Set b
    P Q : Lang
    f : A ✶ → B
    u v w : A ✶
\end{code}

%<*ν𝒟>
\AgdaTarget{ν, δ}
\begin{code}
ν : (A ✶ → B) → B                -- “nullable”
ν f = f []

𝒟 : (A ✶ → B) → A ✶ → (A ✶ → B)  -- “derivative”
𝒟 f u = λ v → f (u ⊙ v)
\end{code}
%% 𝒟 f u v = f (u ⊙ v)
%% 𝒟 f u = λ v → f (u ⊙ v)
%% 𝒟 f u = f ∘ (u ⊙_)
%</ν𝒟>

%<*δ>
\begin{code}
δ : (A ✶ → B) → A → (A ✶ → B)
δ f a = 𝒟 f [ a ]
\end{code}
%</δ>

%<*𝒟[]⊙>
\begin{code}
𝒟[] : 𝒟 f [] ≡ f

𝒟⊙ : 𝒟 f (u ⊙ v) ≡ 𝒟 (𝒟 f u) v
\end{code}
\begin{code}[hide]
𝒟[] = refl

𝒟⊙ {u = []} = refl
𝒟⊙ {f = f} {u = a ∷ u} = 𝒟⊙ {f = δ f a} {u = u}
\end{code}
%</𝒟[]⊙>

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

%<*ν∘𝒟>
\begin{code}
ν∘𝒟 : ν ∘ 𝒟 f ≗ f
\end{code}
\begin{code}[hide]
ν∘𝒟 u rewrite (++-identityʳ u) = refl

-- ν∘𝒟 f u = cong f (++-identityʳ u)

-- ν∘𝒟 f []       = refl
-- ν∘𝒟 f (a ∷ as) = ν∘𝒟 (δ f a) as
\end{code}
%</ν∘𝒟>

%<*𝒟foldl>
\begin{code}
𝒟foldl : 𝒟 f ≗ foldl δ f
\end{code}
\begin{code}[hide]
𝒟foldl []        = refl
𝒟foldl (a ∷ as)  = 𝒟foldl as
\end{code}
%</𝒟foldl>

%% Phasing out. Still used in talk.tex.
%<*ν∘foldlδ>
\AgdaTarget{ν∘foldlδ}
%% ν∘foldlδ : ∀ w → P w ≡ ν (foldl δ P w)
\begin{code}
ν∘foldlδ : ν ∘ foldl δ f ≗ f
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
\AgdaTarget{νpureᵀ, νmapᵀ, νmapᵀ₂}
\begin{code}
νpureᵀ  : ν (pureᵀ  x)      ≡ x
νmapᵀ   : ν (mapᵀ   g P)    ≡ g  (ν P)
νmapᵀ₂  : ν (mapᵀ₂  h P Q)  ≡ h  (ν P) (ν Q)
\end{code}
\AgdaTarget{δpureᵀ, δmapᵀ, δmapᵀ₂}
\begin{code}
δpureᵀ  : δ (pureᵀ  x)      a ≡ pureᵀ  x
δmapᵀ   : δ (mapᵀ   g P)    a ≡ mapᵀ   g (δ P a)
δmapᵀ₂  : δ (mapᵀ₂  h P Q)  a ≡ mapᵀ₂  h (δ P a) (δ Q a)
\end{code}
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

ν☆ {P = P} = mk↔′ k k⁻¹ invˡ invʳ
 where
   k : ν (P ☆) → (ν P) ✶
   k zero☆ = []
   k (suc☆ (([] , []) , refl , (νP , νP☆))) = νP ∷ k νP☆

   k⁻¹ : (ν P) ✶ → ν (P ☆)
   k⁻¹ [] = zero☆
   k⁻¹ (νP ∷ νP✶) = suc☆ (([] , []) , refl , (νP , k⁻¹ νP✶))

   invˡ : ∀ (νP✶ : (ν P) ✶) → k (k⁻¹ νP✶) ≡ νP✶
   invˡ [] = refl
   invˡ (νP ∷ νP✶) rewrite invˡ νP✶ = refl

   invʳ : ∀ (νP☆ : ν (P ☆)) → k⁻¹ (k νP☆) ≡ νP☆
   invʳ zero☆ = refl
   invʳ (suc☆ (([] , []) , refl , (νP , νP☆))) rewrite invʳ νP☆ = refl

δ☆ {P}{a} {w} = mk↔′ k k⁻¹ invˡ invʳ
 where
   k : δ (P ☆) a w → ((ν P) ✶ · (δ P a ⋆ P ☆)) w
   k (suc☆ (([] , .(a ∷ w)) , refl , (νP , P☆a∷w))) with k P☆a∷w
   ... |            νP✶  , etc
       = νP ∷ νP✶ , etc
   k (suc☆ ((.a ∷ u , v) , refl , (Pa∷u , P☆v))) = [] , (u , v) , refl , (Pa∷u , P☆v)

   k⁻¹ : ((ν P) ✶ · (δ P a ⋆ P ☆)) w → δ (P ☆) a w
   k⁻¹ ([] , (u , v) , refl , (Pa∷u , P☆v)) = (suc☆ ((a ∷ u , v) , refl , (Pa∷u , P☆v)))
   k⁻¹ (νP ∷ νP✶ , etc) = (suc☆ (([] , a ∷ w) , refl , (νP , k⁻¹ (νP✶ , etc))))

   invˡ : (s : ((ν P) ✶ · (δ P a ⋆ P ☆)) w) → k (k⁻¹ s) ≡ s
   invˡ ([] , (u , v) , refl , (Pa∷u , P☆v)) = refl
   invˡ (νP ∷ νP✶ , etc) rewrite invˡ (νP✶ , etc) = refl

   invʳ : (s : δ (P ☆) a w) → k⁻¹ (k s) ≡ s
   invʳ (suc☆ (([] , .(a ∷ w)) , refl , (νP , P☆a∷w))) rewrite invʳ P☆a∷w = refl
   invʳ (suc☆ ((.a ∷ u , v) , refl , (Pa∷u , P☆v))) = refl

\end{code}


Clarify the relationship with automatic differentiation:

Now enhance \AF 𝒟:
%<*𝒟′>
\begin{code}
𝒟′ : (A ✶ → B) → A ✶ → B × (A ✶ → B)
𝒟′ f u = f u , 𝒟 f u
\end{code}
%</𝒟′>

%% The ʻ name trick (defined in unicode.tex) adds a hat to the name it precedes.
%<*ʻ𝒟>
\begin{code}
ʻ𝒟 : (A ✶ → B) → A ✶ → B × (A ✶ → B)
ʻ𝒟 f u = ν f′ , f′ where f′ = foldl δ f u
\end{code}
%% ʻ𝒟 f u = let f′ = foldl δ f u in ν f′ , f′
%</ʻ𝒟>

%<*𝒟′≡ʻ𝒟>
\begin{code}
𝒟′≡ʻ𝒟 : 𝒟′ f ≗ ʻ𝒟 f
\end{code}
\begin{code}[hide]
𝒟′≡ʻ𝒟 [] = refl
𝒟′≡ʻ𝒟 (a ∷ as) = 𝒟′≡ʻ𝒟 as
\end{code}
%</𝒟′≡ʻ𝒟>

\note{There's probably a way to \AK{rewrite} with \AB{𝒟foldl} and \AB{𝒟′foldl} to eliminate the induction here.}

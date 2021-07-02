# Paper #87 review responses

***Note:** I say "we" instead of "I" in these responses, because the blind review process was still in effect when I wrote them.*


## Review A

> My major concern is novelty, but unfortunately I am not familiar with the prior work. Given that I was a bit surprised by the absence of prior work, and that there were already so many papers on related topics, my rating is B. I might advocate for this paper more enthusiastically once novelty is confirmed.

We were surprised as well not to find formalized & mechanized connections between the simple, non-operational semantics of language specification and the dual decidable representations of regular expressions and tries.
Note also that proof relevance yields *parsing* (explanations) rather than mere recognition.
We are not aware of formalized (or even rigorous) accounts of *parsing* (as opposed to mere recognition) based on non-operational specification of languages and derivatives.

> I recognize that a note on the versions of Agda and its standard library would help the reader.

Will do. Thank you for the suggestion!


## Review B

> It seems that in Fig. 1 "a language over an alphabet A" is not A^* but A^* -> Set l. This is at least nonstandard --- a standard definition should be A*. Explain the reason.

`A^*` is the set of *all* strings over an alphabet `A`, i.e., the "universal language".
Other languages are proper subsets, which are neatly formalized in type theory as `A^* -> Set l`, i.e., a function mapping each string `w` to the type of proofs that `w` is in the language.

> By the way, can you use Prop instead of Set l? I suspect the former is more intuitive, especially for those who are not experts on type theory. 

`Set` appears to be much more widely used in the Agda ecosystem than `Prop` and so using `Set` allows reusing many more existing definitions and proofs, including type isomorphisms.
More fundamentally, `Prop` is proof-irrelevant, so we would only get language recognition.
In contrast, using `Set` gives proof-relevant recognition, i.e., parsing.

> In Fig. 1, while I believe c :: A, I could not figure out the type of scalar, s.

In the definition of scalar multiplication (`(s · P) w = s × P w`), `s` appears as an argument to the type product operator and so is a type (i.e., has type `Set ℓ`).
Logically, it's a proposition being conjoined with the property of the string `w` being in the language `P`.
This operator makes for more elegant and more general formulations of derivatives of concatenated and starred languages than Brzozowski's definitions.
The additional generality comes from proof relevance ("parsing").
It's also fundamentally important to the algebraic setting of semimodules (generalized vector spaces), which is a natural fit to proof-relevant languages.

> This paper carefully distinguished three kinds of equalities, namely propositional equality, isomorphism, and extensional isomorphism. However, I did not understand why that equality should be used for each occurrence. For example, why in Fig. 1 is propositional equality necessary?

Figure 1 uses both propositional equality and extensional isomorphism.
We could not have used (propositional) equality for all of the lemmas, since this strong condition does not hold in all cases.
We could have used the weaker isomorphism condition for all of the lemmas, but the equalities are more specific and thus more informative.
Moreover, isomorphisms require some notational overhead to apply, as shown where they are invoked in figures 5 and 7.
In fact, there might be some notational overhead even for propositional equalities, but these ones are actually *definitional* (meaning proved by normalization, as noted on line 194), making them especially convenient.

The reason for using both isomorphism and extensional isomorphism is simply that the `ν` lemmas are about types/propositions (nullability) while the `δ` lemmas are about predicates (general, proof-relevant language membership).

*Correction:* My answer was about Figure 3.
As for Figure 1, the uses of propositional equality are for lists (not types or type-level predicates), to which the other mentioned equality notions do not apply.

> Section 2 uses A* -> B instead of A* -> Set l. Perhaps, the reason is that all the definitions can be polymorphic on the result, B. However, this difference at least makes the meaning difficult to understand. 

Indeed, this generalization is important because it points out that the central notion of derivatives is much more general than its usual setting of languages (even beyond generalizing from `Set` to arbitrary semirings), and some definitions and properties hold in the more general setting.

> p5. "isomorphic types or predicates are equivalently decidable":
> I could not understand the reason.

The reason (proof) is outlined in the next sentence ("One direction of the isomorphism proves \AB{B} from \AB{A}, while the other proves {\AF ¬ B} from {\AF ¬ A}") and formalized in the definitions/proofs of the `_▹_` and `_▸_` signatures/lemmas stated in between.
As with the rest of the paper, we mostly state the lemmas & theorems (signatures), leaving the interested reader to view proofs as desired in the paper/project's Agda source code.

> Figs. 4 and 5 are nearly identical to Figs. 6 and 7. While I could understand that it is because of the duality, I still wonder what is the essential differences. 

The essential difference is that the representation data constructors and the representation examiners trade places (the duality).
More specifically

*   For regular expressions, language building blocks (`∅`, `_∪_`, `𝟙`, `_*_`, etc) are data constructors, while `ν` and `δ` are functions that examine the data.
*   For tries, `ν` and `δ` are codata constructors, while language building blocks are functions that examine the codata.

This duality is visually highlighted in the code arrangement in figures 4 and 6 and in the syntax coloring in figures 5 and 7.
(Line 419: "The compiler-generated syntax coloring differs to reflect the changed interpretation of the definitions.")

> Usually, an inductive definition gives a datatype, whereas a coinductive one does a function (or stream). However, the automatic differentiation requires the concrete construction process of the function even for the coinductive case. Another possible difference is the potential of the infiniteness of the coinductive definition. However, for this particular case, I am not aware of the usefulness of infiniteness. 

The same pattern occurs in this paper.
Streams are a special case of string tries (for a singleton alphabet), being infinite in the specific and more general case.
The pattern also generalizes beyond string tries to tries over arbitrary regular algebraic data types.

By "concrete construction process", do you mean that there are still (corecursively defined) examination functions?
If so, this situation is also customary in our experience when working with coinductive structures.

> On page 9. it is argued that a difference is a work-sharing between the function and its derivative. I agree with this point but do not think it to be critical. Existing parsing methods based on the derivatives do such work sharing. Moreover, automatic differentiation alone cannot share repeated calculations of derivatives when we arrive at the same state more than once.

We thought this work sharing issue worth pointing out, because it makes an enormous difference for symbolic vs automatic differentiation in the usual calculus sense, and indeed is the main argument usually given in the literature for preferring the latter over the former.
We are not aware of a clear or rigorous discussion of the issue in derivative-based parsing work (though there are many optimizations described informally and without semantic basis).
It is not clear what the practical implications are in the setting of languages, but it seems worth mentioning to stimulate closer examination.
If the performance difference is much less than with differential calculus, then it's important to understand why.
For instance, maybe there is a dual technique for regular expressions that could be examined clearly for useful practical and theoretical insight.
On the other hand, if the difference is the same or greater, then it's important to exploit the potential with better justification and perhaps implementation.

We certainly agree with your remark about the potential for improved work sharing when a "state" is reached in more than one way!


## Review C

> The specification of language membership (language operations) is non-operational and it seems to be one of the key ideas that the authors are advocating, i.e., to have as simple as possible specifications with respect to which other operations (or implementations) can be proved correct.

Yes, exactly.

> The result of this approach is that the provided language membership deciders (defined using differentiation on inductive or coinductive representations of the language) are correct. In other words, the function that decides language membership is a theorem saying that if there is a representation for a language P, then language membership in P is decidable, i.e., for any w, the function either computes a witness of P w (the type of language membership proofs of w in P) or constructs a proof that no such exists.

Indeed. Well-summarized. Thank you.

> Overall, I think this is a nice, clean, well-written and compact paper. Working things out so that clean and simple definitions are also "magically" correct according to Agda is often a non-trivial task. The idea that specifications should be as simple as possible is a very reasonable one. Therefore, I think these ideas deserve to be communicated.

Thank you!
The clean, simple, automatically verified nature is exactly what we were wanting to highlight.

> One issue I have is that reading the paper might give the impression that the choice of type theory (instead of set theory) or type-level languages is necessary for achieving non-operational specification of language membership or more informative language membership than just true/false. >The paper does demonstrate that type theory can be convenient for achieving this.
>
> For example, the concatenation of P and Q (subsets of A*) is a certain subset of A* 
>
> P * Q = { w \in A* | exists u, v. w = uv \and u \in P \and v \in Q }
>
> and the characteristic function of this set corresponds to what is given in Figure 1. This could be done in Agda with decidable languages (A* -> 2) and thus also achieve non-operational specification (values of A* -> 2 as type indices). (Assumption: a word w can be decomposed in a finite number of ways.)

We wrote a comparison with set-theoretical and decidable specifications and discarded it for better focus.
Yes, one can start with decidable languages and exploit the property that every finite list can be unappended in finitely many ways.
Doing so would go against the principle of simple, elegant, non-operational *specifications*, since it relies on cleverness involving and motivated by decidability of language *recognition* rather than the simpler nature of language *definition*.

> line 18: I think it would be helpful to later mention what properties would have required induction/coinduction? 

Thanks. We might refer to Abel [2016], which proves a great number of algebraic properties on tries, all of them needing coinduction/bisimulation.
The key to eliminating these much more complex proofs is inheriting properties from the *indices* (languages specified as type-level predicates), which are simple and neither inductive nor coinductive.

> Contribution 1, line 93: Is this meant to say that capturing the semantic essence of Brzozowski's derivatives is something new? The semantic operation was defined before the syntactic one. Brzozowski references three papers where (under different names) derivatives of sequences are used and then defines the corresponding operation on syntax.

*Formalizing* (stating and proving in a formal system) the semantic essence is new, as far as we know. Generalizing this essence from languages to functions from lists might be new as well. Moreover, most recent work we know of seems to identify derivatives with regular expressions, leading readers away from the more natural and general notion in practice and its alternative realizations, such as tries. (Abel [2016] is an exception but lacks a formal semantic specification separate from the implementation itself.)

See also the paragraph starting on line 717, including the mention of Brzozowski on line 720.
I imagine you will agree that it is easier to make clear comparisons after the technical substance is presented (in conclusions) than before (in introduction); and yet readers want at least a general sense of comparison before the technical substance.

> Contribution 2, line 99: The duality is between regular expressions and a certain subset of tries (those constructed using the language building operations). The two things named Lang in Figures 4 and 6 are not equally expressive.

We agree. This comparison can be expressed more clearly, including the fact that regular expressions *and their derivatives* also naturally generalize to a much broader class of languages, as Might and Darais [2010] and follow-up work has noted (though without much specification or rigor).

> line 103: Is "proof isomorphism" (throughout the paper) the same as "type isomorphism" on line 188?

Yes. "Type isomorphism" is more technically specific (suiting the technical meat of the paper), while its use as "proof isomorphism" seems more suitable for the introduction and the contrast with "logical equivalence" mentioned in line 103.

> Contribution 3, line 103: Is this statement considering previous work on formalisations or formal languages in general? As soon as something more general is considered instead of nullability (true/false empty word property), the lemmas (or definitions) for concatenation and closure start to look like those in Figure 2. 

The statement refers to work we are aware of in formal languages as well as its formalization. Have we missed something important?

> line 179: What is meant exactly by "liberation"? I think it is fairly standard to consider left and right quotients (wrt. a word) of languages (sets of strings, no grammars) as monoid actions and thus reducing language membership to nullability also in a step-by-step manner.

This sentence is in the context of the immediately preceding sentence, which refers to Brzozowski's paper ("Derivatives of *Regular Expressions*"---emphasis mine) and its extensions by Might and Darais [2010] etc.
We are trying to encourage a shift from recent near-identification of derivatives (for parsing) as about a particular grammatical/inductive language representation back to the underlying semantic basis you mention (though also tilted toward proof relevance for parsing and other applications), so that the formal development has a simpler formal starting point (and neither inductive nor coinductive) and alternatives to grammatical representation are easier to notice.

> line 283: I think it would be good to also say what is the correctness condition (in addition to the fact that it is guaranteed by types).

The condition is stated on line 228 and is captured in the type of `⟦_⟧` on line 310, namely that `⟦_⟧` is both computable and converts a language into a decidable recognizer/parser.
We will add a reminder at line 283.
Thanks.

> line 308: This left triangle looks like a map operation. Maybe a comment about why this has to be part of the syntax.

The left triangle *reifies* a map operation.
The reason it must be part of the inductive representation is the same as the other constructors, namely so that the core lemmas (figure 2) translate into an implementation.
We will add a comment.

> line 333: Maybe a comment about why f works on the left hand side of the triangle with both p and with p differentiated.

Thanks.
The reason is that both `p` and `δ p a` are languages/predicates.

> Figures 4 and 5: there is no definition of the language (A* -> Set) denoted by an expression and thus no formal statement that it indeed denotes the language in its type.

Thank you.
This missing semantic function maps every `p : Lang P` to `P`, regardless of the specifics of `p` (which is why the algebraic properties transfer effortlessly from type-level languages without having to consider the structure of `p`).
We agree that it's worth stating explicitly and will do so.

> line 623: By a choice of an equivalence relation we are quotienting the (encapsulated) representation. It would be good to give a bit more intuition here (which quotient is this).

Indeed. This comment is closely related to your remark above about the denotation of the decidable language representations and has the same answer. Equivalence of representations is *semantic* equivalence, which is to say equivalence of the indices (type-level languages) that capture the semantics.
We will add this clarification.

> line 723: What are transformations?

The rules of differentiation, as transformations of symbolic/grammatical representations.

> line 724: "based *on* the"?

Fixed. Thanks!


## Review D

> Section 6.2 is quite dense, and its motivation is not entirely clear to me. Is its purpose to show that existentials can be used to force the dependently-typed definitions developed throughout the paper into the simply-typed algebraic structures? If so, I believe a single paragraph would to, and would perhaps be less confusing. Furthermore, the section title is confusing: transport properties to what? We haven't defined the existentially quantifier variants yet, so it's not yet obvious that we have anywhere to transport properties to.

The purpose is to show that the properties of non-decidable, type-level languages transfer effortlessly to the decidable implementations.
The importance of this fact is that one gets both (a) easy proofs of useful correctness properties (without complications due to efficiency and even decidability) *and* (b) efficient implementations.

This simple solution for property transfer, however, raises a "technical obstacle" (line 581): the indexed data types do not match the types of standard algebraic properties.
Existential wrapping is a simple, generic solution to this obstacle.

I renamed the section from "Transporting Properties" to "Transporting Properties from Specification to Implementations"

> Line 86: The clause "including the use of existential quantifiers" is confusing, as it in no way makes clear what the existential quantifiers are used for. I'd suggest dropping the clause entirely.

I've appended "(as in Figure 1) to that sentence".

> Line 500: The types of the primitive language constructs are elided throughout the paper. Therefore, it is a bit surprising to see that the variant of star which, ostensibly, abstracts away from lists, still references the list primitives foldr and All, as well as the monoid properties.

Before generalizing, the list plays two different algebraic roles: monoid and foldable.
Either can be generalized independently.

> Line 608: Why are the existentially-wrapped versions specifically based on the inductive variant? Is there anything specific that makes these better or more amenable? The text so far led me to believe the coinductive variant was better and more performant.

It was an arbitrary choice. Both implementations (inductive and coinductive) are wrapped alike. We will say so in the text.

> Line 638: Is the pattern matching in the type valid Agda syntax? Again, I don't think these liftings really add anything to the paper.

Yes. All such declarations and definitions in the paper (and those elided from the paper) are fully type- (and thus correctness-)checked when the paper is typeset.

* * * * * * * * * * * * * * * * * * * *

From the final review:
<blockquote>
The reviewers want to thank the author for this interesting submission and are happy to accept it with the understanding that the author will make all of the following changes:

1. Clarify what's new in the context of proof mechanization or type theory, what's new in the context of parsing, and what's new in the context of formal languages & automata. In particular, some contributions do not seem to be novel in the last context. The author did not respond to Reviewer C's comment about the work of Lombardy and Sakarovitch, but their work seems to be similar to the derivative operations in the paper and the author should pay attention to it (in addition to other related works).

2. Explain the Agda syntax more for the readers who are not familiar with Agda. For example, add concrete examples showing how operators in Fig. 1 apply to concrete regular expressions and words, including the fully expanded types and values (as witnesses of the membership). The current draft has only 16 pages so space should not be an issue.

3. Clarify the difference between data and codata: both generally and in terms of difference it makes for main results of this paper.

4. Consider explaining how to recover the ordinary setting where a language is a set of words and language union is idempotent. For example, explain how the current work can be used to prove the classical theorem for the ordinary setting that the set of derivatives of a regular expression is finite modulo associativity, commutativity and idempotence of union (although the derivative defined here might require more).

5. Fix typos and other issues that have already been discussed in the reviews and the response.
</blockquote>

My response:

1.  I added the following paragraph to the beginning of section 7 (Related Work):

    > The shift from languages as sets of strings to type-level predicates (i.e., proof relevance or “parsing”) is akin to weighted automata [Schützenberger 1961; Droste and Kuske 2019] and more generally to semiring-based parsing [Chomsky and Schützenberger 1959; Goodman 1998, 1999; Liu 2004], noting that types (“Set” in Agda) form a (commutative) semiring (up to isomorphism). In particular, Lombardy and Sakarovitch [2005] investigated Brzozowski-style derivatives in this more general setting, formalizing and generalizing the work of Antimirov [1996], who decomposed derivatives into simpler components (“partial derivatives”) that sum to the full derivative and lead to efficient recognizers in the form of nondeterministic automata.

    Also an initial sentence to the (now) third paragraph of that section:
    
    > The main contributions of this paper are to formalization and mechanization of language recognition and parsing.

2.  I added a new figure 2 with examples of languages and membership proofs, along with a new footnote 2 giving some detailed explanations.

3.  I added a new footnote 10:

    > Inductive types (“data”) describe finitely large values and are processed recursively (as least fixed points) by pattern- matching clauses that decompose arguments. Dually, coinductive types (“codata”) describe infinitely large values and are processed corecursively (as greatest fixed points) by copattern-matching clauses that compose results. Programs on inductive types are often proved by induction, while programs on coinductive types are often proved by coinduction. (As we will see in Section 6.2, however, the simple relationship to the specification in Section 2 allows many trivial correctness proofs, needing neither induction or coinduction.) See Gordon [1995] for a tutorial on theory and techniques of coinduction.
    > 
    > Tries in general represent functions, with each trie datum corresponding to a domain value. Even when each domain value is finitely large, there are often infinitely many of them (e.g., lists), so tries will naturally be infinite and thus more amenable to coinductive than inductive analysis.

4.  Appended to the final paragraph of section 7:

    > As mentioned at the end of Section 3, one can simplify the development above somewhat by replacing proof isomorphism with the coarser notion of logical equivalence. Doing so restores union idempotence (modulo equivalence), losing proof relevance and thus re- placing parsing by recognition. One might then also prove that the set of derivatives of a regular language is finite (again, modulo equivalence).

5.  Done!

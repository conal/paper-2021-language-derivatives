ICFP 2021 Paper #87 Reviews and Comments
===========================================================================

Paper #87 Symbolic and Automatic Differentiation of Languages


Review #87A
===========================================================================

Overall merit
-------------

B. I support accepting this paper but will not champion it.

Reviewer expertise
------------------

Z. Some familiarity

Paper summary
-------------

This paper fills in a possibly missing link between the list-based semantics of regular expressions and the trie-based coinductive semantics. The work was mechanized in Agda, using sized types to overcome one technical difficulty in defining the concatenation operator for the coinductive semantics.

Comments for author
-------------------

The two semantics used in the paper seem intuitive and I was a bit surprised that the equivalence has not been mechanized before. If the linkage is indeed missing from the literature, then this is a wonderful piece of work to be included.

I seemed to be able to infer the intended meaning of all the code, and the discussions look reasonable. However, I am a proficient Agda user and some notes on the syntax could help more general audience.

My major concern is novelty, but unfortunately I am not familiar with the prior work. Given that I was a bit surprised by the absence of prior work, and that there were already so many papers on related topics, my rating is B. I might advocate for this paper more enthusiastically once novelty is confirmed.

##### Response to other reviews about running Agda

I can check all the supplied Agda code, using the latest development versions (the master branches on GitHub) of Agda and the Agda standard library. The entire codebase contains two use of the `TERMINATING` pragma in `Automatic.lagda` which turns off the termination checker for the operations _not_ using sized types (as discussed in L420-432), but otherwise I did not find anything suspicious. As a bonus point, the authors have tried to impose `--without-K` that effectively turns off UIP when possible. I recognize that a note on the versions of Agda and its standard library would help the reader.



Review #87B
===========================================================================

Overall merit
-------------

B. I support accepting this paper but will not champion it.

Reviewer expertise
------------------

Z. Some familiarity

Paper summary
-------------

This paper studies type-theoretic accounts of parsing. It generalizes Brzozowsik's derivatives for regular expressions to arbitrary languages and points out that we can recover the original derivatives via reflections. It also finds that the reflection applied to the dual (i.e., coinductive) definition leads to tries. The theory is implemented and proved in Agda. 

I generally like this paper. A type-theoretic view of parsing is an interesting research topic, and it reports several findings. In particular, I was excited to use automatic differentiation for calculating Brzozowski derivatives. However, its presentation is not good. It is like the authors' own memo. It enumerates necessary formulas without providing sufficient explanations. I suspect that the current draft is accessible only by limited experts.

Comments for author
-------------------

*   Not all ICFP audiences are familiar with the dependent type theory and Agda (even though most of them have heard them). Recalling basic notations and concepts is very useful. 

*   It seems that in Fig. 1 "a language over an alphabet A" is not A* but A* -> Set l. This is at least nonstandard --- a standard definition should be A*. Explain the reason. By the way, can you use Prop instead of Set l? I suspect the former is more intuitive, especially for those who are not experts on type theory. 

*   In Fig. 1, while I believe c :: A, I could not figure out the type of scalar, s.

*   This paper carefully distinguished three kinds of equalities, namely propositional equality, isomorphism, and extensional isomorphism. However, I did not understand why that equality should be used for each occurrence. For example, why in Fig. 1 is propositional equality necessary?

*   Section 2 uses A* -> B instead of A* -> Set l. Perhaps, the reason is that all the definitions can be polymorphic on the result, B. However, this difference at least makes the meaning difficult to understand. 

*   p5. "isomorphic types or predicates are equivalently decidable":
I could not understand the reason.

*   Figs. 4 and 5 are nearly identical to Figs. 6 and 7. While I could understand that it is because of the duality, I still wonder what is the essential differences. Usually, an inductive definition gives a datatype, whereas a coinductive one does a function (or stream). However, the automatic differentiation requires the concrete construction process of the function even for the coinductive case. Another possible difference is the potential of the infiniteness of the coinductive definition. However, for this particular case, I am not aware of the usefulness of infiniteness. 

*   On page 9. it is argued that a difference is a work-sharing between the function and its derivative. I agree with this point but do not think it to be critical. Existing parsing methods based on the derivatives do such work sharing. Moreover, automatic differentiation alone cannot share repeated calculations of derivatives when we arrive at the same state more than once.


Review #87C
===========================================================================

Overall merit
-------------

B. I support accepting this paper but will not champion it.

Reviewer expertise
------------------

Y. Knowledgeable

Paper summary
-------------

The main content of the paper is a formalisation of languages and derivatives. The starting point of the formalisation is the choice of type theory (Agda) instead of set theory. Languages are taken to be type-level predicates (A* -> Set). This allows for language membership to have more than just a single justification and to use constructions on types as the logical language to specify language membership. The specification of language membership (language operations) is non-operational and it seems to be one of the key ideas that the authors are advocating, i.e., to have as simple as possible specifications with respect to which other operations (or implementations) can be proved correct. The result of this approach is that the provided language membership deciders (defined using differentiation on inductive or coinductive representations of the language) are correct. In other words, the function that decides language membership is a theorem saying that if there is a representation for a language P, then language membership in P is decidable, i.e., for any w, the function either computes a witness of P w (the type of language membership proofs of w in P) or constructs a proof that no such exists. The rest of the paper works out a generalisation of languages to predicates and predicate operations, investigates some properties of these and how to transport properties to implementations. 

The Agda code did not parse with my version of Agda. Since there was no information of which version of Agda I should use, I did not verify/type check the Agda code. 

Overall, I think this is a nice, clean, well-written and compact paper. Working things out so that clean and simple definitions are also "magically" correct according to Agda is often a non-trivial task. The idea that specifications should be as simple as possible is a very reasonable one. Therefore, I think these ideas deserve to be communicated.

Comments for author
-------------------

*   One issue I have is that reading the paper might give the impression that the choice of type theory (instead of set theory) or type-level languages is necessary for achieving non-operational specification of language membership or more informative language membership than just true/false. The paper does demonstrate that type theory can be convenient for achieving this.

    For example, the concatenation of P and Q (subsets of A*) is a certain subset of A* 

    P * Q = { w \in A* | exists u, v. w = uv \and u \in P \and v \in Q }

    and the characteristic function of this set corresponds to what is given in Figure 1. This could be done in Agda with decidable languages (A* -> 2) and thus also achieve non-operational specification (values of A* -> 2 as type indices). (Assumption: a word w can be decomposed in a finite number of ways.)

*   Instead of considering languages as A* -> 2 we could take A* -> R where R is a semiring (for example, integer semiring to consider languages as multisets of words instead of just sets of words, i.e., a word occurs in a language some number of times). 

*   My main concern regarding this membership question is that this paper is very much related to weighted automata (a subfield of automata theory and formal languages) but there is no discussion of that. The main idea there is exactly that language membership is not necessarily given by (coefficients in) a Boolean semiring. Brzozowski's derivatives have been considered in that setting (Lombardy, Sakarovitch, Derivatives of rational expressions with multiplicity, 2005) and there are many similarities. 

*   line 18: I think it would be helpful to later mention what properties would have required induction/coinduction? 

*   Contribution 1, line 93: Is this meant to say that capturing the semantic essence of Brzozowski's derivatives is something new? The semantic operation was defined before the syntactic one. Brzozowski references three papers where (under different names) derivatives of sequences are used and then defines the corresponding operation on syntax.

*   Contribution 2, line 99: The duality is between regular expressions and a certain subset of tries (those constructed using the language building operations). The two things named Lang in Figures 4 and 6 are not equally expressive.

*   line 103: Is "proof isomorphism" (throughout the paper) the same as "type isomorphism" on line 188?

*   Contribution 3, line 103: Is this statement considering previous work on formalisations or formal languages in general? As soon as something more general is considered instead of nullability (true/false empty word property), the lemmas (or definitions) for concatenation and closure start to look like those in Figure 2. 

*   line 132: Another way to interpret these equations is that the derivative operation is a right monoid action (this might be equivalent to Footnote 4). Furthermore, since we are dealing with free monoids, the right monoid action is given by the generators (i.e., as a left fold).

*   line 179: What is meant exactly by "liberation"? I think it is fairly standard to consider left and right quotients (wrt. a word) of languages (sets of strings, no grammars) as monoid actions and thus reducing language membership to nullability also in a step-by-step manner.

*   line 283: I think it would be good to also say what is the correctness condition (in addition to the fact that it is guaranteed by types).

*   line 308: This left triangle looks like a map operation. Maybe a comment about why this has to be part of the syntax.

*   line 333: Maybe a comment about why f works on the left hand side of the triangle with both p and with p differentiated.

*   Figures 4 and 5: there is no definition of the language (A* -> Set) denoted by an expression and thus no formal statement that it indeed denotes the language in its type.

*   line 462: It is not clear to me why (just) the trie representation exploits the sharing potential. Due to the use of fold, it does not seem to be necessary to use the letter-by-letter differentiation. If f : A* -> B and u : A* then as automatic differentiation take \nu f', f' where f' = D f u. The same pattern can be used with symbolic differentiation by extending it to words via a fold. This part of the paper was a bit underwhelming for me. I was curious to learn what is automatic differentiation. It was described as some reinterpretation of function building vocabulary that avoids duplicated work. From this example it seems that everything here can avoid duplicate work. 

*   line 527: "booleans" is sometimes required to be capitalised.

*   line 580: Maybe an example of a property would be nice here.

*   line 623: By a choice of an equivalence relation we are quotienting the (encapsulated) representation. It would be good to give a bit more intuition here (which quotient is this).

*   line 722: Antimirov's derivatives, for example, have also been considered as an inductively defined relation. Then we can take the derivation trees for (e, w, e')  as the parsings or explanations (where e is an expression e, w is a word, e' is a nullable expression). 

*   line 723: What are transformations?

*   line 724: "based *on* the"?


Review #87D
===========================================================================

Overall merit
-------------

A. I will champion accepting this paper.

Reviewer expertise
------------------

X. Expert

Paper summary
-------------

The authors present a simple and straightforward formalisation of the basics of formal languages using Brzozowski derivatives in Agda.

Comments for author
-------------------


# Overview

Overall this is an eminently readable paper presenting interesting work and, possibly, an interesting addition to the Agda standard library, and I would happily recommend its acceptance based on that alone.

## Major comments

Section 6.2 is quite dense, and it's motivation is not entirely clear to me. Is it's purpose to show that existentials can be used to force the dependently-typed definitions developed throughout the paper into the simply-typed algebraic structures? If so, I believe a single paragraph would to, and would perhaps be less confusing. Furthermore, the section title is confusing: transport properties to what? We haven't defined the existentially quantifier variants yet, so it's not yet obvious that we have anywhere to transport properties to.


## Minor comments

The title of this paper could be made more explicit about its content:   more common use of the term "differentiation" refers to differentiation of real-valued functions (as known in Calculus or Machine Learning), and so the title may sound ambiguous. 

* Line 86: The clause "including the use of existential quantifiers" is confusing, as it in no way makes clear what the existential quantifiers are used for. I'd suggest dropping the clause entirely.

* Line 125: Please spend a few more words giving an intuition for the derivative 𝒟.

* Figs. 5 and 7: The column-major versus row-major distinction is rather vague, and requires a bit more explanation of the distinction between data and codata. For instance, w.r.t. the statement "each row is a complete definition" (line 416), it is difficult for the reader unfamiliar with copatterns to infer that, e.g., the first row contains a definition of the actions of \nu and \delta on \nothing, rather than an incomplete definition of \nu and \delta (as it would be with patterns).

* Line 500: The types of the primitive language constructs are elided throughout the paper. Therefore, it is a bit surprising to see that the variant of star which, ostensibly, abstracts away from lists, still references the list primitives foldr and All, as well as the monoid properties.

* Line 526: The closure operation is typeset with a different symbol. Is this intentional? Is it meant to refer the

* Line 568: The authors include an interpretation of the algebraic structure instantiated to natural numbers (as number of parses). However, they do not give a similar interpretation for probability distributions, and they do not motivate how tropical semirings would help with optimisation. Such additions would be very welcome!

* Line 608: The references to Figures 1 and 4 are rather opaque, especially given that these name are overloaded throughout the paper. Please mention in the text whether these refer to the inductive or the coinductive variant, to save the reader the long journey back to these figures.

* Line 608: Why are the existentially-wrapped versions specifically based on the inductive variant? Is there anything specific that makes these better or more amenable? The text so far led me to believe the coinductive variant was better and more performant.

* Line 619: The use of inj2 is confusing to readers familiar with the Agda standard library, as it usually refers to the right injection for sum types.

* Line 638: Is the pattern matching in the type valid Agda syntax? Again, I don't think these liftings really add anything to the paper.

* Fig. 14: I don't think the examples of opening various algebraic structures from the standard library adds anything to this paper, and if anything makes it more confusing. Neither the referred algebraic structures, nor the modules Symbolic and Automatic were define in this paper. I think removing this figure is probably preferable over adding explanations of the various structures.

* * * * * * * * * * * * * * * * * * * *

Comment @A1 by Reviewer A
---------------------------------------------------------------------------
The reviewers want to thank the author for this interesting submission and are happy to accept it with the understanding that the author will make all of the following changes:

1. Clarify what's new in the context of proof mechanization or type theory, what's new in the context of parsing, and what's new in the context of formal languages & automata. In particular, some contributions do not seem to be novel in the last context. The author did not respond to Reviewer C's comment about the work of Lombardy and Sakarovitch, but their work seems to be similar to the derivative operations in the paper and the author should pay attention to it (in addition to other related works).
2. Explain the Agda syntax more for the readers who are not familiar with Agda. For example, add concrete examples showing how operators in Fig. 1 apply to concrete regular expressions and words, including the fully expanded types and values (as witnesses of the membership). The current draft has only 16 pages so space should not be an issue.
3. Clarify the difference between data and codata: both generally and in terms of difference it makes for main results of this paper.
4. Consider explaining how to recover the ordinary setting where a language is a set of words and language union is idempotent. For example, explain how the current work can be used to prove the classical theorem for the ordinary setting that the set of derivatives of a regular expression is finite modulo associativity, commutativity and idempotence of union (although the derivative defined here might require more).
5. Fix typos and other issues that have already been discussed in the reviews and the response.

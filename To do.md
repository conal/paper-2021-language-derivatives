## To do

*   Conclusions and future work:
    *   Sharing work and finite-state property
*   Check footnotes composition carefully.
    Sometimes there are terrible splits across pages or even a figure appearing beneath a footnote.
    The ACM layout does better than my own.

*   Mention optimizations for regular expressions and tries.
*   Read over `Predicate.Properties` and see what might be worth mentioning.
    For instance, distributivity of concatenation over union generalizes to mapping.
*   Rework abstract now that I've moved the predicate generalization toward the end of the paper.
*   Maybe further highlight the specific differences between the ν-δ lemmas and Brzozowski's original versions (imitated AFAICT by related work).

*   Maybe "proof relevance" is a better term for the proof isomorphism aspect of this paper.
    For languages, proof relevance means we care about the proofs, and we do care, since the parsing information is in the proof.
    "Proof-relevant languages".
*   Generalize from lists.
    Other types have their own deltas.

Less important:

*   Fourier theorem?
*   Reconcile talk font vs paper font.
    I don't know how they come to differ.
*   Future work:
    *   Beyond regular languages
    *   Could I automate the transition from lemmas to implementation via rewrite rules?
        I'd have to suppress normalization, which would seem to break many proofs.
    *   DFA and/or NFA implementations from the same specification and in the same style, i.e., indexed by type-level languages.

From old paper version to-do:

*   Maybe switch to semiring and module notation starting in *Predicate Algebra*.
*   Explore the idea that Brzozowski's technique uses symbolic differentiation, but automatic differentiation has the usual advantages.
    What dimension do our domain and codomain have?
    Do forward, reverse, and mixed modes have anything to say?
    Is there something *linear* about derivatives?
    The right meaning for linearity seems clear from the function/free semimodule.
*   Other forms of convolution.
    I think generalized convolution is intrinsically amenable to memoization / dynamic programming.
    What about incremental evaluation?
*   Try redefining `AgdaFormat` as described in latex/agda.sty for more control over token rendering.
    If successful, stop using a special unicode replacement for "`*`" in the text.
*   Regular expressions and beyond:
    *   Define an inductive type family of regular expressions and a semantic function.
        Provide a `ClosedSemiring` instance and prove that the semantic function is a closed semiring homomorphism.
        Use as an alternative implementation of matching.
    *   Likewise for other language classes.
*   Run this stuff, and do some simple timing.
*   Find some languages with genuinely dependent types.
    I have something similar with decidability, though `Dec` instead of `Set`.

## Did

*   Link to repo, and say what versions of Agda and agda-stdlib.
*   From reviews:
    *   Note versions of Agda and its standard library.
    *   "line 283: I think it would be good to also say what is the correctness condition (in addition to the fact that it is guaranteed by types)."
       The condition is stated on line 228 and is captured in the type of `⟦_⟧` on line 310, namely that `⟦_⟧` is both computable and converts a language into a decidable recognizer/parser.
       Add a reminder at line 283.
    *   "line 308: This left triangle looks like a map operation. Maybe a comment about why this has to be part of the syntax."

        Indeed, the left triangle does reify a map operation.
        The reason it must be part of the inductive representation is the same as the other constructors, namely so that the core lemmas (figure 2) translate into an implementation.
        Add a clarifying comment.

    *   "Figures 4 and 5: there is no definition of the language (A* -> Set) denoted by an expression and thus no formal statement that it indeed denotes the language in its type."

        This missing semantic function maps every `p : Lang P` to `P`, regardless of the specifics of `p`.
        Add it.

        "line 623: By a choice of an equivalence relation we are quotienting the (encapsulated) representation. It would be good to give a bit more intuition here (which quotient is this)."

        This comment is closely related to the previous one about the denotation of the decidable language representations and has the same answer.
        Equivalence of representations is *semantic* equivalence, which is to say equivalence of the indices (type-level languages) that capture the semantics.
        Add this clarification.

*   Define language star via `mapⱽ` and `All`.
*   Check each use of `\\agda` to see if removing a preceding blank line improves indentation.
*   Point to the GitHub repo in the non-ACM version of the paper.
*   Maybe use acmsmall for the public/non-anonymous version of my paper, tweaking some features.
    Reconsider each use of `\\ifacm`.
*   Fix layout for `\\figref{nu-delta-codomain-lemmas}` in ACM version.
    It now uses horizontal layout, requiring `small` for ACM.
    I have plenty of room, so stack vertically instead.
*   Automata perspective.
*   Clarify tries as "automatic differentiation".
*   Mention the *non-idempotence* of this notion of languages, due to choice of equivalence relation.
*   Maybe mention logical equivalence vs proof isomorphism again in the Related Work section.
*   Wouter's paper
*   Mention OstermannJabs2018.
*   Maybe demote sections 4 (Reflections), 5 (Symbolic Differentiation), and 6 (Automatic Differentiation) into subsections of a new section called "From languages to parsing".
   Probably replace all occurrences of "`\\secreftwo{Symbolic Differentiation}{Automatic Differentiation}`".
*   Consider exposing level polymorphism in the talk & paper.
    It's there just under the surface.
*   Polish the abstract, especially the second/middle paragraph.
*   Fill in missing references and explanations flagged in the text.
*   Cite Martin Löf type theory.
*   Related work
*   Introduction, including clear statement of contributions
*   Mention that everything in the paper is verified by Agda.
    Here's what Andreas Abel wrote in *Equational Reasoning about Formal Languages in Coalgebraic Style*:
    "All the definitions, theorems, and proofs of this paper have been extracted from Agda code via an Agda to LaTeX translation and are, thus, guaranteed to be correct (assuming the consistency of Agda itself)."

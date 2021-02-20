## To do

*   Maybe demote sections 4 (Reflections), 5 (Symbolic Differentiation), and 6 (Automatic Differentiation) into subsections of a new section called "From languages to parsing".
   Probably replace all occurrences of "`\\secreftwo{Symbolic Differentiation}{Automatic Differentiation}`".
*   Clarify tries as "automatic differentiation".
*   Read over `Predicate.Properties` and see what might be worth mentioning.
    For instance, distributivity of concatenation over union generalizes to mapping.
*   `starʳ`
*   Define language star via `mapⱽ` and `All`.
*   Consider exposing level polymorphism in the talk & paper.
    It's there just under the surface.
*   Mention the *non-idempotence* of this notion of languages, due to choice of equivalence relation.
*   Fix layout for `\\figref{nu-delta-codomain-lemmas}` in ACM version.
    It now uses horizontal layout, requiring `small` for ACM.
    Stack vertically instead.

Less important:

*   Fourier theorem?
*   Reconcile talk font vs paper font.
    I don't know how they come to differ.
*   Future work:
    *   Beyond regular languages
    *   Could I automate the transition from lemmas to implementation via rewrite rules?
        I'd have to suppress normalization, which would seem to break many proofs.
    *   DFA and/or NFA implementations from the same specification and in the same style, i.e., indexed by type-level languages.
    *   Optimizations for regular expressions and tries.

From old paper version to-do:

*   Maybe switch to semiring and module notation starting in *Predicate Algebra*.
*   Scour ICFP proceedings for papers done in dependently typed languages, especially Agda.
    What can I learn?
    Must I tone down the Agda-ness for ICFP?
    Maybe ask colleagues for advice, e.g., Wouter Swierstra.
*   Explore the idea that Brzozowski's technique uses symbolic differentiation, but automatic differentiation has the usual advantages.
    What dimension do our domain and codomain have?
    Do forward, reverse, and mixed modes have anything to say?
    Is there something *linear* about derivatives?
    The right meaning for linearity seems clear from the function/free semimodule.
*   Generalize from lists.
    Other types have their own deltas.
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

*   Polish the abstract, especially the second/middle paragraph.
*   Fill in missing references and explanations flagged in the text.
*   Cite Martin Löf type theory.
*   Related work
*   Introduction, including clear statement of contributions
*   Mention that everything in the paper is verified by Agda.
    Here's what Andreas Abel wrote in *Equational Reasoning about Formal Languages in Coalgebraic Style*:
    "All the definitions, theorems, and proofs of this paper have been extracted from Agda code via an Agda to LaTeX translation and are, thus, guaranteed to be correct (assuming the consistency of Agda itself)."

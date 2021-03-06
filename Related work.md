## Related work

*   [*Combining predicate transformer semantics for effects: a case study in parsing regular languages*]\:
    *   ...

*   [*Equational Reasoning about Formal Languages in Coalgebraic Style*]\:
    *   Focuses on coalgebraic/coinductive techniques.
    *   Relates to automata theory.
    *   Implements the same vocabulary on tries as in my paper, but does not prove consistency with a simpler, less operational specification.
    *   Equivalence is defined via bisimulation, and proofs are coinductive, in terms of tries.

*   [*A Typed, Algebraic Approach to Parsing*]\:

    <blockquote>
    In this paper, we recall the definition of the context-free expressions (or μ-regular expressions), an algebraic presentation of the context-free languages. Then, we define a core type system for the context-free expressions which gives a compositional criterion for identifying those context-free expressions which can be parsed unambiguously by predictive algorithms in the style of recursive descent or LL(1).

    Next, we show how these typed grammar expressions can be used to derive a parser combinator library which both guarantees linear-time parsing with no backtracking and single-token lookahead, and which respects the natural denotational semantics of context-free expressions. Finally, we show how to exploit the type information to write a staged version of this library, which produces dramatic increases in performance, even outperforming code generated by the standard parser generator tool ocamlyacc.
    </blockquote>

    Doesn't seem strongly relevant, since it uses simple types and doesn't capture correctness.
    On the other hand, it may have some helpful pointers for extending from regular languages to context-free.

        > This paper describes an implementation of Harper's continuation-based regular-expression matcher as a strong functional program in Cedille; i.e., Cedille statically confirms termination of the program on all inputs. The approach uses neither dependent types nor termination proofs. Instead, a particular interface dubbed a recursion universe is provided by Cedille, and the language ensures that all programs written against this interface terminate. Standard polymorphic typing is all that is needed to check the code against the interface. This answers a challenge posed by Bove, Krauss, and Sozeau.

*   *Strong Functional Pearl: Harper’s Regular-Expression Matcher in Cedille*:
    *   Abstract:
        > This paper describes an implementation of Harper's continuation-based regular-expression matcher as a strong functional program in Cedille; i.e., Cedille statically confirms termination of the program on all inputs. The approach uses neither dependent types nor termination proofs. Instead, a particular interface dubbed a recursion universe is provided by Cedille, and the language ensures that all programs written against this interface terminate. Standard polymorphic typing is all that is needed to check the code against the interface. This answers a challenge posed by Bove, Krauss, and Sozeau.

*   [*Intrinsic Verification of a Regular Expression Matcher*]\:

    *  Quote:
    > When coding a program/proof in a dependently typed language, there is a choice between "extrinsic" verification (write the simply-typed code, and then prove it correct) and "intrinsic verification" (fuse the program and proof into one function, with a dependent type).

    *   Uses Agda
    *   Relies on defunctionalization to prove termination
    *   Bob H's original formulation identifies a termination bug.
        "The problem can be fixed by restricting the domain of the function to standard regular expressions, which have no Kleene-stared subexpressions that accept the empty string, and then using a preprocessor translation to solve the original problem."
        In this paper, they "use a syntactic criterion, generating standard regular expressions by literals, concatenation, alternation, and Kleene plus (one or more occurrences) instead of Kleene star (zero or more occurrences), and omitting the empty string regexp ε."
    *   The authors define an indexed data type `_∈Ls_` of regular expressions that is quite similar to my few definitions.
    *   They relate general regular expressions to standard ones.

*   [*Total parser combinators*]\:
    *   Abstract:
        <blockquote>
        A monadic parser combinator library which guarantees termination of parsing, while still allowing many forms of left recursion, is described. The library's interface is similar to those of many other parser combinator libraries, with two important differences: one is that the interface clearly specifies which parts of the constructed parsers may be infinite, and which parts have to be finite, using dependent types and a combination of induction and coinduction; and the other is that the parser type is unusually informative.

        The library comes with a formal semantics, using which it is proved that the parser combinators are as expressive as possible. The implementation is supported by a machine-checked correctness proof.
        </blockquote>
    *   Has a [GitHub repo](https://github.com/nad/parser-combinators).
    *   Introduction has many references for parser combinators.
    *   "In Sections 3.3 and 4.2 Brzozowski derivative operators (Brzozowski 1964) are implemented for recognisers and parsers, and in Sections 3.4 and 4.3 these operators are used to characterise recogniser and parser equivalence coinductively. Rutten (1998) performs similar tasks for regular expressions."
    *   "Agda is a total language. This means that all computations of inductive type must be terminating, and that all computations of coinductive type must be productive. A computation is productive if the computation of the next constructor is always terminating, so even though an infinite colist cannot be computed in finite time we know that the computation of any finite prefix has to be terminating. For types which are partly inductive and partly coinductive the inductive parts must always be computable in finite time, while the coinductive parts must always be productively computable."
    *   This paper seems quite relevant and worth studying.
        It doesn't appear to be as elegant, but then it is tackling context-free languages.

*   [*Certified Parsing of Regular Languages*]\:
    *   Abstract:
        <blockquote>
        We report on a certified parser generator for regular languages using the Agda programming language. Specifically, we programmed a transformation of regular expressions into a Boolean-matrix based representation of nondeterministic finite automata (NFAs). And we proved (in Agda) that a string matches a regular expression if and only if the NFA accepts it. The proof of the if-part is effectively a function turning acceptance of a string into a parse tree while the only-if part gives a function turning rejection into a proof of impossibility of a parse tree.
        </blockquote>
    *   Similar language definition as predicate but via an inductive type of regular expressions and another of membership proofs.
    *   Uses boolean matrices to represent NFA.
        "We parse strings with nondeterministic finite automata and represent them in terms of Boolean matrices."
        I'd like to understand this technique, and consider replacing the booleans with propositions.

*   [*Regular Expressions in Agda*]\:
    *   Similar to my work in some ways, but `ν` and `δ` are *defined* on regular expressions instead of proved.
    *   It's a short paper, but I'm unsure what the authors really proved.
    *   In the conclusion section:
        <blockquote>
        However, we note a particular defficiency in our program. That is the inability to prove the non-membership of some string in a given language. Indeed, we prove membership by constructing an element of the dependent data type `x ∈⌣⟦E⟧` in doing this we have to be able to construct an element of the datatype e0 = e/a at each step of the induction, to do a complete pattern matching we need to include the cases when this construction fails (i.e. the `Nothing` case). The fact that we couldn’t construct an element of the datatype doesn’t execulde the possibility that `e′` is a derviative of `e` to a since `e′` might be semanticaly equivalent to `e/a` but syntactically different.
        </blockquote>

*   [*Certified Context-Free Parsing: A formalisation of Valiant's Algorithm in Agda]
*   [*A theory of changes for higher-order languages---incrementalizing λ-calculi by static differentiation*] also used dependent types, though de-emphasized in the paper.
*   Derivatives of data types, starting with Brzozowski.
    Show it to be a special case.
*   AD
*   Convolution
*   *A play on regular expressions*.
    Doesn't seem very relevant.
*   [*A constructive theory of regular languages in Coq*]\:
    <blockquote>
    We present a formal constructive theory of regular languages consisting of about 1400 lines of Coq/Ssreflect. As representations we consider regular expressions, deterministic and nondeterministic automata, and Myhill and Nerode partitions. We construct computable functions translating between these representations and show that equivalence of representations is decidable. We also establish the usual closure properties, give a minimization algorithm for DFAs, and prove that minimal DFAs are unique up to state renaming. Our development profits much from Ssreflect’s support for finite types and graphs.
    </blockquote>

*   From agda-stdlib/CHANGELOG/v1.2.md:
    "A version of the `Reflects` idiom, as seen in SSReflect, has been introduced in `Relation.Nullary`."
    Apparently, SSReflect ("Small Scale Reflection") is a Coq extension.
    See [*The SSReflect proof language — Coq documentation*](https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html) and [*An introduction to small scale reflection in Coq*](https://jfr.unibo.it/article/view/1979).
*   [*Formal Languages, Formally and Coinductively*]\:
    <blockquote>
    Traditionally, formal languages are defined as sets of words. More recently, the alternative coalgebraic or coinductive representation as infinite tries, i.e., prefix trees branching over the alphabet, has been used to obtain compact and elegant proofs of classic results in language theory. In this article, we study this representation in the Isabelle proof assistant. We define regular operations on infinite tries and prove the axioms of Kleene algebra for those operations. Thereby, we exercise corecursion and coinduction and confirm the coinductive view being profitable in formalizations, as it improves over the set-of-words view with respect to proof automation.
    </blockquote>

*   [*Generic Level Polymorphic N-ary Functions*]
*   [*Fun with Semirings*]
*   Semiring parsing



[*Equational Reasoning about Formal Languages in Coalgebraic Style*]: http://www.cse.chalmers.se/~abela/jlamp17.pdf "paper by Andreas Abel (2017)"

[*Formal Languages, Formally and Coinductively*]: https://arxiv.org/abs/1611.09633 "paper by Dmitriy Traytel (2017)"

[*Proof Pearl: Regular Expression Equivalence and Relation Algebra*]: https://www21.in.tum.de/~krauss/papers/rexp.pdf "paper by Alexander Krauss and Tobias Nipkow (2012)"

[*Generic Level Polymorphic N-ary Functions*]: https://gallais.github.io/pdf/tyde19.pdf "paper by Guillaume Allais (2019)"

[*Fun with Semirings: A functional pearl on the abuse of linear algebra*]: http://stedolan.net/research/semirings.pdf "paper by Stephen Dolan (2013)"

[*Regular Expressions in Agda*]: https://itu.dk/people/basm/report.pdf "paper by Alexandre Agular and Bassel Mannaa (2009)"

[*Certified Context-Free Parsing: A formalisation of Valiant's Algorithm in Agda]: http://arxiv.org/abs/1601.07724 "paper by Jean-Philippe Bernardy and Patrik Jansson (2016)"

[*A theory of changes for higher-order languages---incrementalizing λ-calculi by static differentiation*]: http://inc-lc.github.io/resources/pldi14-ilc-author-final.pdf "paper by Yufei Cai, Paolo G. Giarrusso, Tillmann Rendel, and Klaus Ostermann (2014)"

[*Certified Parsing of Regular Languages*]: https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.571.724 "paper by Denis Firsov , Tarmo Uustalu"

[*Intrinsic Verification of a Regular Expression Matcher*]: http://cattheory.com/regexp2016.pdf "Joomy Korkut, Maksim Trifunovski, and Daniel R. Licata (2016)"

[*A Typed, Algebraic Approach to Parsing*]: https://www.cl.cam.ac.uk/~nk480/parsing.pdf "paper by Neel Krishnaswami and Jeremy Yallop (2019)"

[*Total parser combinators*]: http://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.html "paper by Nils Anders Danielsson (2015)"

[*A constructive theory of regular languages in Coq*]: https://www.ps.uni-saarland.de/~doczkal/regular/ConstructiveRegularLanguages.pdf "paper by Christian Doczkal, Jan-Oliver Kaiser, and Gert Smolka (2013)"

[*Combining predicate transformer semantics for effects: a case study in parsing regular languages*]: https://arxiv.org/abs/2005.00197 "paper by Anne Baanen Wouter Swierstra (2020)"

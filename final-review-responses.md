# ICFP 2021 Paper #87 final review responses

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

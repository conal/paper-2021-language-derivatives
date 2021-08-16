# ICFP talk

I generally don't write out my talks, but this time I did, since I'm recording it.

## Languages via type theory

Languages are often formalized as sets of strings.
Alternatively, we can consider a language to be a type-level predicate, that is a function that maps any string to a type of membership proofs.
Each inhabitant of a membership type is an explanation or parsing.
If there are no inhabitants, then the string is not in the language.

With this simple idea, we can easily define the usual building blocks of languages.
*[Reveal.]*

For instance, a string is in the union of `P` and `Q` when it's in `P` or in `Q`, so memberships are sum types, corresponding to logical disjunction.
Similarly, membership proofs for language intersections are products, corresponding to logical conjunction.

As a more interesting example, a string `w` is in the concatenation of languages `P` and `Q`, exactly when there are strings in `P` and `Q` that concatenate to `w`.
While precise and elegant, this definition does not tell us how to recognize or parse language concatenations, since the existential quantification is over infinitely many string pairs.

In case you're not used to Agda, let me point out a few things:

*   Bottom and top are the empty and singleton types.
    Logically, they correspond to falsity and truth.
*   The type `x ≡ y` has a single inhabitant when indeed `x` does equal `y` and otherwise is empty.
*   Sum types are written with disjoint union symbol.
*   Non-dependent product types are written with cross symbol.
*   Dependent products types are written with the exists symbol.

*[Reveal.]*
The puzzle addressed by this paper is how to bridge the gap between this non-computational specification and correct, computable parsing.

## Plan

Here's the plan:

*   First, we'll define a normal form for languages.
    The main idea is to use Brzozowski-style language derivatives at the level of types, which is to say propositions.

*   Next, prove lemmas relating this normal form to the usual building blocks of languages.

*   So far, everything is propositional rather than computable, that is at the level of types rather than computational inhabitants.
    The next step relates our language lemmas to decidable form.

*   Finally, we'll apply these insights in two ways to yield dual correct parsing implementations.

## Decomposing languages

Remembering that a language is a function from lists, let's consider each data constructor for lists, namely nil and cons:

*   Nullability of a language is the proposition that the language contains the empty string.
*   The derivative of a language `P` with respect to a leading character `a` is another language, consisting of the tails of the strings in `P` that start with `a`.
    The proofs that `w` is in `δ P a` are exactly the proofs that `a ∷ w` is in `P`.

The importance of these definitions comes from a simple fact with a simple inductive proof.
Given a language `P` and string, we can successively differentiate `P` with respect to characters in the string, resulting in a residual language.
The original language `P` contains the input string exactly if the residual language is nullable.

This theorem and its proof are very simple, as shown in the lower left of the slide.
Agda is quite liberal with names, and in this case, the name of the theorem is "`ν∘foldlδ`" with no spaces.

Note that everything on this slide applies not just to languages but more generally to functions from lists to anything.

## Language calculus

The next step in our plan to identify and prove a collection of lemmas that relate ν and δ to the standard language building blocks.

*[reveal]*

The ν lemmas on the left relate types and are equalities or isomorphisms.
The δ lemmas on the right relate languages and are equalities or extensional isomorphisms.

Agda proves the equalities automatically, simply by normalization.
The others take a bit of effort.
All proofs are in the paper's source code.

The style of these lemmas is important.
Each one reduces ν or δ of a standard language construction to ν and/or δ of simpler constructions.
The computable implementations that follow and their full correctness (including termination) are corollaries of these lemmas.

## Decidable types

Given a language and a candidate string, we can apply the language to the string to yield a type of proofs that the string is in the language.
Now we want to *construct* such a proof or show that one cannot exist.
We can express this goal as a decision data type.

A parser for a language is then a computable function that maps an arbitrary string to a decision about the string belonging to the language.

*[reveal]*

Isomorphisms appear in the language lemmas of the previous slide, so we'll need to know how they relate to decidability.
Fortunately, the answers are simple.
If two types are isomorphic, then a decision for one suffices to decide the other, since evidence of each can be mapped to evidence of the other.
Likewise for extensionally isomorphic predicates.

## Compositionally decidable types

While we cannot possibly decide *all* predicates, we can decide some of them, and we can do so compositionally.
Together with the isomorphism deciders from the previous slide, these compositional deciders cover all of the constructions appearing in the language calculus lemmas.
For instance, consider deciding the conjunction of `A` and `B`.
If we have proofs of each, we can pair those proofs to form a proof of the conjunction.
On the other hand, if we have a *disproof* of either, we can use it to construct a disproof of the conjunction.

## Reflections

Let's pause to reflect on where we are in the story.

*   The language decomposition theorem reduces membership to a succession of derivatives, followed by nullability.
*   Our language lemmas tell us how to decompose nullability and derivatives of languages to the same questions on simpler languages.
*   The resulting questions are all expressed in terms of propositions and predicates that happen to be compositionally decidable.

It looks like we're done: we just formulate the languages, compute derivatives and nullability, and apply the language lemmas.

However, we cannot simply apply the language lemmas by pattern matching, because languages are functions and so cannot be inspected structurally.

Exactly this same situation holds in differential calculus, since differentiation in that setting is also defined on functions and we have a collection of lemmas about derivatives for various formulations of functions, such as sums, products, trig functions, and compositions.
When we want to *compute* correct derivatives, there are two standard solutions, known as "symbolic" and "automatic" differentiation:

*   Symbolic differentiation represents functions structually and applies the differentiation rules by pattern matching.

*   Automatic differentiation represents differentiable functions as functions that compute their derivatives as well as their regular values.

We can apply these same strategies to languages.

## Regular expressions (inductive)

Applying the first strategy to languages leads to an inductive data type of regular expressions.
To keep a simple and rigorous connection to our original specification, we'll index this inductive data type by the type-level language it denotes.
Here I've kept the vocabulary the same, distinguishing type-level language building blocks by a module prefix that shows here as a small, lowered diamond.

Note that ν and δ here are decidable versions.
Correctness of parsing is guaranteed by the types of these two functions, so any definitions that type-check will suffice.

## Symbolic differentiation (column-major / patterns)

Given our inductive representation, we need only define ν and δ.
The definitions shown on this slide are systematically derived from the language lemmas shown earlier in the talk, using the compositional deciders.
The definitions are to be read in column-major order, that is, each column is one definition, given by pattern matching.

## Tries (coinductive)

Applying the second strategy to languages leads instead to a *coinductive* type of tries, which is an exact dual to the inductive structure of regular expressions.
The language operations are now defined functions instead of constructors, while ν and δ are now selectors instead of functions.
Again, correctness of parsing is guaranteed by the types, so any definitions that type-check will suffice.

## Automatic differentiation (row-major / copatterns)

Given our coinductive representation, we need only define the language building blocks.
The definitions shown on this slide are *also* systematically derived from the language lemmas shown earlier in the talk, using the compositional deciders.
This time, the definitions are to be read in row-major order, that is, each row is one definition, and is given by co-pattern matching.
Remember that this language representation is a pair of a ν and a δ, so a single definition gives both.

Here's the magical thing.
Compare this implementation with the previous one.
The code is exactly the same, but its interpretation changes, as signified by the syntax coloring, which the Agda compiler generates during typesetting.

## Summary

What pleases me most about this work:

*   First, there is the simple formal specification, uncomplicated by computability.

*   Second, the clear path of reasoning from propositionally defined languages to decidable parsing via decision types.

*   Finally, the duality of regular expressions and tries---paralleling to symbolic and automatic differentiation---using exactly the same code for parsing in both cases, though with dual interpretations.

## Also in the paper

There are more goodies in the paper.
I encourage you to give it a read.

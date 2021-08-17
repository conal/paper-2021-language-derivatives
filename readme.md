Paper: *Symbolic and Automatic Differentiation of Languages*.
To appear at ICFP 2021.

[See latest version of the paper (PDF), video, and slides (PDF) here.](http://conal.net/papers/language-derivatives/)
Comments appreciated as GitHub issues and pull requests or email (firstname@firstname.net).

There is also [an accompanying talk](http://conal.net/talks/language-derivatives.pdf).

[Reviews](reviews.md) and [my responses](response-to-reviews.md) are included in the repository, along with the [submitted version](icfp21-submitted.pdf) to which the reviews & responses refer.

Run "make" to compile the sources and typeset the paper.
The Agda code should work at least with [Agda](https://github.com/agda/agda) 2.6.1.3 and [agda-stdlib](https://github.com/agda/agda-stdlib) version 1.5.

**Abstract:**

> Formal languages are usually defined in terms of set theory. Choosing type theory instead gives us languages as type-level predicates over strings. Applying a language to a string yields a type whose elements are language membership proofs describing *how* a string parses in the language. The usual building blocks of languages (including union, concatenation, and Kleene closure) have precise and compelling specifications uncomplicated by operational strategies and are easily generalized to a few general domain-transforming and codomain-transforming operations on predicates.
> 
> A simple characterization of languages (and indeed functions from lists to any type) captures the essential idea behind language "differentiation" as used for recognizing languages, leading to a collection of lemmas about type-level predicates.
> These lemmas are the heart of two dual parsing implementations---using (inductive) regular expressions and (coinductive) tries---each containing the same code but in dual arrangements (with representation and primitive operations trading places).
> The regular expression version corresponds to symbolic differentiation, while the trie version corresponds to automatic differentiation.
> 
> The relatively easy-to-prove properties of type-level languages transfer almost effortlessly to the decidable implementations. In particular, despite the inductive and coinductive nature of regular expressions and tries respectively, we need neither inductive nor coinductive/bisumulation arguments to prove algebraic properties.


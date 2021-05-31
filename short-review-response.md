# Paper #87 review responses

## Review A

> My major concern is novelty, but unfortunately I am not familiar with the prior work. Given that I was a bit surprised by the absence of prior work, and that there were already so many papers on related topics, my rating is B. I might advocate for this paper more enthusiastically once novelty is confirmed.

We were surprised as well not to find formalized & mechanized connections between the simple, non-operational semantics of language specification and the dual decidable representations of regular expressions and tries.
Note also that proof relevance yields *parsing* (explanations) rather than mere recognition.
We are not aware of formalized (or even rigorous) accounts of *parsing* (as opposed to mere recognition) based on non-operational specification of languages and derivatives.
> It seems that in Fig. 1 "a language over an alphabet A" is not A^* but A^* -> Set l. This is at least nonstandard --- a standard definition should be A*. Explain the reason.

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

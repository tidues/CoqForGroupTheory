# CoqForGroupTheory
## The Problem
An attempt to prove this result in group theory with Coq:

If group `G` is finite, then for any element `a` in `G` there exist a positive integer `k` such that `a^k = e` where `e` is the identity element.

Same thing have been done before with Agda (a dependent typed language can be used also as a theorem prover) https://github.com/tidues/AgdaProofsForAbstractAlgebra.

## Main Contents
Starting with definition of groups, then I proved a bunch of basic properties after which the main theorem has been proved. An extra group notation simplifier is also created by encoding the group elements and operation into a type -- a technique called univserse. This can be used for prove by reflection in other proofs.

## Comparison between Coq and Agda
Compare with proving the same thing in agda, Coq is a much more maturer theorem prover, the tactics make the job of proving intuitive and compact. However agda is more transparent, that is in Agda proving a theorem and defining a function are exactly the same thing, which let you feel the meaning of Curry-Howard isomorphism, and also in Agda the syntax is much more closed to Haskell. Overall, learning how to prove in Agda makes you a better user in coq. But if I just want to get the job done, and if it is a complicated one, I'll probabily go with Coq. 

But don't forget Agda is a general programming language while Coq is more focused in proof assistant, and writing programs with dependent typed language like Agda is really a huge fun. I hope this can be adopted by Haskell eventually, since it makes a lot of tough jobs in Haskell ten times easier.

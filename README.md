# CoqForGroupTheory
An attempt to prove this result in group theory with coq:

If group `G` is finite, then for any element `a` in `G` there exist a positive integer `k` such that `a^k = e` where `e` is the identity element.

Same thing have been done before with Agda (a dependent typed language can be used also as a theorem prover) https://github.com/tidues/AgdaProofsForAbstractAlgebra.

Starting with definition of groups, then I proved a bunch of basic properties after which the main theorem has been proved. An extra group notation simplifier is also created by encoding the group elements and operation into a type -- a technique called univserse. This can be used for prove by reflection in later proofs.

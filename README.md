The theory is a formalization of the OCL type system,
its abstract syntax and expression typing rules [1].
The theory does not define a concrete syntax and a semantics.
In contrast to Featherweight OCL [2],
it is based on a deep embedding approach. The type system is defined
from scratch, it is not based on the Isabelle HOL type system.

The Safe OCL distincts nullable and non-nullable types. Also
the theory gives a formal definition of safe navigation
operations [3]. The Safe OCL typing rules
are much stricter than rules given in the OCL specification.
It allows one to catch more errors on a type checking phase.

The type theory presented is four-layered: classes, basic types,
generic types, errorable types. We introduce the following new types:
non-nullable types (*τ[1]*), nullable types (*τ[?]*),
*OclSuper*. *OclSuper* is a supertype of all other types
(basic types, collections, tuples). This type allows us to define
a total supremum function, so types form an upper semilattice.
It allows us to define rich expression typing rules in an elegant manner.

The Preliminaries Chapter of the theory defines a number of
helper lemmas for transitive closures and tuples. It defines also
a generic object model independent from OCL. It allows one to use
the theory as a reference for formalization of analogous languages.

[1] Object Management Group, "Object Constraint Language (OCL).
Version 2.4", Feb. 2014. http://www.omg.org/spec/OCL/2.4/.

[2] A. D. Brucker, F. Tuong, and B. Wolff, "Featherweight OCL: A proposal
for a machine-checked formal semantics for OCL 2.5", Archive of Formal
Proofs, Jan. 2014. http://isa-afp.org/entries/Featherweight_OCL.html,
Formal proof development.

[3] E. D. Willink, "Safe navigation in OCL" in Proceedings of the 15th
International Workshop on OCL and Textual Modeling co-located with
18th International Conference on Model Driven Engineering Languages
and Systems (MoDELS 2015), Ottawa, Canada, September 28, 2015.
(A. D. Brucker, M. Egea, M. Gogolla, and F. Tuong, eds.), vol. 1512 of
CEUR Workshop Proceedings, pp. 81-88, CEUR-WS.org, 2015.

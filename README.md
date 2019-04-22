Here is an informal outline of the theory.

# Abstract

The theory is a formalization of the OCL type system,
its abstract syntax and expression typing rules [1].
The theory does not define a concrete syntax and a semantics.
In contrast to Featherweight OCL [2], it is based on a deep embedding
approach. The type system is defined from scratch, it is not based
on the Isabelle HOL type system.

The Safe OCL distincts nullable and null-free types, errorable
and error-free types. Also the theory gives a formal definition
of safe navigation operations [3]. The Safe OCL typing rules
are much stricter than rules given in the OCL specification.
It allows one to catch more errors on a type checking phase.

The type theory presented is four-layered: classes, ordinary types,
nullable types, errorable types. We introduce the following new types:
error-free null-free types (*τ[1]*), error-free nullable types (*τ[?]*),
errorable null-free types (*τ[1!]*), errorable nullable types (*τ[?!]*).
Also we define formaly the *Map* type, which is absent in the current
OCL specification. We define *OclAny* as a supertype of all other types
(basic types, collections, tuples). This type allows us to define
a total supremum function, so types form an upper semilattice.
It allows us to define rich expression typing rules in an elegant manner.

The theory defines expression normalization rules for implicit types,
safe navigation operations, navigation short-hands, and closure body.

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

# Types

## Definition

Ordinary and nullable types:

<pre>
datatype (plugins del: size) 'a type =
  OclAny
| OclVoid

| Boolean
| Real
| Integer
| UnlimitedNatural
| String

| Enum "'a enum_type"
| ObjectType 'a ("⟨_⟩<sub>𝒯</sub>")
| Tuple "telem ⇀<sub>f</sub> 'a type<sub>N</sub>"

| Collection "'a type<sub>N</sub>"
| Set "'a type<sub>N</sub>"
| OrderedSet "'a type<sub>N</sub>"
| Bag "'a type<sub>N</sub>"
| Sequence "'a type<sub>N</sub>"

| Map "'a type<sub>N</sub>" "'a type<sub>N</sub>"

and 'a type<sub>N</sub> =
  Required "'a type" ("_[1]")
| Optional "'a type" ("_[?]")
</pre>

Errorable types:

<pre>
datatype 'a errorable ("_<sub>E</sub>") =
  ErrorFree 'a
| Errorable 'a

type_synonym 'a type<sub>NE</sub> = "'a type<sub>N</sub> errorable"
</pre>

## Subtype Relation

<pre>
lemma type_less_left_simps:
  "OclAny < σ = False"
  "OclVoid < σ = (σ ≠ OclVoid)"

  "Boolean < σ = (σ = OclAny)"
  "Real < σ = (σ = OclAny)"
  "Integer < σ = (σ = OclAny ∨ σ = Real)"
  "UnlimitedNatural < σ = (σ = OclAny)"
  "String < σ = (σ = OclAny)"

  "Enum ℰ < σ = (σ = OclAny)"
  "ObjectType 𝒞 < σ = (∃𝒟. σ = OclAny ∨ σ = ObjectType 𝒟 ∧ 𝒞 < 𝒟)"
  "Tuple π < σ = (∃ξ.
      σ = OclAny ∨
      σ = Tuple ξ ∧ strict_subtuple (≤) π ξ)"

  "Collection τ < σ = (∃φ.
      σ = OclAny ∨
      σ = Collection φ ∧ τ < φ)"
  "Set τ < σ = (∃φ.
      σ = OclAny ∨
      σ = Collection φ ∧ τ ≤ φ ∨
      σ = Set φ ∧ τ < φ)"
  "OrderedSet τ < σ = (∃φ.
      σ = OclAny ∨
      σ = Collection φ ∧ τ ≤ φ ∨
      σ = OrderedSet φ ∧ τ < φ)"
  "Bag τ < σ = (∃φ.
      σ = OclAny ∨
      σ = Collection φ ∧ τ ≤ φ ∨
      σ = Bag φ ∧ τ < φ)"
  "Sequence τ < σ = (∃φ.
      σ = OclAny ∨
      σ = Collection φ ∧ τ ≤ φ ∨
      σ = Sequence φ ∧ τ < φ)"

  "Map τ φ < σ = (∃ρ υ.
      σ = OclAny ∨
      σ = Map ρ υ ∧ τ = ρ ∧ φ < υ ∨
      σ = Map ρ υ ∧ τ < ρ ∧ φ = υ ∨
      σ = Map ρ υ ∧ τ < ρ ∧ φ < υ)"
</pre>

<pre>
lemma type_less_right_simps:
  "τ < OclAny = (τ ≠ OclAny)"
  "τ < OclVoid = False"

  "τ < Boolean = (τ = OclVoid)"
  "τ < Real = (τ = Integer ∨ τ = OclVoid)"
  "τ < Integer = (τ = OclVoid)"
  "τ < UnlimitedNatural = (τ = OclVoid)"
  "τ < String = (τ = OclVoid)"

  "τ < Enum ℰ = (τ = OclVoid)"
  "τ < ObjectType 𝒟 = (∃𝒞. τ = ObjectType 𝒞 ∧ 𝒞 < 𝒟 ∨ τ = OclVoid)"
  "τ < Tuple ξ = (∃π. τ = Tuple π ∧ strict_subtuple (≤) π ξ ∨ τ = OclVoid)"

  "τ < Collection σ = (∃φ.
      τ = Collection φ ∧ φ < σ ∨
      τ = Set φ ∧ φ ≤ σ ∨
      τ = OrderedSet φ ∧ φ ≤ σ ∨
      τ = Bag φ ∧ φ ≤ σ ∨
      τ = Sequence φ ∧ φ ≤ σ ∨
      τ = OclVoid)"
  "τ < Set σ = (∃φ. τ = Set φ ∧ φ < σ ∨ τ = OclVoid)"
  "τ < OrderedSet σ = (∃φ. τ = OrderedSet φ ∧ φ < σ ∨ τ = OclVoid)"
  "τ < Bag σ = (∃φ. τ = Bag φ ∧ φ < σ ∨ τ = OclVoid)"
  "τ < Sequence σ = (∃φ. τ = Sequence φ ∧ φ < σ ∨ τ = OclVoid)"

  "τ < Map ρ υ = (∃φ σ.
      τ = Map φ σ ∧ φ = ρ ∧ σ < υ ∨
      τ = Map φ σ ∧ φ < ρ ∧ σ = υ ∨
      τ = Map φ σ ∧ φ < ρ ∧ σ < υ ∨
      τ = OclVoid)"
</pre>

<pre>
lemma type⇩N_less_left_simps:
  "Required ρ < σ = (∃υ.
      σ = Required υ ∧ ρ < υ ∨
      σ = Optional υ ∧ ρ ≤ υ)"
  "Optional ρ < σ = (∃υ.
      σ = Optional υ ∧ ρ < υ)"
</pre>

<pre>
lemma type⇩N_less_right_simps:
  "τ < Required υ = (∃ρ.
      τ = Required ρ ∧ ρ < υ)"
  "τ < Optional υ = (∃ρ.
      τ = Required ρ ∧ ρ ≤ υ ∨
      τ = Optional ρ ∧ ρ < υ)"
</pre>

<pre>
lemma errorable_less_left_simps:
  "ErrorFree ρ < σ = (∃υ.
      σ = ErrorFree υ ∧ ρ < υ ∨
      σ = Errorable υ ∧ ρ ≤ υ)"
  "Errorable ρ < σ = (∃υ.
      σ = Errorable υ ∧ ρ < υ)"
</pre>

<pre>
lemma errorable_less_right_simps:
  "τ < ErrorFree υ = (∃ρ.
      τ = ErrorFree ρ ∧ ρ < υ)"
  "τ < Errorable υ = (∃ρ.
      τ = ErrorFree ρ ∧ ρ ≤ υ ∨
      τ = Errorable ρ ∧ ρ < υ)"
</pre>

## Upper Semilattice of Types

<pre>
fun type_sup (infixl "⊔<sub>T</sub>" 65)
and type_sup<sub>N</sub> (infixl "⊔<sub>N</sub>" 65) where
  "OclAny ⊔<sub>T</sub> σ = OclAny"
| "OclVoid ⊔<sub>T</sub> σ = σ"

| "Boolean ⊔<sub>T</sub> σ = (case σ
    of Boolean ⇒ Boolean
     | OclVoid ⇒ Boolean
     | _ ⇒ OclAny)"
| "Real ⊔<sub>T</sub> σ = (case σ
    of Real ⇒ Real
     | Integer ⇒ Real
     | OclVoid ⇒ Real
     | _ ⇒ OclAny)"
| "Integer ⊔<sub>T</sub> σ = (case σ
    of Real ⇒ Real
     | Integer ⇒ Integer
     | OclVoid ⇒ Integer
     | _ ⇒ OclAny)"
| "UnlimitedNatural ⊔<sub>T</sub> σ = (case σ
    of UnlimitedNatural ⇒ UnlimitedNatural
     | OclVoid ⇒ UnlimitedNatural
     | _ ⇒ OclAny)"
| "String ⊔<sub>T</sub> σ = (case σ
    of String ⇒ String
     | OclVoid ⇒ String
     | _ ⇒ OclAny)"

| "Enum ℰ ⊔<sub>T</sub> σ = (case σ
    of Enum ℰ' ⇒ if ℰ = ℰ' then Enum ℰ else OclAny
     | OclVoid ⇒ Enum ℰ
     | _ ⇒ OclAny)"
| "⟨𝒞⟩<sub>𝒯</sub> ⊔<sub>T</sub> σ = (case σ
    of ⟨𝒟⟩<sub>𝒯</sub> ⇒ ⟨𝒞 ⊔ 𝒟⟩<sub>𝒯</sub>
     | OclVoid ⇒ ⟨𝒞⟩<sub>𝒯</sub>
     | _ ⇒ OclAny)"
| "Tuple π ⊔<sub>T</sub> σ = (case σ
    of Tuple ξ ⇒ Tuple (fmmerge_fun (⊔<sub>N</sub>) π ξ)
     | OclVoid ⇒ Tuple π
     | _ ⇒ OclAny)"

| "Collection τ ⊔<sub>T</sub> σ = (case σ
    of Collection ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Set ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OrderedSet ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Bag ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Sequence ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OclVoid ⇒ Collection τ
     | _ ⇒ OclAny)"
| "Set τ ⊔<sub>T</sub> σ = (case σ
    of Collection ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Set ρ ⇒ Set (τ ⊔<sub>N</sub> ρ)
     | OrderedSet ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Bag ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Sequence ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OclVoid ⇒ Set τ
     | _ ⇒ OclAny)"
| "OrderedSet τ ⊔<sub>T</sub> σ = (case σ
    of Collection ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Set ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OrderedSet ρ ⇒ OrderedSet (τ ⊔<sub>N</sub> ρ)
     | Bag ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Sequence ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OclVoid ⇒ OrderedSet τ
     | _ ⇒ OclAny)"
| "Bag τ ⊔<sub>T</sub> σ = (case σ
    of Collection ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Set ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OrderedSet ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Bag ρ ⇒ Bag (τ ⊔<sub>N</sub> ρ)
     | Sequence ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OclVoid ⇒ Bag τ
     | _ ⇒ OclAny)"
| "Sequence τ ⊔<sub>T</sub> σ = (case σ
    of Collection ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Set ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | OrderedSet ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Bag ρ ⇒ Collection (τ ⊔<sub>N</sub> ρ)
     | Sequence ρ ⇒ Sequence (τ ⊔<sub>N</sub> ρ)
     | OclVoid ⇒ Sequence τ
     | _ ⇒ OclAny)"

| "Map τ σ ⊔<sub>T</sub> φ = (case φ
    of Map ρ υ ⇒ Map (τ ⊔<sub>N</sub> ρ) (σ ⊔<sub>N</sub> υ)
     | OclVoid ⇒ Map τ σ
     | _ ⇒ OclAny)"

| "Required τ ⊔<sub>N</sub> σ = (case σ
    of Required ρ ⇒ Required (τ ⊔<sub>T</sub> ρ)
     | Optional ρ ⇒ Optional (τ ⊔<sub>T</sub> ρ))"
| "Optional τ ⊔<sub>N</sub> σ = (case σ
    of Required ρ ⇒ Optional (τ ⊔<sub>T</sub> ρ)
     | Optional ρ ⇒ Optional (τ ⊔<sub>T</sub> ρ))"
</pre>

<pre>
primrec sup_errorable where
  "ErrorFree τ ⊔ σ = (case σ
    of ErrorFree ρ ⇒ ErrorFree (τ ⊔ ρ)
     | Errorable ρ ⇒ Errorable (τ ⊔ ρ))"
| "Errorable τ ⊔ σ = (case σ
    of ErrorFree ρ ⇒ Errorable (τ ⊔ ρ)
     | Errorable ρ ⇒ Errorable (τ ⊔ ρ))"
</pre>

## Type Notation

| Notation                            | Meaning                                                                                       |
|:-----------------------------------:|-----------------------------------------------------------------------------------------------|
| τ                                   | a type with unspecified nullability and errorability                                          |
| τ[1]                                | a null-free and error-free type                                                               |
| τ[?]                                | a nullable and error-free type                                                                |
| τ[1!]                               | a null-free and errorable type                                                                |
| τ[?!]                               | a nullable and errorable type                                                                 |
| τ[!]                                | an errorable variant of a type *τ*                                                            |
| Collection<sub>k</sub>(τ)           | a collection type of a kind *k* with element type *τ*; *k* is optional                        |
| OrderedCollection<sub>k</sub>(τ)    | an ordered collection type of a kind *k* with element type *τ*; *k* is optional               |
| NonOrderedCollection<sub>k</sub>(τ) | a non-ordered collection type of a kind *k* with element type *τ*; *k* is optional            |
| UniqueCollection<sub>k</sub>(τ)     | an unqie collection type of a kind *k* with element type *τ*; *k* is optional                 |
| NonUniqueCollection<sub>k</sub>(τ)  | an non-unqie collection type of a kind *k* with element type *τ*; *k* is optional             |
| NonCollection()                     | a non-collection type                                                                         |
| Iterable(τ)                         | either a collection type of any kind with element type *τ*, or a map type with a key type *τ* |
| NonIterable()                       | a non-collection and non-map type                                                             |

Tuple, collection and map types can have elements only with error-free types.

# Typing

## Operations Typing

A strict operation is an operation that is defined for invalid source and
arguments and returns an invalid value if any of its source or arguments
is invalid.

A non-strict operation is an operation that either is not defined for
invalid source and arguments or returns a valid value for invalid source
or arguments.

A null-safe operation is an operation that is defined for a nullable
source.

All metaclass and type operations are non-strict, because neither
source nor argument types can be invalid. For these operations we
define rules for errorable types explicitly.

Most of the other operations are strict by default. The typing rules
for errorable source and arguments are defined implicitly. The only
exclusion from this rule is the following non-strict operations:
+ oclIsUndefined()
+ oclIsInvalid()
+ and
+ or
+ xor
+ implies

For non-strict operations, we specify typing rules for errorable types
explicitly.

Please take a note that most of the operations are undefined for nullable
types. This is a significant difference from the current version of
the OCL specification. The OCL specification allows operation invocation
with null sources and arguments with `invalid` result. We prohibit it.

### Metaclass Operations

`allInstances()` is not defined for errorable source types, because
a resulting collection can not contain `invalid`.

| Operation    | Source Type | Result Type  | Precondition      |
|--------------|:-----------:|:------------:|:-----------------:|
| allInstances | τ[1]        | Set(τ[1])[1] | finite_type τ     |
| allInstances | τ[?]        | Set(τ[?])[1] | finite_type τ     |

### Type Operations

`selectByKind()` and `selectByType()` are not defined for errorable
argument types, because a source collection can not contain `invalid`.

| Operation      | Source Type      | Argument Type | Result Type | Precondition                                                         |
|:--------------:|:----------------:|:-------------:|:-----------:|:--------------------------------------------------------------------:|
| oclAsType      | τ                | σ             | σ           | τ < σ                                                                |
| oclAsType      | τ                | σ             | σ[!]        | σ < τ                                                                |
| oclIsTypeOf    | τ                | σ             | Boolean[1]  | σ < τ ∧ error_free_null_free_type τ                                  |
| oclIsTypeOf    | τ                | σ             | Boolean[1!] | σ < τ ∧ ¬ error_free_null_free_type τ                                |
| oclIsKindOf    | τ                | σ             | Boolean[1]  | σ < τ ∧ error_free_null_free_type τ                                  |
| oclIsKindOf    | τ                | σ             | Boolean[1!] | σ < τ ∧ ¬ error_free_null_free_type τ                                |
| selectByKind   | τ                | σ             | υ           | τ ↪ Collection<sub>k</sub>(ρ)[1] ∧<br/>σ < ρ ∧<br/>error_free_type σ ∧<br/>υ ↩ Collection<sub>k</sub>(σ)[1] |
| selectByType   | τ                | σ             | υ           | τ ↪ Collection<sub>k</sub>(ρ)[1] ∧<br/>σ < ρ ∧<br/>error_free_type σ ∧<br/>υ ↩ Collection<sub>k</sub>(σ)[1] |

### OclAny Operations

`oclAsSet()` is not defined for errorable source types, because
a resulting collection can not contain `invalid`.

| Operation      | Source Type | Result Type  | Precondition              |
|:--------------:|:-----------:|:------------:|:-------------------------:|
| oclAsSet       | τ[1]        | Set(τ[1])[1] | τ[1] ↪ NonIterable()[1]   |
| oclAsSet       | τ[?]        | Set(τ[1])[1] | τ[?] ↪ NonIterable()[?]   |
| oclIsNew       | τ           | Boolean[1]   | τ ↪ ObjectType(𝒞)[_]     |
| oclIsUndefined | τ[?]        | Boolean[1]   |                           |
| oclIsUndefined | τ[1!]       | Boolean[1]   |                           |
| oclIsUndefined | τ[?!]       | Boolean[1]   |                           |
| oclIsInvalid   | τ[1!]       | Boolean[1]   |                           |
| oclIsInvalid   | τ[?!]       | Boolean[1]   |                           |
| toString       | τ           | String[1]    |                           |

| Operation      | Source Type | Argument Type | Result Type | Precondition        |
|:--------------:|:-----------:|:-------------:|:-----------:|:-------------------:|
| =              | τ           | σ             | Boolean[1]  | τ ≤ σ ∨ σ < τ       |
| <>             | τ           | σ             | Boolean[1]  | τ ≤ σ ∨ σ < τ       |

### Boolean Operations

| Operation      | Source Type | Result Type | Precondition        |
|:--------------:|:-----------:|:-----------:|:-------------------:|
| not            | τ           | τ           | τ ≤ Boolean[?!]     |

| Operation      | Source Type | Argument Type | Result Type | Precondition        |
|:--------------:|:-----------:|:-------------:|:-----------:|:-------------------:|
| and            | τ           | σ             | τ ⊔ σ       | τ ⊔ σ ≤ Boolean[?!] |
| or             | τ           | σ             | τ ⊔ σ       | τ ⊔ σ ≤ Boolean[?!] |
| xor            | τ           | σ             | τ ⊔ σ       | τ ⊔ σ ≤ Boolean[?!] |
| implies        | τ           | σ             | τ ⊔ σ       | τ ⊔ σ ≤ Boolean[?!] |

### Numeric Operations

| Operation      | Source Type         | Result Type | Precondition        |
|:--------------:|:-------------------:|:-----------:|:-------------------:|
| -              | Real[1]             | Real[1]     |                     |
| -              | Integer[1]          | Integer[1]  |                     |
| abs            | Real[1]             | Real[1]     |                     |
| abs            | Integer[1]          | Integer[1]  |                     |
| floor          | Real[1]             | Integer[1]  |                     |
| round          | Real[1]             | Integer[1]  |                     |
| toInteger      | UnlimitedNatural[1] | Integer[1!] |                     |

| Operation      | Source Type | Argument Type | Result Type          | Precondition                                            |
|:--------------:|:-----------:|:-------------:|:--------------------:|:-------------------------------------------------------:|
| +              | τ           | σ             | τ ⊔ σ                | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| +              | τ           | σ             | UnlimitedNatural[1!] | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| -              | τ           | σ             | τ ⊔ σ                | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| *              | τ           | σ             | τ ⊔ σ                | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| *              | τ           | σ             | UnlimitedNatural[1!] | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| /              | τ           | σ             | Real[1!]             | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| /              | τ           | σ             | Real[1!]             | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| div            | τ           | σ             | Integer[1!]          | τ = Integer[1] ∧<br/>σ = Integer[1]                     |
| div            | τ           | σ             | UnlimitedNatural[1!] | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| mod            | τ           | σ             | Integer[1!]          | τ = Integer[1] ∧<br/>σ = Integer[1]                     |
| mod            | τ           | σ             | UnlimitedNatural[1!] | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| max            | τ           | σ             | τ ⊔ σ                | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| max            | τ           | σ             | UnlimitedNatural[1]  | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| min            | τ           | σ             | τ ⊔ σ                | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| min            | τ           | σ             | UnlimitedNatural[1]  | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| <              | τ           | σ             | Boolean[1]           | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| <              | τ           | σ             | Boolean[1]           | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| <=             | τ           | σ             | Boolean[1]           | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| <=             | τ           | σ             | Boolean[1]           | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| >              | τ           | σ             | Boolean[1]           | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| >              | τ           | σ             | Boolean[1]           | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |
| >=             | τ           | σ             | Boolean[1]           | Integer[1] ≤ τ ≤ Real[1] ∧<br/>Integer[1] ≤ σ ≤ Real[1] |
| >=             | τ           | σ             | Boolean[1]           | τ = UnlimitedNatural[1] ∧<br/>σ = UnlimitedNatural[1]   |

### String Operations

| Operation      | Source Type         | Result Type            | Precondition        |
|:--------------:|:-------------------:|:----------------------:|:-------------------:|
| size           | String[1]           | Integer[1]             |                     |
| characters     | String[1]           | Sequence(String[1])[1] |                     |
| toUpperCase    | String[1]           | String[1]              |                     |
| toLowerCase    | String[1]           | String[1]              |                     |
| toBoolean      | String[1]           | Boolean[1!]            |                     |
| toReal         | String[1]           | Real[1!]               |                     |
| toInteger      | String[1]           | Integer[1!]            |                     |

| Operation        | Source Type | Argument Type | Result Type | Precondition         |
|:----------------:|:-----------:|:-------------:|:-----------:|:--------------------:|
| concat           | String[1]   | String[1]     | String[1]   |                      |
| equalsIgnoreCase | String[1]   | String[1]     | Boolean[1]  |                      |
| <                | String[1]   | String[1]     | Boolean[1]  |                      |
| <=               | String[1]   | String[1]     | Boolean[1]  |                      |
| >                | String[1]   | String[1]     | Boolean[1]  |                      |
| >=               | String[1]   | String[1]     | Boolean[1]  |                      |
| indexOf          | String[1]   | String[1]     | Integer[1]  |                      |
| at               | String[1]   | Integer[1]    | String[1!]  |                      |

| Operation        | Source Type | Argument Type | 2nd Argument Type | Result Type | Precondition     |
|:----------------:|:-----------:|:-------------:|:-----------------:|:-----------:|:----------------:|
| substring        | String[1]   | Integer[1]    | Integer[1]        | String[1!]  |                  |

### Iterable Operations

| Operation      | Source Type                  | Result Type                                 | Precondition                                         |
|:--------------:|:----------------------------:|:-------------------------------------------:|:----------------------------------------------------:|
| size           | Iterable(τ)[1]               | Integer[1]                                  |                                                      |
| isEmpty        | Iterable(τ)[1]               | Boolean[1]                                  |                                                      |
| notEmpty       | Iterable(τ)[1]               | Boolean[1]                                  |                                                      |
| max            | Collection(τ)[1]             | τ                                           | a binary operation "max" is defined for τ            |
| min            | Collection(τ)[1]             | τ                                           | a binary operation "min" is defined for τ            |
| sum            | Collection(τ)[1]             | τ                                           | a binary operation "+" is defined for τ              |
| asSet          | Collection(τ)[1]             | Set(τ)[1]                                   |                                                      |
| asOrderedSet   | Collection(τ)[1]             | OrderedSet(τ)[1]                            |                                                      |
| asBag          | Collection(τ)[1]             | Bag(τ)[1]                                   |                                                      |
| asSequence     | Collection(τ)[1]             | Sequence(τ)[1]                              |                                                      |
| flatten        | Collection<sub>k</sub>(τ)[1] | Collection<sub>k</sub>(to_single_type τ)[1] |                                                      |
| first          | OrderedCollection(τ)[1]      | τ[!]                                        |                                                      |
| last           | OrderedCollection(τ)[1]      | τ[!]                                        |                                                      |
| reverse        | OrderedCollection(τ)[1]      | OrderedCollection(τ)[1]                     |                                                      |
| keys           | Map(τ, σ)[1]                 | Set(τ)[1]                                   |                                                      |
| values         | Map(τ, σ)[1]                 | Bag(τ)[1]                                   |                                                      |

| Operation           | Source Type                  | Argument Type           | Result Type                           | Precondition                                         |
|:-------------------:|:----------------------------:|:-----------------------:|:-------------------------------------:|:----------------------------------------------------:|
| count               | Collection(τ)[1]             | σ                       | Integer[1]                            | σ ≤ to_optional_type_nested τ                        |
| includes            | Iterable(τ)[1]               | σ                       | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| excludes            | Iterable(τ)[1]               | σ                       | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| includesValue       | Map(τ, ρ)[1]                 | σ                       | Boolean[1]                            | σ ≤ to_optional_type_nested ρ                        |
| excludesValue       | Map(τ, ρ)[1]                 | σ                       | Boolean[1]                            | σ ≤ to_optional_type_nested ρ                        |
| includesAll         | Iterable(τ)[1]               | Collection(σ)[1]        | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| excludesAll         | Iterable(τ)[1]               | Collection(σ)[1]        | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| includesMap         | Map(τ, ρ)[1]                 | Map(σ, υ)[1]            | Boolean[1]                            | σ ≤ to_optional_type_nested τ∧<br/>υ ≤ to_optional_type_nested ρ |
| excludesMap         | Map(τ, ρ)[1]                 | Map(σ, υ)[1]            | Boolean[1]                            | σ ≤ to_optional_type_nested τ∧<br/>υ ≤ to_optional_type_nested ρ |
| product             | Collection(τ)[1]             | Collection(σ)[1]        | Set(Tuple(first: τ, second: σ)[1])[1] |                                                      |
| union               | Set(τ)[1]                    | Set(σ)[1]               | Set(τ ⊔ σ)[1]                         |                                                      |
| union               | Set(τ)[1]                    | Bag(σ)[1]               | Bag(τ ⊔ σ)[1]                         |                                                      |
| union               | Bag(τ)[1]                    | Set(σ)[1]               | Bag(τ ⊔ σ)[1]                         |                                                      |
| union               | Bag(τ)[1]                    | Bag(σ)[1]               | Bag(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Set(τ)[1]                    | Set(σ)[1]               | Set(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Set(τ)[1]                    | Bag(σ)[1]               | Set(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Bag(τ)[1]                    | Set(σ)[1]               | Set(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Bag(τ)[1]                    | Bag(σ)[1]               | Bag(τ ⊔ σ)[1]                         |                                                      |
| -                   | Set(τ)[1]                    | Set(σ)[1]               | Set(τ)[1]                             | τ ≤ σ ∨ σ ≤ τ                                        |
| symmetricDifference | Set(τ)[1]                    | Set(σ)[1]               | Set(τ ⊔ σ)[1]                         |                                                      |
| including           | Collection<sub>k</sub>(τ)[1] | σ                       | Collection<sub>k</sub>(τ ⊔ σ)[1]      |                                                      |
| excluding           | Collection(τ)[1]             | σ                       | Collection(τ)[1]                      | σ ≤ τ                                                |
| includingAll        | Collection<sub>k</sub>(τ)[1] | Collection(σ)[1]        | Collection<sub>k</sub>(τ ⊔ σ)[1]      |                                                      |
| excludingAll        | Collection(τ)[1]             | Collection(σ)[1]        | Collection(τ)[1]                      | σ ≤ τ                                                |
| includingMap        | Map(τ, ρ)[1]                 | Map(σ, υ)[1]            | Map(τ ⊔ σ, ρ ⊔ υ)[1]                  |                                                      |
| excludingMap        | Map(τ, ρ)[1]                 | Map(σ, υ)[1]            | Map(τ, ρ)[1]                          | σ ≤ τ ∧ υ ≤ ρ                                        |
| append              | OrderedCollection(τ)[1]      | σ                       | OrderedCollection(τ)[1]               | σ ≤ τ                                                |
| prepend             | OrderedCollection(τ)[1]      | σ                       | OrderedCollection(τ)[1]               | σ ≤ τ                                                |
| appendAll           | OrderedCollection(τ)[1]      | OrderedCollection(σ)[1] | OrderedCollection(τ)[1]               | σ ≤ τ                                                |
| prependAll          | OrderedCollection(τ)[1]      | OrderedCollection(σ)[1] | OrderedCollection(τ)[1]               | σ ≤ τ                                                |
| at                  | OrderedCollection(τ)[1]      | Integer[1]              | τ[!]                                  |                                                      |
| at                  | Map(τ, ρ)[1]                 | σ                       | ρ[!]                                  | σ ≤ τ                                                |
| indexOf             | OrderedCollection(τ)[1]      | σ                       | Integer[1]                            | σ ≤ τ                                                |

| Operation        | Source Type             | Argument Type | 2nd Argument Type | Result Type              | Precondition    |
|:----------------:|:-----------------------:|:-------------:|:-----------------:|:------------------------:|:---------------:|
| insertAt         | OrderedCollection(τ)[1] | Integer[1]    | σ                 | OrderedCollection(τ)[1!] | σ ≤ τ           |
| subOrderedSet    | OrderedSet(τ)[1]        | Integer[1]    | Integer[1]        | OrderedSet(τ)[1!]        |                 |
| subSequence      | Sequence(τ)[1]          | Integer[1]    | Integer[1]        | Sequence(τ)[1!]          |                 |
| includes         | Map(τ, ρ)[1]            | σ             | υ                 | Boolean[1]               | σ ≤ τ ∧ υ ≤ ρ   |
| excludes         | Map(τ, ρ)[1]            | σ             | υ                 | Boolean[1]               | σ ≤ τ ∧ υ ≤ ρ   |
| including        | Map(τ, ρ)[1]            | σ             | υ                 | Map(τ ⊔ σ, ρ ⊔ υ)[1]     |                 |
| excluding        | Map(τ, ρ)[1]            | σ             | υ                 | Map(τ, ρ)[1]             | σ ≤ τ ∧ υ ≤ ρ   |

## Expressions Typing

<pre>
inductive typing :: "('a :: ocl_object_model) type<sub>NE</sub> env ⇒ 'a expr ⇒ 'a type<sub>NE</sub> ⇒ bool"
       ("(1_/ ⊢<sub>E</sub>/ (_ :/ _))" [51,51,51] 50)
      and collection_part_typing ("(1_/ ⊢<sub>C</sub>/ (_ :/ _))" [51,51,51] 50)
      and iterator_typing ("(1_/ ⊢<sub>I</sub>/ (_ :/ _))" [51,51,51] 50)
      and expr_list_typing ("(1_/ ⊢<sub>L</sub>/ (_ :/ _))" [51,51,51] 50) where

― ‹Primitive Literals›

 NullLiteralT:
  "Γ ⊢<sub>E</sub> NullLiteral : OclVoid[?]"
|BooleanLiteralT:
  "Γ ⊢<sub>E</sub> BooleanLiteral c : Boolean[1]"
|RealLiteralT:
  "Γ ⊢<sub>E</sub> RealLiteral c : Real[1]"
|IntegerLiteralT:
  "Γ ⊢<sub>E</sub> IntegerLiteral c : Integer[1]"
|UnlimitedNaturalLiteralT:
  "Γ ⊢<sub>E</sub> UnlimitedNaturalLiteral c : UnlimitedNatural[1]"
|StringLiteralT:
  "Γ ⊢<sub>E</sub> StringLiteral c : String[1]"
|EnumLiteralT:
  "has_literal enm lit ⟹
   Γ ⊢<sub>E</sub> EnumLiteral enm lit : (Enum enm)[1]"

― ‹Tuple Literals›

|TupleLiteralNilT:
  "Γ ⊢<sub>E</sub> TupleLiteral [] : (Tuple fmempty)[1]"
|TupleLiteralConsT:
  "Γ ⊢<sub>E</sub> tuple_literal_element_expr el : τ ⟹
   tuple_literal_element_type el = Some σ ⟹
   τ ≤ σ ⟹
   ρ ↩ Tuple([tuple_literal_element_name el ↦⇩f σ])[1] ⟹
   Γ ⊢<sub>E</sub> TupleLiteral elems : υ ⟹
   Γ ⊢<sub>E</sub> TupleLiteral (el # elems) : ρ ⊔ υ"

― ‹Collection Literals›

|CollectionLiteralNilT:
  "k ≠ CollectionKind ⟹
   σ ↩ Collection<sub>k</sub>(OclVoid[1])[1] ⟹
   Γ ⊢<sub>E</sub> CollectionLiteral k [] : σ"
|CollectionLiteralConsT:
  "k ≠ CollectionKind ⟹
   Γ ⊢<sub>C</sub> x : τ ⟹
   σ ↩ Collection<sub>k</sub>(τ)[1] ⟹
   Γ ⊢<sub>E</sub> CollectionLiteral k xs : ρ ⟹
   Γ ⊢<sub>E</sub> CollectionLiteral k (x # xs) : σ ⊔ ρ"

|CollectionPartItemT:
  "Γ ⊢<sub>E</sub> a : τ ⟹
   Γ ⊢<sub>C</sub> CollectionItem a : τ"
|CollectionPartRangeT:
  "Γ ⊢<sub>E</sub> a : Integer[1] ⟹ Γ ⊢<sub>E</sub> b : Integer[1] ⟹
   Γ ⊢<sub>C</sub> CollectionRange a b : Integer[1]"
|LowerErrorableCollectionPartRangeT:
  "Γ ⊢<sub>E</sub> a : Integer[1!] ⟹ Γ ⊢<sub>E</sub> b : Integer[1] ⟹
   Γ ⊢<sub>C</sub> CollectionRange a b : Integer[1!]"
|UpperErrorableCollectionPartRangeT:
  "Γ ⊢<sub>E</sub> a : Integer[1] ⟹ Γ ⊢<sub>E</sub> b : Integer[1!] ⟹
   Γ ⊢<sub>C</sub> CollectionRange a b : Integer[1!]"
|ErrorableCollectionPartRangeT:
  "Γ ⊢<sub>E</sub> a : Integer[1!] ⟹ Γ ⊢<sub>E</sub> b : Integer[1!] ⟹
   Γ ⊢<sub>C</sub> CollectionRange a b : Integer[1!]"

― ‹Map Literals›

|MapNilT:
  "τ ↩ Map(OclVoid[1], OclVoid[1])[1] ⟹
   Γ ⊢<sub>E</sub> MapLiteral [] : τ"
|MapConsT:
  "Γ ⊢<sub>E</sub> map_literal_element_key x : τ ⟹
   Γ ⊢<sub>E</sub> map_literal_element_value x : σ ⟹
   ρ ↩ Map(τ, σ)[1] ⟹
   Γ ⊢<sub>E</sub> MapLiteral xs : υ ⟹
   Γ ⊢<sub>E</sub> MapLiteral (x # xs) : ρ ⊔ υ"

― ‹Misc Expressions›

|LetT:
  "Γ ⊢<sub>E</sub> init : σ ⟹
   σ ≤ τ ⟹
   Γ(v ↦⇩f τ) ⊢<sub>E</sub> body : ρ ⟹
   Γ ⊢<sub>E</sub> Let v (Some τ) init body : ρ"
|VarT:
  "fmlookup Γ v = Some τ ⟹
   Γ ⊢<sub>E</sub> Var v : τ"
|IfT:
  "Γ ⊢<sub>E</sub> cnd : Boolean[1] ⟹
   Γ ⊢<sub>E</sub> thn : σ ⟹
   Γ ⊢<sub>E</sub> els : ρ ⟹
   Γ ⊢<sub>E</sub> If cnd thn els : σ ⊔ ρ"
|ErrorableIfT:
  "Γ ⊢<sub>E</sub> cnd : Boolean[1!] ⟹
   Γ ⊢<sub>E</sub> thn : σ ⟹
   Γ ⊢<sub>E</sub> els : ρ ⟹
   Γ ⊢<sub>E</sub> If cnd thn els : (σ ⊔ ρ)[!]"

― ‹Call Expressions›

|MetaOperationCallT:
  "mataop_type τ op σ ⟹
   Γ ⊢<sub>E</sub> MetaOperationCall τ op : σ"

|StaticOperationCallT:
  "Γ ⊢<sub>L</sub> params : π ⟹
   static_operation τ op π oper ⟹
   ¬ fBex (fset_of_list π) errorable_type ⟹
   Γ ⊢<sub>E</sub> StaticOperationCall τ op params : oper_type oper"
|ErrorableStaticOperationCallT:
  "Γ ⊢<sub>L</sub> params : π ⟹
   static_operation τ op π oper ⟹
   fBex (fset_of_list π) errorable_type ⟹
   Γ ⊢<sub>E</sub> StaticOperationCall τ op params : (oper_type oper)[!]"

|TypeOperationCallT:
  "Γ ⊢<sub>E</sub> a : τ ⟹
   typeop_type k op τ σ ρ ⟹
   Γ ⊢<sub>E</sub> TypeOperationCall a k op σ : ρ"

|OperationCallT:
  "Γ ⊢<sub>E</sub> src : τ ⟹
   Γ ⊢<sub>L</sub> params : π ⟹
   op_type op k τ π σ ⟹
   Γ ⊢<sub>E</sub> OperationCall src k op params : σ"

|AttributeCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒞⟩<sub>𝒯</sub>[1] ⟹
   attribute 𝒞 prop 𝒟 τ ⟹
   Γ ⊢<sub>E</sub> AttributeCall src prop : τ"
|ErrorableAttributeCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒞⟩<sub>𝒯</sub>[1!] ⟹
   attribute 𝒞 prop 𝒟 τ ⟹
   Γ ⊢<sub>E</sub> AttributeCall src prop : τ[!]"

|AssociationEndCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒞⟩<sub>𝒯</sub>[1] ⟹
   association_end 𝒞 from role 𝒟 end ⟹
   Γ ⊢<sub>E</sub> AssociationEndCall src from role : assoc_end_type end"
|ErrorableAssociationEndCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒞⟩<sub>𝒯</sub>[1!] ⟹
   association_end 𝒞 from role 𝒟 end ⟹
   Γ ⊢<sub>E</sub> AssociationEndCall src from role : (assoc_end_type end)[!]"

|AssociationClassCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒞⟩<sub>𝒯</sub>[1] ⟹
   referred_by_association_class 𝒞 from 𝒜 𝒟 ⟹
   Γ ⊢<sub>E</sub> AssociationClassCall src from 𝒜 : class_assoc_type 𝒜"
|ErrorableAssociationClassCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒞⟩<sub>𝒯</sub>[1!] ⟹
   referred_by_association_class 𝒞 from 𝒜 𝒟 ⟹
   Γ ⊢<sub>E</sub> AssociationClassCall src from 𝒜 : (class_assoc_type 𝒜)[!]"

|AssociationClassEndCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒜⟩<sub>𝒯</sub>[1] ⟹
   association_class_end 𝒜 role end ⟹
   Γ ⊢<sub>E</sub> AssociationClassEndCall src role : class_assoc_end_type end"
|ErrorableAssociationClassEndCallT:
  "Γ ⊢<sub>E</sub> src : ⟨𝒜⟩<sub>𝒯</sub>[1!] ⟹
   association_class_end 𝒜 role end ⟹
   Γ ⊢<sub>E</sub> AssociationClassEndCall src role : (class_assoc_end_type end)[!]"

|TupleElementCallT:
  "Γ ⊢<sub>E</sub> src : (Tuple π)[1] ⟹
   fmlookup π elem = Some τ ⟹
   Γ ⊢<sub>E</sub> TupleElementCall src elem : ErrorFree τ"
|ErrorableTupleElementCallT:
  "Γ ⊢<sub>E</sub> src : (Tuple π)[1!] ⟹
   fmlookup π elem = Some τ ⟹
   Γ ⊢<sub>E</sub> TupleElementCall src elem : Errorable τ"

― ‹Iterator Expressions›

|CollectionLoopT:
  "Γ ⊢<sub>E</sub> src : τ ⟹
   τ ↪ Collection(σ)[1] ⟹
   σ ≤ its_ty ⟹
   list_all (λit. snd it = None) its ⟹
   Γ ++⇩f iterators its its_ty ⊢<sub>E</sub> body : ρ ⟹
   Γ ⊢<sub>I</sub> (src, its, (Some its_ty, None), body) : (τ, σ, ρ)"
|MapLoopT:
  "Γ ⊢<sub>E</sub> src : τ ⟹
   τ ↪ Map(σ, υ)[1] ⟹
   σ ≤ its_key_ty ⟹
   υ ≤ its_val_ty ⟹
   Γ ++⇩f iterators its its_key_ty ++⇩f coiterators its its_val_ty ⊢<sub>E</sub> body : ρ ⟹
   Γ ⊢<sub>I</sub> (src, its, (Some its_key_ty, Some its_val_ty), body) : (τ, σ, ρ)"

|IterateT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, Let res (Some res_t) res_init body) : (τ, σ, ρ) ⟹
   ρ ≤ res_t ⟹
   Γ ⊢<sub>E</sub> IterateCall src its its_ty res (Some res_t) res_init body : ρ"

|AnyIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢<sub>E</sub> AnyIterationCall src its its_ty body : σ[!]"
|ClosureIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   τ ↪ Collection<sub>k</sub>(σ)[1] ⟹
   ρ ↪ Collection<sub>k</sub>(φ)[1] ⟹
   φ ≤ σ ⟹
   υ ↩ UniqueCollection<sub>k</sub>(σ)[1] ⟹
   Γ ⊢<sub>E</sub> ClosureIterationCall src its its_ty body : υ"

|CollectionCollectIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   to_single_type ρ ρ' ⟹
   τ ↪ Collection<sub>k</sub>(σ)[1] ⟹
   υ ↩ NonUniqueCollection<sub>k</sub>(ρ')[1] ⟹
   Γ ⊢<sub>E</sub> CollectIterationCall src its its_ty body : υ"
|MapCollectIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   to_single_type ρ ρ' ⟹
   τ ↪ Map(_, _)[1] ⟹
   υ ↩ Bag(ρ')[1] ⟹
   Γ ⊢<sub>E</sub> CollectIterationCall src its its_ty body : υ"

|CollectByIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   υ ↩ Map(σ, ρ)[1] ⟹
   Γ ⊢<sub>E</sub> CollectByIterationCall src its its_ty body : υ"

|CollectionCollectNestedIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   τ ↪ Collection<sub>k</sub>(σ)[1] ⟹
   υ ↩ NonUniqueCollection<sub>k</sub>(ρ)[1] ⟹
   Γ ⊢<sub>E</sub> CollectNestedIterationCall src its its_ty body : υ"
|MapCollectNestedIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   τ ↪ Map(υ, _)[1] ⟹
   φ ↩ Map(υ, ρ)[1] ⟹
   Γ ⊢<sub>E</sub> CollectNestedIterationCall src its its_ty body : φ"

|ExistsIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   ρ ≤ Boolean[?!] ⟹
   Γ ⊢<sub>E</sub> ExistsIterationCall src its its_ty body : ρ"
|ForAllIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   ρ ≤ Boolean[?!] ⟹
   Γ ⊢<sub>E</sub> ForAllIterationCall src its its_ty body : ρ"
|OneIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢<sub>E</sub> OneIterationCall src its its_ty body : Boolean[1]"
|IsUniqueIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   Γ ⊢<sub>E</sub> IsUniqueIterationCall src its its_ty body : Boolean[1]"
|SelectIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢<sub>E</sub> SelectIterationCall src its its_ty body : τ"
|RejectIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢<sub>E</sub> RejectIterationCall src its its_ty body : τ"
|SortedByIterationT:
  "Γ ⊢<sub>I</sub> (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   τ ↪ Collection<sub>k</sub>(σ)[1] ⟹
   υ ↩ OrderedCollection<sub>k</sub>(σ)[1] ⟹
   Γ ⊢<sub>E</sub> SortedByIterationCall src its its_ty body : υ"

― ‹Expression Lists›

|ExprListNilT:
  "Γ ⊢<sub>L</sub> [] : []"
|ExprListConsT:
  "Γ ⊢<sub>E</sub> expr : τ ⟹
   Γ ⊢<sub>L</sub> exprs : π ⟹
   Γ ⊢<sub>L</sub> expr # exprs : τ # π"
</pre>

# Normalization

The following variables are used in the table:
+ `x` is a non-nullable single or tuple value,
+ `n` is a nullable single or tuple value,
+ `xs` is a non-nullable iterable value of non-nullable values,
+ `ns` is a non-nullable iterable value of nullable values. 
+ `nxs` is a nullable iterable value of non-nullable values,
+ `nns` is a nullable iterable value of nullable values. 

The following type variables are used in the table:
+ T[1] is a non-nullable variant of a value's type,
+ S[1] is a non-nullable variant of a iterable value's type.


| Original Expression  | Normalized Closure Body                                       | Note |
|:--------------------:|:-------------------------------------------------------------:|:----:|
| `src->closure(x)`    | `src->closure(x.oclAsSet())`                                  |      |
| `src->closure(n)`    | `src->closure(n.oclAsSet())`                                  |      |
| `src?->closure(x)`   | `src?->closure(x.oclAsSet())`                                 |      |
| `src?->closure(n)`   | `src?->closure(n.oclAsSet())`                                 |      |
| `src->closure(xs)`   | `src->closure(xs)`                                            |      |
| `src->closure(ns)`   | `src->closure(ns)`                                            |      |
| `src->closure(nxs)`  | `src->closure(nxs)`                                           |      |
| `src->closure(nns)`  | `src->closure(nns)`                                           |      |
| `src?->closure(xs)`  | `src->closure(xs)`                                            |      |
| `src?->closure(ns)`  | `src->closure(ns->selectByKind(T[1]))`                        |      |
| `src?->closure(nxs)` | `src->closure(if nxs <> null then nxs.oclAsType(S[1]) else Collection<sub>k</sub>(T)[1] endif)` |      |
| `src?->closure(nns)` | `src->closure(if nns <> null then nns.oclAsType(S[1])->selectByKind(T[1]) else Collection<sub>k</sub>(T)[1] endif)` |      |


| Original Expression | Normalized Expression                                         | Note |
|:-------------------:|:-------------------------------------------------------------:|:----:|
| `x.op()`            | `x.op()`                                                      |      |
| `n.op()`            | `n.op()`                                                      | (1)  |
| `x?.op()`           | &ndash;                                                       |      |
| `n?.op()`           | `if n <> null then n.oclAsType(T[1]).op() else null endif`    | (2)  |
| `x->op()`           | `x.oclAsSet()->op()`                                          |      |
| `n->op()`           | `n.oclAsSet()->op()`                                          |      |
| `x?->op()`          | &ndash;                                                       |      |
| `n?->op()`          | &ndash;                                                       |      |
|                     |                                                               |      |
| `xs.op()`           | <code>xs->collect(x &#124; x.op())</code>                     |      |
| `ns.op()`           | <code>ns->collect(n &#124; n.op())</code>                     | (1)  |
| `xs?.op()`          | &ndash;                                                       |      |
| `ns?.op()`          | <code>ns->selectByKind(T[1])->collect(x &#124; x.op())</code> |      |
| `xs->op()`          | `xs->op()`                                                    |      |
| `ns->op()`          | `ns->op()`                                                    |      |
| `xs?->op()`         | &ndash;                                                       |      |
| `ns?->op()`         | `ns->selectByKind(T[1])->op()`                                |      |
|                     |                                                               |      |
| `nxs.op()`          | &ndash;                                                       |      |
| `nns.op()`          | &ndash;                                                       |      |
| `nxs?.op()`         | <code>if nxs &lt;> null then nxs.oclAsType(S[1])->collect(x &#124; x.op()) else null endif</code>                     |      |
| `nns?.op()`         | <code>if nns &lt;> null then nns.oclAsType(S[1])->selectByKind(T[1])->collect(x &#124; x.op()) else null endif</code> |      |
| `nxs->op()`         | `nxs->op()`                                                   | (1)  |
| `nns->op()`         | `nns->op()`                                                   | (1)  |
| `nxs?->op()`        | `if nxs <> null then nxs.oclAsType(S[1])->op() else null endif`            |      |
| `nns?->op()`        | `if nns <> null then nns.oclAsType(S[1])->selectByKind(T[1])->op() else null endif` |      |

(1) The resulting expression will be ill-typed if the operation is unsafe.
An unsafe operation is an operation which is not well-typed for a nullable
source.

(2) It would be a good idea to prohibit such a transformation
for safe operations. A safe operation is an operation which is well-typed
for a nullable source. However, it is hard to define safe operations
formally considering operations overloading, complex relations between
operation parameters types (please see the typing rules for the equality
operator), and user-defined operations.

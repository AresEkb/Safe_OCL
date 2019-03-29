Here is an informal outline of the theory.

# Abstract

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

# 2. Types

## 2.1. Definition

<pre>
datatype 'a type =
  OclAny
| OclVoid

| Boolean
| Real
| Integer
| UnlimitedNatural
| String

| ObjectType 'a ("⟨_⟩<sub>𝒯</sub>" [0] 1000)
| Enum "'a enum"

| Collection "'a type<sub>N</sub>"
| Set "'a type<sub>N</sub>"
| OrderedSet "'a type<sub>N</sub>"
| Bag "'a type<sub>N</sub>"
| Sequence "'a type<sub>N</sub>"

| Tuple "telem ⇀<sub>f</sub> 'a type<sub>N</sub>"

and 'a type<sub>N</sub> =
  Required "'a type" ("_[1]<sub>N</sub>" [1000] 1000)
| Optional "'a type" ("_[?]<sub>N</sub>" [1000] 1000)
</pre>

## Subtype Relation

The subtype relation is a transitive closure of the following relation:

<pre>
inductive subtype :: "'a::order type ⇒ 'a type ⇒ bool" (infix "⊏" 65)
      and subtype<sub>N</sub> :: "'a type<sub>N</sub> ⇒ 'a type<sub>N</sub> ⇒ bool" (infix "⊏<sub>N</sub>" 65) where

― ‹Basic Types›

  "OclVoid ⊏ Boolean"
| "OclVoid ⊏ UnlimitedNatural"
| "OclVoid ⊏ String"
| "OclVoid ⊏ ⟨𝒞⟩<sub>𝒯</sub>"
| "OclVoid ⊏ Enum ℰ"

| "UnlimitedNatural ⊏ Integer"
| "Integer ⊏ Real"
| "𝒞 < 𝒟 ⟹ ⟨𝒞⟩<sub>𝒯</sub> ⊏ ⟨𝒟⟩<sub>𝒯</sub>"

| "Boolean ⊏ OclAny"
| "Real ⊏ OclAny"
| "String ⊏ OclAny"
| "⟨𝒞⟩<sub>𝒯</sub> ⊏ OclAny"
| "Enum ℰ ⊏ OclAny"

― ‹Collection Types›

| "OclVoid ⊏ Set OclVoid[1]<sub>N</sub>"
| "OclVoid ⊏ OrderedSet OclVoid[1]<sub>N</sub>"
| "OclVoid ⊏ Bag OclVoid[1]<sub>N</sub>"
| "OclVoid ⊏ Sequence OclVoid[1]<sub>N</sub>"

| "τ ⊏<sub>N</sub> σ ⟹ Collection τ ⊏ Collection σ"
| "τ ⊏<sub>N</sub> σ ⟹ Set τ ⊏ Set σ"
| "τ ⊏<sub>N</sub> σ ⟹ OrderedSet τ ⊏ OrderedSet σ"
| "τ ⊏<sub>N</sub> σ ⟹ Bag τ ⊏ Bag σ"
| "τ ⊏<sub>N</sub> σ ⟹ Sequence τ ⊏ Sequence σ"

| "Set τ ⊏ Collection τ"
| "OrderedSet τ ⊏ Collection τ"
| "Bag τ ⊏ Collection τ"
| "Sequence τ ⊏ Collection τ"

| "Collection OclAny[?]<sub>N</sub> ⊏ OclAny"

― ‹Tuple Types›

| "OclVoid ⊏ Tuple π"
| "strict_subtuple (λτ σ. τ ⊏<sub>N</sub> σ ∨ τ = σ) π ξ ⟹
   Tuple π ⊏ Tuple ξ"
| "Tuple π ⊏ OclAny"

― ‹Nullable Types›

| "τ ⊏ σ ⟹ Required τ ⊏<sub>N</sub> Required σ"
| "τ ⊏ σ ⟹ Optional τ ⊏<sub>N</sub> Optional σ"
| "Required τ ⊏<sub>N</sub> Optional τ"
</pre>

## 2.4. Upper Semilattice of Types

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
     | UnlimitedNatural ⇒ Real
     | OclVoid ⇒ Real
     | _ ⇒ OclAny)"
| "Integer ⊔<sub>T</sub> σ = (case σ
    of Real ⇒ Real
     | Integer ⇒ Integer
     | UnlimitedNatural ⇒ Integer
     | OclVoid ⇒ Integer
     | _ ⇒ OclAny)"
| "UnlimitedNatural ⊔<sub>T</sub> σ = (case σ
    of Real ⇒ Real
     | Integer ⇒ Integer
     | UnlimitedNatural ⇒ UnlimitedNatural
     | OclVoid ⇒ UnlimitedNatural
     | _ ⇒ OclAny)"
| "String ⊔<sub>T</sub> σ = (case σ
    of String ⇒ String
     | OclVoid ⇒ String
     | _ ⇒ OclAny)"

| "⟨𝒞⟩<sub>𝒯</sub> ⊔<sub>T</sub> σ = (case σ
    of ⟨𝒟⟩<sub>𝒯</sub> ⇒ ⟨𝒞 ⊔ 𝒟⟩<sub>𝒯</sub>
     | OclVoid ⇒ ⟨𝒞⟩<sub>𝒯</sub>
     | _ ⇒ OclAny)"
| "Enum ℰ ⊔<sub>T</sub> σ = (case σ
    of Enum ℰ' ⇒ if ℰ = ℰ' then Enum ℰ else OclAny
     | OclVoid ⇒ Enum ℰ
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

| "Tuple π ⊔<sub>T</sub> σ = (case σ
    of Tuple ξ ⇒ Tuple (fmmerge_fun (⊔<sub>N</sub>) π ξ)
     | OclVoid ⇒ Tuple π
     | _ ⇒ OclAny)"

| "Required τ ⊔<sub>N</sub> σ = (case σ
    of Required ρ ⇒ Required (τ ⊔<sub>T</sub> ρ)
     | Optional ρ ⇒ Optional (τ ⊔<sub>T</sub> ρ))"
| "Optional τ ⊔<sub>N</sub> σ = (case σ
    of Required ρ ⇒ Optional (τ ⊔<sub>T</sub> ρ)
     | Optional ρ ⇒ Optional (τ ⊔<sub>T</sub> ρ))"
</pre>

# 3. Erorrable Types

## 3.1. Generic Errorable Type

<pre>
datatype 'a errorable_type ("_<sub>E</sub>" [21] 21) =
  ErrorFree 'a
| Errorable 'a

fun less_errorable_type where
  "ErrorFree τ < ErrorFree σ = (τ < σ)"
| "Errorable τ < ErrorFree σ = False"
| "ErrorFree τ < Errorable σ = (τ ≤ σ)"
| "Errorable τ < Errorable σ = (τ < σ)"

fun less_eq_errorable_type where
  "ErrorFree τ ≤ ErrorFree σ = (τ ≤ σ)"
| "Errorable τ ≤ ErrorFree σ = False"
| "ErrorFree τ ≤ Errorable σ = (τ ≤ σ)"
| "Errorable τ ≤ Errorable σ = (τ ≤ σ)"

fun sup_errorable_type where
  "ErrorFree τ ⊔ σ = (case σ
    of ErrorFree ρ ⇒ ErrorFree (τ ⊔ ρ)
     | Errorable ρ ⇒ Errorable (τ ⊔ ρ))"
| "Errorable τ ⊔ σ = (case σ
    of ErrorFree ρ ⇒ Errorable (τ ⊔ ρ)
     | Errorable ρ ⇒ Errorable (τ ⊔ ρ))"
</pre>

## 3.2. OCL Errorable Type

| Notation | Meaning                                              |
|:--------:|------------------------------------------------------|
| τ[1]     | a null-free and error-free type                      |
| τ[?]     | a nullable and error-free type                       |
| τ[1!]    | a null-free and errorable type                       |
| τ[?!]    | a nullable and errorable type                        |
| τ        | a type with unspecified nullability and errorability |
| τ[!]     | an errorable variant of a type τ                     |

Collection and tuple types can have elements only with error-free types.

# Typing

## Operation Typing

Most of the operations are strict. If a source expression or any argument
of a strict operation is invalid then the operation result is invalid too.
If a source expression or any argument of a strict operation has an
errorable type then a result type of the opertation is errorable too.
This rule implicitly applies to all strict operations.

A non-strict operation is an operation which either return a non-invalid
value for invalid arguments, or is not defined for invalid arguments.

The following operations are non-strict:
+ allInstances()
+ selectByKind()
+ selectByType()
+ oclAsSet()
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
with null sources and arguments with *invalid* result.

### Metaclass Operations

*allInstances()* is not defined for errorable source types, because
a resulting collection can not contain *invalid*.

| Operation    | Source Type | Result Type  | Precondition      |
|--------------|:-----------:|:------------:|:-----------------:|
| allInstances | τ[1]        | Set(τ[1])[1] | is_finite_type τ  |
| allInstances | τ[?]        | Set(τ[?])[1] | is_finite_type τ  |

### Type Operations

*selectByKind()* and *selectByType()* are not defined for errorable
argument types, because a source collection can not contain *invalid*.

| Operation      | Source Type      | Argument Type | Result Type | Precondition                                                         |
|:--------------:|:----------------:|:-------------:|:-----------:|:--------------------------------------------------------------------:|
| oclAsType      | τ                | σ             | σ[!]        | σ < τ                                                                |
| oclAsType      | τ                | σ             | σ[!]        | τ < σ<br/>is_unsafe_cast τ σ                                         |
| oclAsType      | τ                | σ             | σ           | τ < σ<br/>¬ is_unsafe_cast τ σ                                       |
| oclIsTypeOf    | τ[1]             | σ             | Boolean[1]  | σ < τ[1]                                                             |
| oclIsTypeOf    | τ[?]             | σ             | Boolean[1!] | σ < τ[?]                                                             |
| oclIsKindOf    | τ[1]             | σ             | Boolean[1]  | σ < τ[1]                                                             |
| oclIsKindOf    | τ[?]             | σ             | Boolean[1!] | σ < τ[?]                                                             |
| selectByKind   | τ[1]             | σ[1]          | υ           | element_type τ[1] ρ<br/>σ[1] < ρ<br/>update_element_type τ[1] σ[1] υ |
| selectByKind   | τ[1]             | σ[?]          | υ           | element_type τ[1] ρ<br/>σ[?] < ρ<br/>update_element_type τ[1] σ[?] υ |
| selectByKind   | τ[1!]            | σ[1]          | υ[!]        | element_type τ[1] ρ<br/>σ[1] < ρ<br/>update_element_type τ[1] σ[1] υ |
| selectByKind   | τ[1!]            | σ[?]          | υ[!]        | element_type τ[1] ρ<br/>σ[?] < ρ<br/>update_element_type τ[1] σ[?] υ |
| selectByType   | τ[1]             | σ[1]          | υ           | element_type τ[1] ρ<br/>σ[1] < ρ<br/>update_element_type τ[1] σ[1] υ |
| selectByType   | τ[1]             | σ[?]          | υ           | element_type τ[1] ρ<br/>σ[?] < ρ<br/>update_element_type τ[1] σ[?] υ |
| selectByType   | τ[1!]            | σ[1]          | υ[!]        | element_type τ[1] ρ<br/>σ[1] < ρ<br/>update_element_type τ[1] σ[1] υ |
| selectByType   | τ[1!]            | σ[?]          | υ[!]        | element_type τ[1] ρ<br/>σ[?] < ρ<br/>update_element_type τ[1] σ[?] υ |

### OclAny Operations

*oclAsSet()* is not defined for errorable source types, because
a resulting collection can not contain *invalid*.

| Operation      | Source Type | Result Type  | Precondition              |
|:--------------:|:-----------:|:------------:|:-------------------------:|
| oclAsSet       | τ[1]        | Set(τ[1])[1] | ¬ is_collection_type τ[1] |
| oclAsSet       | τ[?]        | Set(τ[1])[1] | ¬ is_collection_type τ[?] |
| oclIsNew       | τ           | Boolean[1]   | is_object_type τ          |
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
| -              | UnlimitedNatural[1] | Integer[1]  |                     |
| abs            | Real[1]             | Real[1]     |                     |
| abs            | Integer[1]          | Integer[1]  |                     |
| floor          | Real[1]             | Integer[1]  |                     |
| round          | Real[1]             | Integer[1]  |                     |
| toInteger      | UnlimitedNatural[1] | Integer[1!] |                     |

| Operation      | Source Type | Argument Type | Result Type | Precondition                                                                  |
|:--------------:|:-----------:|:-------------:|:-----------:|:-----------------------------------------------------------------------------:|
| +              | τ           | σ             | τ ⊔ σ       | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| -              | τ           | σ             | Real[1]     | τ ⊔ σ = Real[1]                                                               |
| -              | τ           | σ             | Integer[1]  | UnlimitedNatural[1] ≤ τ ≤ Integer[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Integer[1] |
| *              | τ           | σ             | τ ⊔ σ       | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| /              | τ           | σ             | Real[1!]    | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| div            | τ           | σ             | (τ ⊔ σ)[!]  | UnlimitedNatural[1] ≤ τ ≤ Integer[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Integer[1] |
| mod            | τ           | σ             | (τ ⊔ σ)[!]  | UnlimitedNatural[1] ≤ τ ≤ Integer[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Integer[1] |
| max            | τ           | σ             | τ ⊔ σ       | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| min            | τ           | σ             | τ ⊔ σ       | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| <              | τ           | σ             | Boolean[1]  | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| <=             | τ           | σ             | Boolean[1]  | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| >              | τ           | σ             | Boolean[1]  | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |
| >=             | τ           | σ             | Boolean[1]  | UnlimitedNatural[1] ≤ τ ≤ Real[1]<br/>UnlimitedNatural[1] ≤ σ ≤ Real[1]       |

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

| Operation        | Source Type | Argument Type | Result Type | Precondition                         |
|:----------------:|:-----------:|:-------------:|:-----------:|:------------------------------------:|
| concat           | String[1]   | String[1]     | String[1]   |                                      |
| equalsIgnoreCase | String[1]   | String[1]     | String[1]   |                                      |
| <                | String[1]   | String[1]     | Boolean[1]  |                                      |
| <=               | String[1]   | String[1]     | Boolean[1]  |                                      |
| >                | String[1]   | String[1]     | Boolean[1]  |                                      |
| >=               | String[1]   | String[1]     | Boolean[1]  |                                      |
| indexOf          | String[1]   | String[1]     | Integer[1]  |                                      |
| at               | String[1]   | σ             | String[1!]  | UnlimitedNatural[1] ≤ σ ≤ Integer[1] |

| Operation        | Source Type | Argument Type | 2nd Argument Type | Result Type | Precondition                                                                  |
|:----------------:|:-----------:|:-------------:|:-----------------:|:-----------:|:-----------------------------------------------------------------------------:|
| substring        | String[1]   | σ             | ρ                 | String[1!]  | UnlimitedNatural[1] ≤ σ ≤ Integer[1]<br/>UnlimitedNatural[1] ≤ ρ ≤ Integer[1] |

### Collection Operations

| Operation      | Source Type         | Result Type            | Precondition                                         |
|:--------------:|:-------------------:|:----------------------:|:----------------------------------------------------:|
| size           | Collection(τ)[1]    | Integer[1]             |                                                      |
| isEmpty        | Collection(τ)[1]    | Boolean[1]             |                                                      |
| notEmpty       | Collection(τ)[1]    | Boolean[1]             |                                                      |
| max            | Collection(τ)[1]    | τ                      | a binary operation "max" is defined for τ            |
| min            | Collection(τ)[1]    | τ                      | a binary operation "min" is defined for τ            |
| sum            | Collection(τ)[1]    | τ                      | a binary operation "+" is defined for τ              |
| asSet          | Collection(τ)[1]    | Set(τ)[1]              |                                                      |
| asOrderedSet   | Collection(τ)[1]    | OrderedSet(τ)[1]       |                                                      |
| asBag          | Collection(τ)[1]    | Bag(τ)[1]              |                                                      |
| asSequence     | Collection(τ)[1]    | Sequence(τ)[1]         |                                                      |
| flatten        | τ[1]                | σ[1]                   | inner_element_type τ ρ<br/>update_element_type τ ρ σ |
| first          | OrderdSet(τ)[1]     | τ[1!]                  |                                                      |
| first          | Sequence(τ)[1]      | τ[1!]                  |                                                      |
| last           | OrderdSet(τ)[1]     | τ[1!]                  |                                                      |
| last           | Sequence(τ)[1]      | τ[1!]                  |                                                      |
| reverse        | OrderedSet(τ)[1]    | OrderedSet(τ)[1]       |                                                      |
| reverse        | Sequence(τ)[1]      | Sequence(τ)[1]         |                                                      |

| Operation           | Source Type      | Argument Type    | Result Type                           | Precondition                                         |
|:-------------------:|:----------------:|:----------------:|:-------------------------------------:|:----------------------------------------------------:|
| includes            | Collection(τ)[1] | σ                | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| excludes            | Collection(τ)[1] | σ                | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| count               | Collection(τ)[1] | σ                | Integer[1]                            | σ ≤ to_optional_type_nested τ                        |
| includesAll         | Collection(τ)[1] | Collection(σ)[1] | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| excludesAll         | Collection(τ)[1] | Collection(σ)[1] | Boolean[1]                            | σ ≤ to_optional_type_nested τ                        |
| product             | Collection(τ)[1] | Collection(σ)[1] | Set(Tuple(first: τ, second: σ)[1])[1] |                                                      |
| union               | Set(τ)[1]        | Set(σ)[1]        | Set(τ ⊔ σ)[1]                         |                                                      |
| union               | Set(τ)[1]        | Bag(σ)[1]        | Bag(τ ⊔ σ)[1]                         |                                                      |
| union               | Bag(τ)[1]        | Set(σ)[1]        | Bag(τ ⊔ σ)[1]                         |                                                      |
| union               | Bag(τ)[1]        | Bag(σ)[1]        | Bag(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Set(τ)[1]        | Set(σ)[1]        | Set(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Set(τ)[1]        | Bag(σ)[1]        | Set(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Bag(τ)[1]        | Set(σ)[1]        | Set(τ ⊔ σ)[1]                         |                                                      |
| intersection        | Bag(τ)[1]        | Bag(σ)[1]        | Bag(τ ⊔ σ)[1]                         |                                                      |
| -                   | Set(τ)[1]        | Set(σ)[1]        | Set(τ)[1]                             | τ ≤ σ ∨ σ ≤ τ                                        |
| symmetricDifference | Set(τ)[1]        | Set(σ)[1]        | Set(τ ⊔ σ)[1]                         |                                                      |
| including           | τ[1]             | σ                | υ                                     | element_type τ ρ<br/>update_element_type τ (ρ ⊔ σ) υ |
| excluding           | τ[1]             | σ                | τ[1]                                  | element_type τ ρ<br/>σ ≤ ρ                           |
| append              | OrderedSet(τ)[1] | σ                | OrderedSet(τ)[1]                      | σ ≤ τ                                                |
| append              | Sequence(τ)[1]   | σ                | Sequence(τ)[1]                        | σ ≤ τ                                                |
| prepend             | OrderedSet(τ)[1] | σ                | OrderedSet(τ)[1]                      | σ ≤ τ                                                |
| prepend             | Sequence(τ)[1]   | σ                | Sequence(τ)[1]                        | σ ≤ τ                                                |
| at                  | OrderedSet(τ)[1] | σ                | τ[1!]                                 | UnlimitedNatural[1] ≤ σ ≤ Integer[1]                 |
| at                  | Sequence(τ)[1]   | σ                | τ[1!]                                 | UnlimitedNatural[1] ≤ σ ≤ Integer[1]                 |
| indexOf             | OrderedSet(τ)[1] | σ                | Integer[1]                            | σ ≤ τ                                                |
| indexOf             | Sequence(τ)[1]   | σ                | Integer[1]                            | σ ≤ τ                                                |

| Operation        | Source Type      | Argument Type | 2nd Argument Type | Result Type       | Precondition                                                                  |
|:----------------:|:----------------:|:-------------:|:-----------------:|:-----------------:|:-----------------------------------------------------------------------------:|
| insertAt         | OrderedSet(τ)[1] | σ             | ρ                 | OrderedSet(τ)[1!] | UnlimitedNatural[1] ≤ σ ≤ Integer[1]<br/>ρ ≤ τ                                |
| insertAt         | Sequence(τ)[1]   | σ             | ρ                 | Sequence(τ)[1!]   | UnlimitedNatural[1] ≤ σ ≤ Integer[1]<br/>ρ ≤ τ                                |
| subOrderedSet    | OrderedSet(τ)[1] | σ             | ρ                 | OrderedSet(τ)[1!] | UnlimitedNatural[1] ≤ σ ≤ Integer[1]<br/>UnlimitedNatural[1] ≤ ρ ≤ Integer[1] |
| subSequence      | Sequence(τ)[1]   | σ             | ρ                 | Sequence(τ)[1!]   | UnlimitedNatural[1] ≤ σ ≤ Integer[1]<br/>UnlimitedNatural[1] ≤ ρ ≤ Integer[1] |

## Expressions Typing

<pre>
inductive typing :: "('a :: ocl_object_model) type⇩N⇩E env ⇒ 'a expr ⇒ 'a type⇩N⇩E ⇒ bool"
       ("(1_/ ⊢⇩E/ (_ :/ _))" [51,51,51] 50)
      and collection_parts_typing ("(1_/ ⊢⇩C/ (_ :/ _))" [51,51,51] 50)
      and collection_part_typing ("(1_/ ⊢⇩P/ (_ :/ _))" [51,51,51] 50)
      and iterator_typing ("(1_/ ⊢⇩I/ (_ :/ _))" [51,51,51] 50)
      and expr_list_typing ("(1_/ ⊢⇩L/ (_ :/ _))" [51,51,51] 50) where

― ‹Primitive Literals›

 NullLiteralT:
  "Γ ⊢⇩E NullLiteral : OclVoid[?]"
|BooleanLiteralT:
  "Γ ⊢⇩E BooleanLiteral c : Boolean[1]"
|RealLiteralT:
  "Γ ⊢⇩E RealLiteral c : Real[1]"
|IntegerLiteralT:
  "Γ ⊢⇩E IntegerLiteral c : Integer[1]"
|UnlimitedNaturalLiteralT:
  "Γ ⊢⇩E UnlimitedNaturalLiteral c : UnlimitedNatural[1]"
|StringLiteralT:
  "Γ ⊢⇩E StringLiteral c : String[1]"
|EnumLiteralT:
  "has_literal enum lit ⟹
   Γ ⊢⇩E EnumLiteral enum lit : (Enum enum)[1]"

― ‹Collection Literals›

|SetLiteralT:
  "Γ ⊢⇩C prts : (ErrorFree τ) ⟹
   Γ ⊢⇩E CollectionLiteral SetKind prts : (Set τ)[1]"
|OrderedSetLiteralT:
  "Γ ⊢⇩C prts : (ErrorFree τ) ⟹
   Γ ⊢⇩E CollectionLiteral OrderedSetKind prts : (OrderedSet τ)[1]"
|BagLiteralT:
  "Γ ⊢⇩C prts : (ErrorFree τ) ⟹
   Γ ⊢⇩E CollectionLiteral BagKind prts : (Bag τ)[1]"
|SequenceLiteralT:
  "Γ ⊢⇩C prts : (ErrorFree τ) ⟹
   Γ ⊢⇩E CollectionLiteral SequenceKind prts : (Sequence τ)[1]"

― ‹We prohibit empty collection literals, because their type is unclear.
  We could use @{text "OclVoid[1]"} element type for empty collections, but
  the typing rules will give wrong types for nested collections, because,
  for example, @{text "OclVoid[1] ⊔ Set(Integer[1]) = OclSuper"}›

|CollectionPartsSingletonT:
  "Γ ⊢⇩P x : τ ⟹
   Γ ⊢⇩C [x] : τ"
|CollectionPartsListT:
  "Γ ⊢⇩P x : τ ⟹
   Γ ⊢⇩C y # xs : σ ⟹
   Γ ⊢⇩C x # y # xs : τ ⊔ σ"

|CollectionPartItemT:
  "Γ ⊢⇩E a : τ ⟹
   Γ ⊢⇩P CollectionItem a : τ"
|CollectionPartRangeT:
  "Γ ⊢⇩E a : τ ⟹
   Γ ⊢⇩E b : σ ⟹
   τ = UnlimitedNatural[1]─Integer[1] ⟹
   σ = UnlimitedNatural[1]─Integer[1] ⟹
   Γ ⊢⇩P CollectionRange a b : Integer[1]"

― ‹Tuple Literals›
― ‹We do not prohibit empty tuples, because it could be useful.
  @{text "Tuple()"} is a supertype of all other tuple types.›

|TupleLiteralNilT:
  "Γ ⊢⇩E TupleLiteral [] : (Tuple fmempty)[1]"
|TupleLiteralConsT:
  "Γ ⊢⇩E TupleLiteral elems : (Tuple ξ)[1] ⟹
   Γ ⊢⇩E tuple_literal_element_expr el : (ErrorFree τ) ⟹
   tuple_literal_element_type el = Some σ ⟹
   τ ≤ σ ⟹
   Γ ⊢⇩E TupleLiteral (el # elems) : (Tuple (ξ(tuple_literal_element_name el ↦⇩f σ)))[1]"

― ‹Misc Expressions›

|LetT:
  "Γ ⊢⇩E init : σ ⟹
   σ ≤ τ ⟹
   Γ(v ↦⇩f τ) ⊢⇩E body : ρ ⟹
   Γ ⊢⇩E Let v (Some τ) init body : ρ"
|VarT:
  "fmlookup Γ v = Some τ ⟹
   Γ ⊢⇩E Var v : τ"
|IfT:
  "Γ ⊢⇩E a : Boolean[1] ⟹
   Γ ⊢⇩E b : σ ⟹
   Γ ⊢⇩E c : ρ ⟹
   Γ ⊢⇩E If a b c : σ ⊔ ρ"

― ‹Call Expressions›

|MetaOperationCallT:
  "mataop_type τ op σ ⟹
   Γ ⊢⇩E MetaOperationCall τ op : σ"
|StaticOperationCallT:
  "Γ ⊢⇩L params : π ⟹
   static_operation τ op π oper ⟹
   Γ ⊢⇩E StaticOperationCall τ op params : oper_type oper"

|TypeOperationCallT:
  "Γ ⊢⇩E a : τ ⟹
   typeop_type k op τ σ ρ ⟹
   Γ ⊢⇩E TypeOperationCall a k op σ : ρ"

|AttributeCallT:
  "Γ ⊢⇩E src : ⟨𝒞⟩⇩𝒯[1] ⟹
   attribute 𝒞 prop 𝒟 τ ⟹
   Γ ⊢⇩E AttributeCall src DotCall prop : τ"
|AssociationEndCallT:
  "Γ ⊢⇩E src : ⟨𝒞⟩⇩𝒯[1] ⟹
   association_end 𝒞 from role 𝒟 end ⟹
   Γ ⊢⇩E AssociationEndCall src DotCall from role : assoc_end_type end"
|AssociationClassCallT:
  "Γ ⊢⇩E src : ⟨𝒞⟩⇩𝒯[1] ⟹
   referred_by_association_class 𝒞 from 𝒜 𝒟 ⟹
   Γ ⊢⇩E AssociationClassCall src DotCall from 𝒜 : class_assoc_type 𝒜"
|AssociationClassEndCallT:
  "Γ ⊢⇩E src : ⟨𝒜⟩⇩𝒯[1] ⟹
   association_class_end 𝒜 role end ⟹
   Γ ⊢⇩E AssociationClassEndCall src DotCall role : class_assoc_end_type end"
|OperationCallT:
  "Γ ⊢⇩E src : τ ⟹
   Γ ⊢⇩L params : π ⟹
   op_type op k τ π σ ⟹
   Γ ⊢⇩E OperationCall src k op params : σ"

|TupleElementCallT:
  "Γ ⊢⇩E src : σ ⟹
   tuple_element_type σ elem τ ⟹
   Γ ⊢⇩E TupleElementCall src DotCall elem : τ"

― ‹Iterator Expressions›

|IteratorT:
  "Γ ⊢⇩E src : τ ⟹
   element_type τ σ ⟹
   σ ≤ its_ty ⟹
   Γ ++⇩f fmap_of_list (map (λit. (it, its_ty)) its) ⊢⇩E body : ρ ⟹
   Γ ⊢⇩I (src, its, (Some its_ty), body) : (τ, σ, ρ)"

|IterateT:
  "Γ ⊢⇩I (src, its, its_ty, Let res (Some res_t) res_init body) : (τ, σ, ρ) ⟹
   ρ ≤ res_t ⟹
   Γ ⊢⇩E IterateCall src ArrowCall its its_ty res (Some res_t) res_init body : ρ"

|AnyIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢⇩E AnyIteratorCall src ArrowCall its its_ty body : σ"
|ClosureIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   (* По-моему тут ошибка, должен быть просто element_type? *)
   to_single_type ρ ρ' ⟹
   ρ' ≤ σ ⟹
   to_unique_collection_type τ υ ⟹
   Γ ⊢⇩E ClosureIteratorCall src ArrowCall its its_ty body : υ"
|CollectIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   to_nonunique_collection_type τ υ ⟹
   to_single_type ρ ρ' ⟹
   update_element_type υ ρ' φ ⟹
   Γ ⊢⇩E CollectIteratorCall src ArrowCall its its_ty body : φ"
|CollectNestedIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   to_nonunique_collection_type τ υ ⟹
   update_element_type υ ρ φ ⟹
   Γ ⊢⇩E CollectNestedIteratorCall src ArrowCall its its_ty body : φ"
|ExistsIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢⇩E ExistsIteratorCall src ArrowCall its its_ty body : ρ"
|ForAllIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢⇩E ForAllIteratorCall src ArrowCall its its_ty body : ρ"
|OneIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢⇩E OneIteratorCall src ArrowCall its its_ty body : Boolean[1]"
|IsUniqueIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   Γ ⊢⇩E IsUniqueIteratorCall src ArrowCall its its_ty body : Boolean[1]"
|SelectIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢⇩E SelectIteratorCall src ArrowCall its its_ty body : τ"
|RejectIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   ρ ≤ Boolean[?] ⟹
   Γ ⊢⇩E RejectIteratorCall src ArrowCall its its_ty body : τ"
|SortedByIteratorT:
  "Γ ⊢⇩I (src, its, its_ty, body) : (τ, σ, ρ) ⟹
   length its ≤ 1 ⟹
   to_ordered_collection_type τ υ ⟹
   Γ ⊢⇩E SortedByIteratorCall src ArrowCall its its_ty body : υ"

― ‹Expression Lists›

|ExprListNilT:
  "Γ ⊢⇩L [] : []"
|ExprListConsT:
  "Γ ⊢⇩E expr : τ ⟹
   Γ ⊢⇩L exprs : π ⟹
   Γ ⊢⇩L expr # exprs : τ # π"
</pre>

# Normalization


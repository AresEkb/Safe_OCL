(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Typing\<close>
theory OCL_Typing
  imports OCL_Object_Model OCL_Type_Helpers "HOL-Library.Transitive_Closure_Table"
begin

text \<open>
  The following rules are more restrictive than rules given in
  the OCL specification. This allows one to identify more errors
  in expressions. However, these restrictions may be revised if necessary.
  Perhaps some of them could be separated and should cause warnings
  instead of errors.\<close>

(*** Operations Typing ******************************************************)

section \<open>Operations Typing\<close>

text \<open>
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
  exclusion from this rule is the following non-strict operations:\<close>

inductive non_strict_op :: "op \<Rightarrow> bool" where
  "non_strict_op OclIsUndefinedOp"
| "non_strict_op OclIsInvalidOp"
| "non_strict_op AndOp"
| "non_strict_op OrOp"
| "non_strict_op XorOp"
| "non_strict_op ImpliesOp"

abbreviation "strict_op op \<equiv> \<not> non_strict_op op"

subsection \<open>Metaclass Operations\<close>

text \<open>
  All basic types in the theory are either nullable or non-nullable.
  For example, instead of @{text Boolean} type we have two types:
  @{text "Boolean[1]"} and @{text "Boolean[?]"}.
  The @{text "allInstances()"} operation is extended accordingly:\<close>

text \<open>
\<^verbatim>\<open>Boolean[1].allInstances() = Set{true, false}
Boolean[?].allInstances() = Set{true, false, null}\<close>\<close>

inductive mataop_type where
  "finite_type\<^sub>N \<tau> \<Longrightarrow>
   mataop_type (ErrorFree \<tau>) AllInstancesOp (Set \<tau>)[1]"

subsection \<open>Type Operations\<close>

text \<open>
  At first we decided to allow casting only to subtypes.
  However sometimes it is necessary to cast expressions to supertypes,
  for example, to access overridden attributes of a supertype.
  So we allow casting to subtypes and supertypes.
  Casting to other types is meaningless and prohibited.\<close>

text \<open>
  According to the Section 7.4.7 of the OCL specification
  @{text "oclAsType()"} can be applied to collections as well as
  to single values. I guess we can allow @{text "oclIsTypeOf()"}
  and @{text "oclIsKindOf()"} for collections too.\<close>

text \<open>
  Please take a note that the following expressions are prohibited,
  because they always return true or false:\<close>

text \<open>
\<^verbatim>\<open>1.oclIsKindOf(OclAny[?])
1.oclIsKindOf(String[1])\<close>\<close>

text \<open>
  Please take a note that:\<close>

text \<open>
\<^verbatim>\<open>Set{1,2,null,'abc'}->selectByKind(Integer[1]) = Set{1,2}
Set{1,2,null,'abc'}->selectByKind(Integer[?]) = Set{1,2,null}\<close>\<close>

text \<open>
  The following expressions are prohibited, because they always
  returns either the same or empty collections:\<close>

text \<open>
\<^verbatim>\<open>Set{1,2,null,'abc'}->selectByKind(OclAny[?])
Set{1,2,null,'abc'}->selectByKind(Collection(Boolean[1]))\<close>\<close>

abbreviation "error_free_null_free_type \<tau> \<equiv> error_free_type \<tau> \<and> required_type \<tau>"

inductive typeop_type where
  "\<tau> < \<sigma> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> \<sigma>"
| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> \<sigma>[!]"

| "\<sigma> < \<tau> \<Longrightarrow> error_free_null_free_type \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsTypeOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow> \<not> error_free_null_free_type \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsTypeOfOp \<tau> \<sigma> Boolean[1!]"

| "\<sigma> < \<tau> \<Longrightarrow> error_free_null_free_type \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsKindOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow> \<not> error_free_null_free_type \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsKindOfOp \<tau> \<sigma> Boolean[1!]"

| "\<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<rho>)[1] \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow>
   error_free_type \<sigma> \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   typeop_type ArrowCall SelectByKindOp \<tau> \<sigma> \<upsilon>"

| "\<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<rho>)[1] \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow>
   error_free_type \<sigma> \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   typeop_type ArrowCall SelectByTypeOp \<tau> \<sigma> \<upsilon>"

subsection \<open>OclAny Operations\<close>

text \<open>
  The OCL specification defines @{text "toString()"} operation
  only for boolean and numeric types. However, I guess it is a good
  idea to define it once for all types. The OCL specification does not
  state that the operation can return @{text invalid} for a null
  boolean value. Let us suppose that it returns a "null" string.
  However, I guess that the operation should be strict and
  return @{text invalid} for an invalid value.\<close>

inductive any_unop_type where
  "\<tau>[1] \<hookrightarrow> NonIterable()[1] \<Longrightarrow>
   any_unop_type OclAsSetOp \<tau>[1] (Set \<tau>[\<^bold>1])[1]"
| "\<tau>[?] \<hookrightarrow> NonIterable()[?] \<Longrightarrow>
   any_unop_type OclAsSetOp \<tau>[?] (Set \<tau>[\<^bold>1])[1]"

| "\<tau> \<hookrightarrow> ObjectType(\<C>)[_] \<Longrightarrow>
   any_unop_type OclIsNewOp \<tau> Boolean[1]"

| "any_unop_type OclIsUndefinedOp \<tau>[?] Boolean[1]"
| "any_unop_type OclIsUndefinedOp \<tau>[1!] Boolean[1]"
| "any_unop_type OclIsUndefinedOp \<tau>[?!] Boolean[1]"

| "any_unop_type OclIsInvalidOp \<tau>[1!] Boolean[1]"
| "any_unop_type OclIsInvalidOp \<tau>[?!] Boolean[1]"

| "any_unop_type ToStringOp \<tau> String[1]"

text \<open>
  It makes sense to compare values only with compatible types.\<close>

(* We have to specify the predicate type explicitly to let
   a generated code work *)
inductive any_binop_type
    :: "any_binop \<Rightarrow> ('a :: order) type\<^sub>N\<^sub>E \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool" where
  "\<tau> \<le> \<sigma> \<or> \<sigma> < \<tau> \<Longrightarrow>
   any_binop_type EqualOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<le> \<sigma> \<or> \<sigma> < \<tau> \<Longrightarrow>
   any_binop_type NotEqualOp \<tau> \<sigma> Boolean[1]"

subsection \<open>Boolean Operations\<close>

text \<open>
  Please take a note that:\<close>

text \<open>
\<^verbatim>\<open>true or false : Boolean[1]
true and null : Boolean[?]
null and null : OclVoid[?]\<close>\<close>

inductive boolean_unop_type where
  "\<tau> \<le> Boolean[?!] \<Longrightarrow>
   boolean_unop_type NotOp \<tau> \<tau>"

inductive boolean_binop_type where
  "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?!] \<Longrightarrow>
   boolean_binop_type AndOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?!] \<Longrightarrow>
   boolean_binop_type OrOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?!] \<Longrightarrow>
   boolean_binop_type XorOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> \<le> Boolean[?!] \<Longrightarrow>
   boolean_binop_type ImpliesOp \<tau> \<sigma> \<rho>"

subsection \<open>Numeric Operations\<close>

text \<open>
  The expression @{text "1 + null"} is not well-typed.
  Nullable numeric values should be converted to non-nullable ones.
  This is a significant difference from the OCL specification.\<close>

text \<open>
  Please take a note that @{text "floor()"} and @{text "round()"}
  operations are undefined for the @{text "Integer"} type.
  The @{text "Integer"} type is not inherited from the @{text "Real"}
  type, it is just a subtype.\<close>

text \<open>
  The @{text "oclAsType(Integer)"} operation is not well-typed,
  because the @{text "UnlimitedNatural"} type is not a subtype
  of the @{text "Integer"} type. So the @{text "toInteger()"}
  operation should be used instead.\<close>

inductive numeric_unop_type where
  "numeric_unop_type UMinusOp Real[1] Real[1]"
| "numeric_unop_type UMinusOp Integer[1] Integer[1]"

| "numeric_unop_type AbsOp Real[1] Real[1]"
| "numeric_unop_type AbsOp Integer[1] Integer[1]"

| "numeric_unop_type FloorOp Real[1] Integer[1]"
| "numeric_unop_type RoundOp Real[1] Integer[1]"

| "numeric_unop_type numeric_unop.ToIntegerOp UnlimitedNatural[1] Integer[1!]"

inductive numeric_binop_type where
  "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> (\<tau> \<squnion> \<sigma>)"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> UnlimitedNatural[1!]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> (\<tau> \<squnion> \<sigma>)"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> (\<tau> \<squnion> \<sigma>)"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> UnlimitedNatural[1!]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type DivideOp \<tau> \<sigma> Real[1!]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type DivideOp \<tau> \<sigma> Real[1!]"

| "\<tau> = Integer[1] \<Longrightarrow> \<sigma> = Integer[1] \<Longrightarrow>
   numeric_binop_type DivOp \<tau> \<sigma> Integer[1!]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type DivOp \<tau> \<sigma> UnlimitedNatural[1!]"

| "\<tau> = Integer[1] \<Longrightarrow> \<sigma> = Integer[1] \<Longrightarrow>
   numeric_binop_type ModOp \<tau> \<sigma> Integer[1!]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type ModOp \<tau> \<sigma> UnlimitedNatural[1!]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type NumericMaxOp \<tau> \<sigma> (\<tau> \<squnion> \<sigma>)"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type NumericMaxOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type NumericMinOp \<tau> \<sigma> (\<tau> \<squnion> \<sigma>)"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type NumericMinOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type NumericLessOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type NumericLessOp \<tau> \<sigma> Boolean[1]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type NumericLessEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type NumericLessEqOp \<tau> \<sigma> Boolean[1]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type NumericGreaterOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type NumericGreaterOp \<tau> \<sigma> Boolean[1]"

| "\<tau> = Integer[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = Integer[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type NumericGreaterEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1] \<Longrightarrow>
   numeric_binop_type NumericGreaterEqOp \<tau> \<sigma> Boolean[1]"

subsection \<open>String Operations\<close>

inductive string_unop_type where
  "string_unop_type StringSizeOp String[1] Integer[1]"
| "string_unop_type CharactersOp String[1] (Sequence String[\<^bold>1])[1]"
| "string_unop_type ToUpperCaseOp String[1] String[1]"
| "string_unop_type ToLowerCaseOp String[1] String[1]"
| "string_unop_type ToBooleanOp String[1] Boolean[1!]"
| "string_unop_type ToRealOp String[1] Real[1!]"
| "string_unop_type ToIntegerOp String[1] Integer[1!]"

inductive string_binop_type where
  "string_binop_type ConcatOp String[1] String[1] String[1]"
| "string_binop_type EqualsIgnoreCaseOp String[1] String[1] Boolean[1]"
| "string_binop_type StringLessOp String[1] String[1] Boolean[1]"
| "string_binop_type StringLessEqOp String[1] String[1] Boolean[1]"
| "string_binop_type StringGreaterOp String[1] String[1] Boolean[1]"
| "string_binop_type StringGreaterEqOp String[1] String[1] Boolean[1]"
| "string_binop_type StringIndexOfOp String[1] String[1] Integer[1]"
| "string_binop_type StringAtOp String[1] Integer[1] String[1!]"

inductive string_ternop_type where
  "string_ternop_type SubstringOp String[1] Integer[1] Integer[1] String[1!]"

subsection \<open>Iterable Operations\<close>

text \<open>
  Please take a note, that @{text "flatten()"} preserves a collection kind.\<close>

abbreviation "max_op_defined \<tau> \<equiv>
  (\<tau> = Real[1] \<or> \<tau> = Integer[1] \<or> \<tau> = UnlimitedNatural[1] \<or>
   operation_defined \<tau> STR ''max'' [\<tau>])"

abbreviation "min_op_defined \<tau> \<equiv>
  (\<tau> = Real[1] \<or> \<tau> = Integer[1] \<or> \<tau> = UnlimitedNatural[1] \<or>
   operation_defined \<tau> STR ''min'' [\<tau>])"

abbreviation "sum_op_defined \<tau> \<equiv>
  (\<tau> = Real[1] \<or> \<tau> = Integer[1] \<or> \<tau> = UnlimitedNatural[1] \<or>
   operation_defined \<tau> STR ''+'' [\<tau>])"


inductive comparable_type\<^sub>T where
  "comparable_type\<^sub>T Real"
| "comparable_type\<^sub>T Integer"
| "comparable_type\<^sub>T UnlimitedNatural"
| "comparable_type\<^sub>T String"

inductive comparable_type\<^sub>N where
  "comparable_type\<^sub>T \<tau> \<Longrightarrow>
   comparable_type\<^sub>N (Required \<tau>) False"
| "comparable_type\<^sub>T \<tau> \<Longrightarrow>
   comparable_type\<^sub>N (Optional \<tau>) True"

inductive comparable_type where
  "comparable_type\<^sub>N \<tau> n \<Longrightarrow>
   comparable_type (ErrorFree \<tau>) n"
| "comparable_type\<^sub>N \<tau> n \<Longrightarrow>
   comparable_type (Errorable \<tau>) n"


inductive iterable_unop_type where
  "\<tau> \<hookrightarrow> Iterable(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type SizeOp \<tau> Integer[1]"
| "\<tau> \<hookrightarrow> Iterable(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type IsEmptyOp \<tau> Boolean[1]"
| "\<tau> \<hookrightarrow> Iterable(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type NotEmptyOp \<tau> Boolean[1]"

| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow> max_op_defined \<sigma> \<Longrightarrow>
   iterable_unop_type MaxOp \<tau> \<sigma>"
| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow> min_op_defined \<sigma> \<Longrightarrow>
   iterable_unop_type MinOp \<tau> \<sigma>"
| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow> sum_op_defined \<sigma> \<Longrightarrow>
   iterable_unop_type SumOp \<tau> \<sigma>"

| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   \<rho> \<hookleftarrow> Set(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type AsSetOp \<tau> \<rho>"
| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   \<rho> \<hookleftarrow> OrderedSet(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type AsOrderedSetOp \<tau> \<rho>"
| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   \<rho> \<hookleftarrow> Bag(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type AsBagOp \<tau> \<rho>"
| "\<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   \<rho> \<hookleftarrow> Sequence(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type AsSequenceOp \<tau> \<rho>"

| "\<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Collection\<^bsub>k\<^esub>(\<rho>)[1] \<Longrightarrow>
   iterable_unop_type FlattenOp \<tau> \<upsilon>"

| "\<tau> \<hookrightarrow> OrderedCollection(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type FirstOp \<tau> \<sigma>[!]"
| "\<tau> \<hookrightarrow> OrderedCollection(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type LastOp \<tau> \<sigma>[!]"
| "\<tau> \<hookrightarrow> OrderedCollection(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type ReverseOp \<tau> \<tau>"

| "\<tau> \<hookrightarrow> Map(\<sigma>, \<rho>)[1] \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Set(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type KeysOp \<tau> \<upsilon>"
| "\<tau> \<hookrightarrow> Map(\<sigma>, \<rho>)[1] \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Bag(\<sigma>)[1] \<Longrightarrow>
   iterable_unop_type ValuesOp \<tau> \<upsilon>"

text \<open>
  Please take a note that if both arguments are collections,
  then an element type of the resulting collection is a super type
  of element types of orginal collections. However for single-valued
  operations (@{text "append()"}, @{text "insertAt()"}, ...)
  this behavior looks undesirable. So we restrict such arguments
  to have a subtype of the collection element type.\<close>

text \<open>
  Please take a note that we allow the following expressions:\<close>

text \<open>
\<^verbatim>\<open>let nullable_value : Integer[?] = null in
Sequence{1..3}->inculdes(nullable_value) and
Sequence{1..3}->inculdes(null) and
Sequence{1..3}->inculdesAll(Set{1,null})\<close>\<close>

text \<open>
  The OCL specification defines @{text "including()"} and
  @{text "excluding()"} operations for the @{text Sequence} type
  but does not define them for the @{text OrderedSet} type.
  We define them for all collection types.

  It is a good idea to prohibit including of values that
  do not conform to a collection element type.
  However we do not restrict it.

  At first we defined the following typing rules for the
  @{text "excluding()"} operation:

{\isacharbar}\ {\isachardoublequoteopen}element{\isacharunderscore}type\ {\isasymtau}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isasymle}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isasymnoteq}\ OclVoid{\isacharbrackleft}{\isacharquery}{\isacharbrackright}\ {\isasymLongrightarrow}\isanewline
\ \ \ collection{\isacharunderscore}binop{\isacharunderscore}type\ ExcludingOp\ {\isasymtau}\ {\isasymsigma}\ {\isasymtau}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ {\isachardoublequoteopen}element{\isacharunderscore}type\ {\isasymtau}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isasymle}\ {\isasymrho}\ {\isasymLongrightarrow}\ {\isasymsigma}\ {\isacharequal}\ OclVoid{\isacharbrackleft}{\isacharquery}{\isacharbrackright}\ {\isasymLongrightarrow}\isanewline
\ \ \ update{\isacharunderscore}element{\isacharunderscore}type\ {\isasymtau}\ {\isacharparenleft}to{\isacharunderscore}required{\isacharunderscore}type\ {\isasymrho}{\isacharparenright}\ {\isasymupsilon}\ {\isasymLongrightarrow}\isanewline
\ \ \ collection{\isacharunderscore}binop{\isacharunderscore}type\ ExcludingOp\ {\isasymtau}\ {\isasymsigma}\ {\isasymupsilon}{\isachardoublequoteclose}\isanewline

  This operation could play a special role in a definition
  of safe navigation operations:\<close>

text \<open>
\<^verbatim>\<open>Sequence{1,2,null}->exculding(null) : Integer[1]\<close>\<close>

text \<open>
  However it is more natural to use a @{text "selectByKind(T[1])"}
  operation instead.\<close>

(* TODO: Написать про разницу including и append *)

notation unwrap_errorable_type ("\<lfloor>_\<rfloor>\<^sub>E")

inductive iterable_binop_type where
  "\<tau> \<hookrightarrow> Collection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho>[??] \<Longrightarrow>
   iterable_binop_type CountOp \<tau> \<sigma> Integer[1]"

| "\<tau> \<hookrightarrow> Iterable(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho>[??] \<Longrightarrow>
   iterable_binop_type IncludesOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<hookrightarrow> Iterable(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho>[??] \<Longrightarrow>
   iterable_binop_type ExcludesOp \<tau> \<sigma> Boolean[1]"

| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow> \<sigma> \<le> \<upsilon>[??] \<Longrightarrow>
   iterable_binop_type IncludesValueOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow> \<sigma> \<le> \<upsilon>[??] \<Longrightarrow>
   iterable_binop_type ExcludesValueOp \<tau> \<sigma> Boolean[1]"

| "\<tau> \<hookrightarrow> Iterable(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Collection(\<upsilon>)[1] \<Longrightarrow>
   \<upsilon> \<le> \<rho>[??] \<Longrightarrow>
   iterable_binop_type IncludesAllOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<hookrightarrow> Iterable(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Collection(\<upsilon>)[1] \<Longrightarrow>
   \<upsilon> \<le> \<rho>[??] \<Longrightarrow>
   iterable_binop_type ExcludesAllOp \<tau> \<sigma> Boolean[1]"

| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Map(\<phi>, \<psi>)[1] \<Longrightarrow>
   \<phi> \<le> \<rho>[??] \<Longrightarrow>
   \<psi> \<le> \<upsilon>[??] \<Longrightarrow>
   iterable_binop_type IncludesMapOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Map(\<phi>, \<psi>)[1] \<Longrightarrow>
   \<phi> \<le> \<rho>[??] \<Longrightarrow>
   \<psi> \<le> \<upsilon>[??] \<Longrightarrow>
   iterable_binop_type ExcludesMapOp \<tau> \<sigma> Boolean[1]"

| "\<tau> \<hookrightarrow> Collection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Collection(\<upsilon>)[1] \<Longrightarrow>
   iterable_binop_type ProductOp \<tau> \<sigma>
      (Set (Tuple(STR ''first'' : \<lfloor>\<rho>\<rfloor>\<^sub>E, STR ''second'' : \<lfloor>\<upsilon>\<rfloor>\<^sub>E))[\<^bold>1])[1]"

| "iterable_binop_type UnionOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "iterable_binop_type UnionOp (Set \<tau>)[1] (Bag \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"
| "iterable_binop_type UnionOp (Bag \<tau>)[1] (Set \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"
| "iterable_binop_type UnionOp (Bag \<tau>)[1] (Bag \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"

| "iterable_binop_type IntersectionOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "iterable_binop_type IntersectionOp (Set \<tau>)[1] (Bag \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "iterable_binop_type IntersectionOp (Bag \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "iterable_binop_type IntersectionOp (Bag \<tau>)[1] (Bag \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"

| "\<tau> \<le> \<sigma> \<or> \<sigma> \<le> \<tau> \<Longrightarrow>
   iterable_binop_type SetMinusOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set \<tau>)[1]"
| "iterable_binop_type SymmetricDifferenceOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"

| "\<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<rho>)[1] \<Longrightarrow>
   \<phi> \<hookleftarrow> Collection\<^bsub>k\<^esub>(\<rho> \<squnion> \<sigma>)[1] \<Longrightarrow>
   iterable_binop_type IncludingOp \<tau> \<sigma> \<phi>"
| "\<tau> \<hookrightarrow> Collection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type ExcludingOp \<tau> \<sigma> \<tau>"
| "\<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Collection(\<upsilon>)[1] \<Longrightarrow>
   \<phi> \<hookleftarrow> Collection\<^bsub>k\<^esub>(\<rho> \<squnion> \<upsilon>)[1] \<Longrightarrow>
   iterable_binop_type IncludingAllOp \<tau> \<sigma> \<phi>"
| "\<tau> \<hookrightarrow> Collection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Collection(\<upsilon>)[1] \<Longrightarrow>
   \<upsilon> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type ExcludingAllOp \<tau> \<sigma> \<tau>"

| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Map(\<rho>', \<upsilon>')[1] \<Longrightarrow>
   \<phi> \<hookleftarrow> Map(\<rho> \<squnion> \<rho>', \<upsilon> \<squnion> \<upsilon>')[1] \<Longrightarrow>
   iterable_binop_type IncludingMapOp \<tau> \<sigma> \<phi>"
| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> Map(\<rho>', \<upsilon>')[1] \<Longrightarrow>
   \<rho>' \<le> \<rho> \<Longrightarrow>
   \<upsilon>' \<le> \<upsilon> \<Longrightarrow>
   iterable_binop_type ExcludingMapOp \<tau> \<sigma> \<tau>"

| "\<tau> \<hookrightarrow> OrderedCollection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type AppendOp \<tau> \<sigma> \<tau>"
| "\<tau> \<hookrightarrow> OrderedCollection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type PrependOp \<tau> \<sigma> \<tau>"
| "\<tau> \<hookrightarrow> OrderedCollection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> OrderedCollection(\<upsilon>)[1] \<Longrightarrow>
   \<upsilon> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type AppendAllOp \<tau> \<sigma> \<tau>"
| "\<tau> \<hookrightarrow> OrderedCollection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<hookrightarrow> OrderedCollection(\<upsilon>)[1] \<Longrightarrow>
   \<upsilon> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type PrependAllOp \<tau> \<sigma> \<tau>"

| "\<tau> \<hookrightarrow> OrderedCollection(\<sigma>)[1] \<Longrightarrow>
   iterable_binop_type AtOp \<tau> Integer[1] \<sigma>[!]"
| "\<tau> \<hookrightarrow> Map(\<rho>, \<upsilon>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho>[??] \<Longrightarrow>
   iterable_binop_type AtOp \<tau> \<sigma> \<upsilon>[!]"

| "\<tau> \<hookrightarrow> OrderedCollection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho> \<Longrightarrow>
   iterable_binop_type IndexOfOp \<tau> \<sigma> Integer[1]"

inductive iterable_ternop_type where
  "\<tau> \<hookrightarrow> OrderedCollection(\<rho>)[1] \<Longrightarrow>
   \<sigma> \<le> \<rho> \<Longrightarrow>
   iterable_ternop_type InsertAtOp \<tau> Integer[1] \<sigma> \<tau>[!]"

| "\<tau> \<hookrightarrow> OrderedSet(\<sigma>)[1] \<Longrightarrow>
   iterable_ternop_type SubOrderedSetOp \<tau> Integer[1] Integer[1] \<tau>[!]"
| "\<tau> \<hookrightarrow> Sequence(\<sigma>)[1] \<Longrightarrow>
   iterable_ternop_type SubSequenceOp \<tau> Integer[1] Integer[1] \<tau>[!]"

| "\<tau> \<hookrightarrow> Map(\<upsilon>, \<phi>)[1] \<Longrightarrow>
   \<sigma> \<le> \<upsilon> \<Longrightarrow>
   \<rho> \<le> \<phi> \<Longrightarrow>
   iterable_ternop_type IncludesPairOp \<tau> \<sigma> \<rho> Boolean[1]"
| "\<tau> \<hookrightarrow> Map(\<upsilon>, \<phi>)[1] \<Longrightarrow>
   \<sigma> \<le> \<upsilon> \<Longrightarrow>
   \<rho> \<le> \<phi> \<Longrightarrow>
   iterable_ternop_type ExcludesPairOp \<tau> \<sigma> \<rho> Boolean[1]"

| "\<tau> \<hookrightarrow> Map(\<upsilon>, \<phi>)[1] \<Longrightarrow>
   \<psi> \<hookleftarrow> Map(\<upsilon> \<squnion> \<sigma>, \<phi> \<squnion> \<rho>)[1] \<Longrightarrow>
   iterable_ternop_type IncludingPairOp \<tau> \<sigma> \<rho> \<psi>"
| "\<tau> \<hookrightarrow> Map(\<upsilon>, \<phi>)[1] \<Longrightarrow>
   \<sigma> \<le> \<upsilon> \<Longrightarrow>
   \<rho> \<le> \<phi> \<Longrightarrow>
   iterable_ternop_type ExcludingPairOp \<tau> \<sigma> \<rho> \<tau>"

subsection \<open>Coercions\<close>

inductive unop_type where
  "any_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inl op) DotCall \<tau> \<sigma>"
| "boolean_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inl op)) DotCall \<tau> \<sigma>"
| "numeric_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inl op))) DotCall \<tau> \<sigma>"
| "string_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inl op)))) DotCall \<tau> \<sigma>"
| "iterable_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inr op)))) ArrowCall \<tau> \<sigma>"

inductive binop_type where
  "any_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inl op) DotCall \<tau> \<sigma> \<rho>"
| "boolean_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inl op)) DotCall \<tau> \<sigma> \<rho>"
| "numeric_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inl op))) DotCall \<tau> \<sigma> \<rho>"
| "string_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inl op)))) DotCall \<tau> \<sigma> \<rho>"
| "iterable_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inr op)))) ArrowCall \<tau> \<sigma> \<rho>"

inductive ternop_type where
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inl op) DotCall \<tau> \<sigma> \<rho> \<upsilon>"
| "iterable_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inr op) ArrowCall \<tau> \<sigma> \<rho> \<upsilon>"

definition "op_result_type_is_errorable op \<pi> \<equiv>
  strict_op op \<and> fBex \<pi> errorable_type"
(*
code_pred [show_modes] unop_type .
code_pred [show_modes] binop_type .
code_pred [show_modes] ternop_type .
*)
inductive op_type where
  "unop_type op k (to_error_free_type \<tau>) \<upsilon> \<Longrightarrow>
   op_result_type_is_errorable (Inl op) {|\<tau>|} \<Longrightarrow>
   op_type (Inl op) k \<tau> [] \<upsilon>[!]"
| "unop_type op k (to_error_free_type \<tau>) \<upsilon> \<Longrightarrow>
   \<not> op_result_type_is_errorable (Inl op) {|\<tau>|} \<Longrightarrow>
   op_type (Inl op) k \<tau> [] \<upsilon>"

| "binop_type op k (to_error_free_type \<tau>) (to_error_free_type \<sigma>) \<upsilon> \<Longrightarrow>
   op_result_type_is_errorable (Inr (Inl op)) {|\<tau>, \<sigma>|} \<Longrightarrow>
   op_type (Inr (Inl op)) k \<tau> [\<sigma>] \<upsilon>[!]"
| "binop_type op k (to_error_free_type \<tau>) (to_error_free_type \<sigma>) \<upsilon> \<Longrightarrow>
   \<not> op_result_type_is_errorable (Inr (Inl op)) {|\<tau>, \<sigma>|} \<Longrightarrow>
   op_type (Inr (Inl op)) k \<tau> [\<sigma>] \<upsilon>"

| "ternop_type op k (to_error_free_type \<tau>) (to_error_free_type \<sigma>)
        (to_error_free_type \<rho>) \<upsilon> \<Longrightarrow>
   op_result_type_is_errorable (Inr (Inr (Inl op))) {|\<tau>, \<sigma>, \<rho>|} \<Longrightarrow>
   op_type (Inr (Inr (Inl op))) k \<tau> [\<sigma>, \<rho>] \<upsilon>[!]"
| "ternop_type op k (to_error_free_type \<tau>) (to_error_free_type \<sigma>)
        (to_error_free_type \<rho>) \<upsilon> \<Longrightarrow>
   \<not> op_result_type_is_errorable (Inr (Inr (Inl op))) {|\<tau>, \<sigma>, \<rho>|} \<Longrightarrow>
   op_type (Inr (Inr (Inl op))) k \<tau> [\<sigma>, \<rho>] \<upsilon>"

| "operation \<tau> op \<pi> oper \<Longrightarrow>
   op_type (Inr (Inr (Inr op))) DotCall \<tau> \<pi> (oper_type oper)"

(*code_pred [show_modes] op_type .*)

(*** Simplification Rules ***************************************************)

subsection \<open>Simplification Rules\<close>

inductive_simps op_type_alt_simps:
"mataop_type \<tau> op \<sigma>"
"typeop_type k op \<tau> \<sigma> \<rho>"

"op_type op k \<tau> \<pi> \<sigma>"
"unop_type op k \<tau> \<sigma>"
"binop_type op k \<tau> \<sigma> \<rho>"
"ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>"

"any_unop_type op \<tau> \<sigma>"
"boolean_unop_type op \<tau> \<sigma>"
"numeric_unop_type op \<tau> \<sigma>"
"string_unop_type op \<tau> \<sigma>"
"iterable_unop_type op \<tau> \<sigma>"

"any_binop_type op \<tau> \<sigma> \<rho>"
"boolean_binop_type op \<tau> \<sigma> \<rho>"
"numeric_binop_type op \<tau> \<sigma> \<rho>"
"string_binop_type op \<tau> \<sigma> \<rho>"
"iterable_binop_type op \<tau> \<sigma> \<rho>"

"string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"
"iterable_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"

(*** Determinism ************************************************************)

(*code_pred [show_modes] op_type .*)

subsection \<open>Determinism\<close>

lemma mataop_type_det:
  "mataop_type \<tau> op \<sigma> \<Longrightarrow>
   mataop_type \<tau> op \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: mataop_type.simps)

lemma typeop_type_det:
  "typeop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   typeop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (erule typeop_type.cases;
      auto simp add: typeop_type.simps)
  using collection_type_det(1) collection_type_det(2) by blast+

lemma any_unop_type_det:
  "any_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   any_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (erule any_unop_type.cases; simp add: any_unop_type.simps)

lemma boolean_unop_type_det:
  "boolean_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   boolean_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (erule boolean_unop_type.cases; simp add: boolean_unop_type.simps)

lemma numeric_unop_type_det:
  "numeric_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   numeric_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (erule numeric_unop_type.cases; auto simp add: numeric_unop_type.simps)

lemma string_unop_type_det:
  "string_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   string_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (erule string_unop_type.cases; simp add: string_unop_type.simps)

lemma iterable_unop_type_det:
  "iterable_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   iterable_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  apply (erule iterable_unop_type.cases; simp add: iterable_unop_type.simps)
  using collection_type_det(2) any_collection_type_det apply blast+
  using collection_type_det to_single_type_det apply blast+
  apply (metis collection_type_det(1) ordered_collection_type.simps)
  apply (metis collection_type_det(1) ordered_collection_type.simps)
  using collection_type_det map_type_det by blast+

lemma unop_type_det:
  "unop_type op k \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   unop_type op k \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (erule unop_type.cases;
      simp add: unop_type.simps any_unop_type_det
                boolean_unop_type_det numeric_unop_type_det
                string_unop_type_det iterable_unop_type_det)

lemma any_binop_type_det:
  "any_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   any_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (erule any_binop_type.cases; auto simp add: any_binop_type.simps)

lemma boolean_binop_type_det:
  "boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (erule boolean_binop_type.cases; simp add: boolean_binop_type.simps)

lemma numeric_binop_type_det:
  "numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (erule numeric_binop_type.cases;
      auto simp add: numeric_binop_type.simps split: if_splits)

lemma string_binop_type_det:
  "string_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   string_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (erule string_binop_type.cases; simp add: string_binop_type.simps)

lemma iterable_binop_type_det:
  "iterable_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   iterable_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (erule iterable_binop_type.cases; simp add: iterable_binop_type.simps)
  using any_collection_type_det apply blast
  using collection_type_det apply blast
  using any_collection_type_det collection_type_det apply blast
  using map_type_det apply blast
  using ordered_collection_type_and_map_type_distinct
        ordered_collection_type_det apply blast
  using ordered_collection_type_and_map_type_distinct map_type_det(1) by blast

lemma binop_type_det:
  "binop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   binop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (erule binop_type.cases;
      simp add: binop_type.simps any_binop_type_det
                boolean_binop_type_det numeric_binop_type_det
                string_binop_type_det iterable_binop_type_det)

lemma string_ternop_type_det:
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (erule string_ternop_type.cases; simp add: string_ternop_type.simps)

lemma iterable_ternop_type_det:
  "iterable_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   iterable_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  apply (erule iterable_ternop_type.cases; simp add: iterable_ternop_type.simps)
  using map_type_det(1) map_type_det(2) by blast

lemma ternop_type_det:
  "ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (erule ternop_type.cases;
      simp add: ternop_type.simps string_ternop_type_det iterable_ternop_type_det)

lemma op_type_det:
  "op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow>
   op_type op k \<tau> \<pi> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (auto simp add: op_type.simps)
  using unop_type_det binop_type_det ternop_type_det apply blast+
  using operation_det by blast

(*** Expressions Typing *****************************************************)

section \<open>Expressions Typing\<close>

text \<open>
  The following typing rules are preliminary. The final rules are given at
  the end of the next chapter.\<close>

definition "iterators its \<tau> \<equiv>
  fmap_of_list (map (\<lambda>it. (fst it, \<tau>)) its)"

definition "coiterators its \<tau> \<equiv>
  fmap_of_list (map (\<lambda>it. (the (snd it), \<tau>)) (filter (\<lambda>it. snd it \<noteq> None) its))"

inductive typing :: "('a :: ocl_object_model) type\<^sub>N\<^sub>E env \<Rightarrow> 'a expr \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool"
       ("(1_/ \<turnstile>\<^sub>E/ (_ :/ _))" [51,51,51] 50)
      and collection_part_typing ("(1_/ \<turnstile>\<^sub>C/ (_ :/ _))" [51,51,51] 50)
      and iterator_typing ("(1_/ \<turnstile>\<^sub>I/ (_ :/ _))" [51,51,51] 50)
      and expr_list_typing ("(1_/ \<turnstile>\<^sub>L/ (_ :/ _))" [51,51,51] 50) where

\<comment> \<open>Primitive Literals\<close>

 NullLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E NullLiteral : OclVoid[?]"
|BooleanLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : Boolean[1]"
|RealLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E RealLiteral c : Real[1]"
|IntegerLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : Integer[1]"
|UnlimitedNaturalLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : UnlimitedNatural[1]"
|StringLiteralT:
  "\<Gamma> \<turnstile>\<^sub>E StringLiteral c : String[1]"
|EnumLiteralT:
  "has_literal enm lit \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E EnumLiteral enm lit : (Enum enm)[1]"

\<comment> \<open>Tuple Literals\<close>

|TupleLiteralNilT:
  "\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : (Tuple fmempty)[1]"
|TupleLiteralConsT:
  "\<Gamma> \<turnstile>\<^sub>E tuple_literal_element_expr el : \<tau> \<Longrightarrow>
   tuple_literal_element_type el = Some \<sigma> \<Longrightarrow>
   \<tau> \<le> \<sigma> \<Longrightarrow>
   \<rho> \<hookleftarrow> Tuple([tuple_literal_element_name el \<mapsto>\<^sub>f \<sigma>])[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleLiteral elems : \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleLiteral (el # elems) : \<rho> \<squnion> \<upsilon>"

\<comment> \<open>Collection Literals\<close>

|CollectionLiteralNilT:
  "k \<noteq> CollectionKind \<Longrightarrow>
   \<sigma> \<hookleftarrow> Collection\<^bsub>k\<^esub>(OclVoid[1])[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral k [] : \<sigma>"
|CollectionLiteralConsT:
  "k \<noteq> CollectionKind \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C x : \<tau> \<Longrightarrow>
   \<sigma> \<hookleftarrow> Collection\<^bsub>k\<^esub>(\<tau>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral k xs : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral k (x # xs) : \<sigma> \<squnion> \<rho>"

|CollectionPartItemT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionItem a : \<tau>"
|CollectionPartRangeT:
  "\<Gamma> \<turnstile>\<^sub>E a : Integer[1] \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E b : Integer[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionRange a b : Integer[1]"
|LowerErrorableCollectionPartRangeT:
  "\<Gamma> \<turnstile>\<^sub>E a : Integer[1!] \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E b : Integer[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionRange a b : Integer[1!]"
|UpperErrorableCollectionPartRangeT:
  "\<Gamma> \<turnstile>\<^sub>E a : Integer[1] \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E b : Integer[1!] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionRange a b : Integer[1!]"
|ErrorableCollectionPartRangeT:
  "\<Gamma> \<turnstile>\<^sub>E a : Integer[1!] \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E b : Integer[1!] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionRange a b : Integer[1!]"

\<comment> \<open>Map Literals\<close>

|MapNilT:
  "\<tau> \<hookleftarrow> Map(OclVoid[1], OclVoid[1])[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MapLiteral [] : \<tau>"
|MapConsT:
  "\<Gamma> \<turnstile>\<^sub>E map_literal_element_key x : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E map_literal_element_value x : \<sigma> \<Longrightarrow>
   \<rho> \<hookleftarrow> Map(\<tau>, \<sigma>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MapLiteral xs : \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MapLiteral (x # xs) : \<rho> \<squnion> \<upsilon>"

\<comment> \<open>Misc Expressions\<close>

|LetT:
  "\<Gamma> \<turnstile>\<^sub>E init : \<sigma> \<Longrightarrow>
   \<sigma> \<le> \<tau> \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E Let v (Some \<tau>) init body : \<rho>"
|VarT:
  "fmlookup \<Gamma> v = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
|IfT:
  "\<Gamma> \<turnstile>\<^sub>E cnd : Boolean[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E thn : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E els : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E If cnd thn els : \<sigma> \<squnion> \<rho>"
|ErrorableIfT:
  "\<Gamma> \<turnstile>\<^sub>E cnd : Boolean[1!] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E thn : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E els : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E If cnd thn els : (\<sigma> \<squnion> \<rho>)[!]"

\<comment> \<open>Call Expressions\<close>

|MetaOperationCallT:
  "mataop_type \<tau> op \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"

|StaticOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   static_operation \<tau> op \<pi> oper \<Longrightarrow>
   \<not> fBex (fset_of_list \<pi>) errorable_type \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op params : oper_type oper"
|ErrorableStaticOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   static_operation \<tau> op \<pi> oper \<Longrightarrow>
   fBex (fset_of_list \<pi>) errorable_type \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op params : (oper_type oper)[!]"

|TypeOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   typeop_type k op \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<rho>"

|OperationCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<sigma>"

|AttributeCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   attribute \<C> prop \<D> \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AttributeCall src prop : \<tau>"
|ErrorableAttributeCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1!] \<Longrightarrow>
   attribute \<C> prop \<D> \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AttributeCall src prop : \<tau>[!]"

|AssociationEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   association_end \<C> from role \<D> end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationEndCall src from role : assoc_end_type end"
|ErrorableAssociationEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1!] \<Longrightarrow>
   association_end \<C> from role \<D> end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationEndCall src from role : (assoc_end_type end)[!]"

|AssociationClassCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   referred_by_association_class \<C> from \<A> \<D> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassCall src from \<A> : class_assoc_type \<A>"
|ErrorableAssociationClassCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1!] \<Longrightarrow>
   referred_by_association_class \<C> from \<A> \<D> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassCall src from \<A> : (class_assoc_type \<A>)[!]"

|AssociationClassEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<A>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   association_class_end \<A> role end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src role : class_assoc_end_type end"
|ErrorableAssociationClassEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<A>\<rangle>\<^sub>\<T>[1!] \<Longrightarrow>
   association_class_end \<A> role end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src role : (class_assoc_end_type end)[!]"

|TupleElementCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : (Tuple \<pi>)[1] \<Longrightarrow>
   fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleElementCall src elem : ErrorFree \<tau>"
|ErrorableTupleElementCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : (Tuple \<pi>)[1!] \<Longrightarrow>
   fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleElementCall src elem : Errorable \<tau>"

\<comment> \<open>Iterator Expressions\<close>

|CollectionLoopT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   \<sigma> \<le> its_ty \<Longrightarrow>
   list_all (\<lambda>it. snd it = None) its \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its its_ty \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_ty, None), body) : (\<tau>, \<sigma>, \<rho>)"
|MapLoopT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Map(\<sigma>, \<upsilon>)[1] \<Longrightarrow>
   \<sigma> \<le> its_key_ty \<Longrightarrow>
   \<upsilon> \<le> its_val_ty \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its its_key_ty ++\<^sub>f coiterators its its_val_ty \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_key_ty, Some its_val_ty), body) : (\<tau>, \<sigma>, \<rho>)"

|IterateT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, Let res (Some res_t) res_init body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> res_t \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E IterateCall src its its_ty res (Some res_t) res_init body : \<rho>"

|AnyIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AnyIterationCall src its its_ty body : \<sigma>[!]"
|ClosureIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   \<rho> \<hookrightarrow> Collection(\<phi>)[1] \<Longrightarrow>
   \<phi> \<le> \<sigma> \<Longrightarrow>
   \<upsilon> \<hookleftarrow> UniqueCollection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src its its_ty body : \<upsilon>"

|CollectionCollectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_single_type \<rho> \<rho>' \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   \<upsilon> \<hookleftarrow> NonUniqueCollection\<^bsub>k\<^esub>(\<rho>')[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectIterationCall src its its_ty body : \<upsilon>"
|MapCollectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_single_type \<rho> \<rho>' \<Longrightarrow>
   \<tau> \<hookrightarrow> Map(_, _)[1] \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Bag(\<rho>')[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectIterationCall src its its_ty body : \<upsilon>"

|CollectByIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<upsilon> \<hookleftarrow> Map(\<sigma>, \<rho>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectByIterationCall src its its_ty body : \<upsilon>"

|CollectionCollectNestedIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   \<upsilon> \<hookleftarrow> NonUniqueCollection\<^bsub>k\<^esub>(\<rho>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src its its_ty body : \<upsilon>"
|MapCollectNestedIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<hookrightarrow> Map(\<upsilon>, _)[1] \<Longrightarrow>
   \<phi> \<hookleftarrow> Map(\<upsilon>, \<rho>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src its its_ty body : \<phi>"

|ExistsIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> Boolean[?!] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ExistsIterationCall src its its_ty body : \<rho>"
|ForAllIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> Boolean[?!] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ForAllIterationCall src its its_ty body : \<rho>"
|OneIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E OneIterationCall src its its_ty body : Boolean[1]"
|IsUniqueIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E IsUniqueIterationCall src its its_ty body : Boolean[1]"
|SelectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E SelectIterationCall src its its_ty body : \<tau>"
|RejectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E RejectIterationCall src its its_ty body : \<tau>"
|SortedByIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   \<upsilon> \<hookleftarrow> OrderedCollection\<^bsub>k\<^esub>(\<sigma>)[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src its its_ty body : \<upsilon>"

\<comment> \<open>Expression Lists\<close>

|ExprListNilT:
  "\<Gamma> \<turnstile>\<^sub>L [] : []"
|ExprListConsT:
  "\<Gamma> \<turnstile>\<^sub>E expr : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L exprs : \<pi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L expr # exprs : \<tau> # \<pi>"

(*** Elimination Rules ******************************************************)

section \<open>Elimination Rules\<close>

inductive_cases NullLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E NullLiteral : \<tau>"
inductive_cases BooleanLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : \<tau>"
inductive_cases RealLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E RealLiteral c : \<tau>"
inductive_cases IntegerLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : \<tau>"
inductive_cases UnlimitedNaturalLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : \<tau>"
inductive_cases StringLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E StringLiteral c : \<tau>"
inductive_cases EnumLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E EnumLiteral enm lit : \<tau>"
inductive_cases TupleLiteralNilTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : \<tau>"
inductive_cases TupleLiteralConsTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleLiteral (x # xs) : \<tau>"
inductive_cases CollectionLiteralNilTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k [] : \<tau>"
inductive_cases CollectionLiteralConsTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k (x # xs) : \<tau>"
inductive_cases MapLiteralNilTE [elim]: "\<Gamma> \<turnstile>\<^sub>E MapLiteral [] : \<tau>"
inductive_cases MapLiteralConsTE [elim]: "\<Gamma> \<turnstile>\<^sub>E MapLiteral (x # xs) : \<tau>"

inductive_cases CollectionItemTE [elim]: "\<Gamma> \<turnstile>\<^sub>C CollectionItem a : \<tau>"
inductive_cases CollectionRangeTE [elim]: "\<Gamma> \<turnstile>\<^sub>C CollectionRange a b : \<tau>"

inductive_cases LetTE [elim]: "\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
inductive_cases VarTE [elim]: "\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
inductive_cases IfTE [elim]: "\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

inductive_cases MetaOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
inductive_cases StaticOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

inductive_cases TypeOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
inductive_cases AttributeCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AttributeCall src prop : \<tau>"
inductive_cases AssociationEndCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src role from : \<tau>"
inductive_cases AssociationClassCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src a from : \<tau>"
inductive_cases AssociationClassEndCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src role : \<tau>"
inductive_cases OperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
inductive_cases TupleElementCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleElementCall src elem : \<tau>"

inductive_cases LoopTE [elim]: "\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
inductive_cases IterateTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IterateCall src its its_ty res res_t res_init body : \<tau>"
inductive_cases AnyIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AnyIterationCall src its its_ty body : \<tau>"
inductive_cases ClosureIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src its its_ty body : \<tau>"
inductive_cases CollectIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectIterationCall src its its_ty body : \<tau>"
inductive_cases CollectByIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectByIterationCall src its its_ty body : \<tau>"
inductive_cases CollectNestedIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src its its_ty body : \<tau>"
inductive_cases ExistsIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ExistsIterationCall src its its_ty body : \<tau>"
inductive_cases ForAllIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ForAllIterationCall src its its_ty body : \<tau>"
inductive_cases OneIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E OneIterationCall src its its_ty body : \<tau>"
inductive_cases IsUniqueIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IsUniqueIterationCall src its its_ty body : \<tau>"
inductive_cases SelectIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E SelectIterationCall src its its_ty body : \<tau>"
inductive_cases RejectIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E RejectIterationCall src its its_ty body : \<tau>"
inductive_cases SortedByIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src its its_ty body : \<tau>"

inductive_cases ExprListNilTE [elim]: "\<Gamma> \<turnstile>\<^sub>L [] : \<pi>"
inductive_cases ExprListConsTE [elim]: "\<Gamma> \<turnstile>\<^sub>L x # xs : \<pi>"

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>

inductive_simps typing_alt_simps: 
"\<Gamma> \<turnstile>\<^sub>E NullLiteral : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RealLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E StringLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E EnumLiteral enm lit : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral (x # xs) : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k (x # xs) : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E MapLiteral [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E MapLiteral (x # xs) : \<tau>"

"\<Gamma> \<turnstile>\<^sub>C CollectionItem a : \<tau>"
"\<Gamma> \<turnstile>\<^sub>C CollectionRange a b : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

"\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AttributeCall src prop : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src role from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src a from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src role : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleElementCall src elem : \<tau>"

"\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
"\<Gamma> \<turnstile>\<^sub>E IterateCall src its its_ty res res_t res_init body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AnyIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectByIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ExistsIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ForAllIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OneIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IsUniqueIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SelectIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RejectIterationCall src its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src its its_ty body : \<tau>"

"\<Gamma> \<turnstile>\<^sub>L [] : \<pi>"
"\<Gamma> \<turnstile>\<^sub>L x # xs : \<pi>"

lemmas ocl_typing_simps =
  op_type_alt_simps
  op_result_type_is_errorable_def
  iterators_def
  coiterators_def
  typing_alt_simps

(*** Misc Properties ********************************************************)

section \<open>Misc Properties\<close>

lemma TupleLiteral_has_Tuple_type:
  "\<Gamma> \<turnstile>\<^sub>E TupleLiteral prts : \<tau> \<Longrightarrow> \<exists>\<pi>. required_tuple_type \<tau> \<pi>"
proof (induct prts arbitrary: \<tau>)
  case Nil show ?case
    apply (insert Nil)
    apply (erule TupleLiteralNilTE)
    by (auto simp add: tuple_type.simps tuple_type\<^sub>N.simps tuple_type\<^sub>T.simps)
next
  case (Cons a prts) show ?case
    apply (insert Cons)
    apply (erule TupleLiteralConsTE)
    using tuple_type_sup tuple_type'_implies_ex_tuple_type by blast
qed

lemma CollectionLiteral_has_Collection_type:
  "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau> \<Longrightarrow> \<exists>\<sigma>. required_collection_type \<tau> k \<sigma>"
proof (induct prts arbitrary: \<tau>)
  case Nil thus ?case by blast
next
  case (Cons a prts) show ?case
    apply (insert Cons)
    apply (erule CollectionLiteralConsTE)
    using collection_type_sup by blast
qed

lemma MapLiteral_has_Map_type:
  "\<Gamma> \<turnstile>\<^sub>E MapLiteral prts : \<tau> \<Longrightarrow> \<exists>\<sigma> \<rho>. required_map_type \<tau> \<sigma> \<rho>"
proof (induct prts arbitrary: \<tau>)
  case Nil show ?case
    apply (insert Nil)
    apply (erule MapLiteralNilTE)
    by (cases \<tau>; simp add: map_type'_implies_ex_map_type)
next
  case (Cons a prts) show ?case
    apply (insert Cons)
    apply (erule MapLiteralConsTE)
    using map_type'_sup map_type'_implies_ex_map_type by blast
qed

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma
  typing_det:
    "\<Gamma> \<turnstile>\<^sub>E expr : \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>E expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  collection_part_typing_det:
    "\<Gamma> \<turnstile>\<^sub>C prt : \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>C prt : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  iterator_typing_det:
    "\<Gamma> \<turnstile>\<^sub>I (src, its, body) : xs \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys \<Longrightarrow> xs = ys" and
  expr_list_typing_det:
    "\<Gamma> \<turnstile>\<^sub>L exprs : \<pi> \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>L exprs : \<xi> \<Longrightarrow> \<pi> = \<xi>"
proof (induct arbitrary: \<sigma> and \<sigma> and ys and \<xi>
       rule: typing_collection_part_typing_iterator_typing_expr_list_typing.inducts)
  case (NullLiteralT \<Gamma>) thus ?case by auto
next
  case (BooleanLiteralT \<Gamma> c) thus ?case by auto
next
  case (RealLiteralT \<Gamma> c) thus ?case by auto
next
  case (IntegerLiteralT \<Gamma> c) thus ?case by auto
next
  case (UnlimitedNaturalLiteralT \<Gamma> c) thus ?case by auto
next
  case (StringLiteralT \<Gamma> c) thus ?case by auto
next
  case (EnumLiteralT enum lit \<Gamma>) thus ?case by auto
next
  case (TupleLiteralNilT \<Gamma>) thus ?case by auto
next
  case (TupleLiteralConsT \<Gamma> el \<tau> \<sigma> \<rho> elems \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E Literal (TupleLiteral (el # elems)) : \<sigma> \<Longrightarrow> \<rho> \<squnion> \<upsilon> = \<sigma>"
    using TupleLiteralConsT.hyps(3) TupleLiteralConsT.hyps(5)
        TupleLiteralConsT.hyps(7) tuple_type_det(2) by fastforce
  thus ?case by (simp add: TupleLiteralConsT.prems)
next
  case (CollectionLiteralNilT k \<sigma> \<Gamma>) thus ?case
    using collection_type_det(2) by blast
next
  case (CollectionLiteralConsT k \<Gamma> x \<tau> \<sigma> xs \<rho>) thus ?case
    by (metis CollectionLiteralConsTE collection_type_det(2))
next
  case (CollectionPartItemT \<Gamma> a \<tau>) thus ?case by blast
next
  case (CollectionPartRangeT \<Gamma> a b) thus ?case by blast
next
  case (LowerErrorableCollectionPartRangeT \<Gamma> a b) thus ?case by blast
next
  case (UpperErrorableCollectionPartRangeT \<Gamma> a b) thus ?case by blast
next
  case (ErrorableCollectionPartRangeT \<Gamma> a b) thus ?case by blast
next
  case (MapNilT \<tau> \<Gamma>) thus ?case
    using map_type_det(2) by blast
next
  case (MapConsT \<Gamma> x \<tau> \<sigma> \<rho> xs \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E Literal (MapLiteral (x # xs)) : \<sigma> \<Longrightarrow> \<rho> \<squnion> \<upsilon> = \<sigma>"
    using MapConsT.hyps map_type_det(2) by blast
  thus ?case by (simp add: MapConsT.prems)
next
  case (LetT \<Gamma> init \<sigma> \<tau> v body \<rho>) thus ?case by blast
next
  case (VarT \<Gamma> v \<tau>) thus ?case by auto
next
  case (IfT \<Gamma> cnd thn \<sigma> els \<rho>) thus ?case by blast
next
  case (ErrorableIfT \<Gamma> cnd thn \<sigma> els \<rho>) thus ?case by blast
next
  case (MetaOperationCallT \<tau> op \<sigma> \<Gamma>) thus ?case
    by (meson MetaOperationCallTE mataop_type_det)
next
  case (StaticOperationCallT \<Gamma> params \<pi> \<tau> op oper)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op params : \<sigma> \<Longrightarrow>
        oper_type oper = \<sigma>"
    apply (erule StaticOperationCallTE)
    using StaticOperationCallT.hyps static_operation_det by blast+
  thus ?case by (simp add: StaticOperationCallT.prems)
next
  case (ErrorableStaticOperationCallT \<Gamma> params \<pi> \<tau> op oper)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op params : \<sigma> \<Longrightarrow>
        (oper_type oper)[!] = \<sigma>"
    apply (erule StaticOperationCallTE)
    using ErrorableStaticOperationCallT.hyps static_operation_det by blast+
  thus ?case by (simp add: ErrorableStaticOperationCallT.prems)
next
  case (TypeOperationCallT \<Gamma> a \<tau> k op \<sigma> \<rho>) thus ?case
    by (metis TypeOperationCallTE typeop_type_det)
next
  case (OperationCallT \<Gamma> src \<tau> params \<pi> op k \<sigma>) thus ?case
    by (metis OperationCallTE op_type_det)
next
  case (AttributeCallT \<Gamma> src \<C> "prop" \<D> \<tau>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AttributeCall src prop : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
    apply (erule AttributeCallTE)
    using AttributeCallT.hyps attribute_det by blast+
  thus ?case by (simp add: AttributeCallT.prems)
next
  case (ErrorableAttributeCallT \<Gamma> src \<C> "prop" \<D> \<tau>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AttributeCall src prop : \<sigma> \<Longrightarrow> \<tau>[!] = \<sigma>"
    apply (erule AttributeCallTE)
    using ErrorableAttributeCallT.hyps attribute_det by blast+
  thus ?case by (simp add: ErrorableAttributeCallT.prems)
next
  case (AssociationEndCallT \<Gamma> src \<C> "from" role \<D> "end")
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AssociationEndCall src from role : \<sigma> \<Longrightarrow>
        assoc_end_type end = \<sigma>"
    apply (erule AssociationEndCallTE)
    using AssociationEndCallT.hyps association_end_det by blast+
  thus ?case by (simp add: AssociationEndCallT.prems)
next
  case (ErrorableAssociationEndCallT \<Gamma> src \<C> "from" role \<D> "end")
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AssociationEndCall src from role : \<sigma> \<Longrightarrow>
        (assoc_end_type end)[!] = \<sigma>"
    apply (erule AssociationEndCallTE)
    using ErrorableAssociationEndCallT.hyps association_end_det by blast+
  thus ?case by (simp add: ErrorableAssociationEndCallT.prems)
next
  case (AssociationClassCallT \<Gamma> src \<C> "from" \<A> \<D>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AssociationClassCall src from \<A> : \<sigma> \<Longrightarrow>
        class_assoc_type \<A> = \<sigma>"
    apply (erule AssociationClassCallTE)
    using AssociationClassCallT.hyps by blast+
  thus ?case by (simp add: AssociationClassCallT.prems)
next
  case (ErrorableAssociationClassCallT \<Gamma> src \<C> "from" \<A> \<D>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AssociationClassCall src from \<A> : \<sigma> \<Longrightarrow>
        (class_assoc_type \<A>)[!] = \<sigma>"
    apply (erule AssociationClassCallTE)
    using ErrorableAssociationClassCallT.hyps by blast+
  thus ?case by (simp add: ErrorableAssociationClassCallT.prems)
next
  case (AssociationClassEndCallT \<Gamma> src \<A> role "end")
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src role : \<sigma> \<Longrightarrow>
        class_assoc_end_type end = \<sigma>"
    apply (erule AssociationClassEndCallTE)
    using AssociationClassEndCallT.hyps
          association_class_end_det by blast+
  thus ?case by (simp add: AssociationClassEndCallT.prems)
next
  case (ErrorableAssociationClassEndCallT \<Gamma> src \<A> role "end")
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src role : \<sigma> \<Longrightarrow>
        (class_assoc_end_type end)[!] = \<sigma>"
    apply (erule AssociationClassEndCallTE)
    using ErrorableAssociationClassEndCallT.hyps
          association_class_end_det by blast+
  thus ?case by (simp add: ErrorableAssociationClassEndCallT.prems)
next
  case (TupleElementCallT \<Gamma> src \<pi> elem \<tau>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E TupleElementCall src elem : \<sigma> \<Longrightarrow> ErrorFree \<tau> = \<sigma>"
    apply (erule TupleElementCallTE)
    using TupleElementCallT.hyps by force+
  thus ?case by (simp add: TupleElementCallT.prems)
next
  case (ErrorableTupleElementCallT \<Gamma> src \<pi> elem \<tau>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E TupleElementCall src elem : \<sigma> \<Longrightarrow> Errorable \<tau> = \<sigma>"
    apply (erule TupleElementCallTE)
    using ErrorableTupleElementCallT.hyps by force+
  thus ?case by (simp add: ErrorableTupleElementCallT.prems)
next
  case (CollectionLoopT \<Gamma> src \<tau> \<sigma> its_ty its body \<rho>)
  have "\<And>ys. \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_ty, None), body) : ys \<Longrightarrow>
        (\<tau>, \<sigma>, \<rho>) = ys"
    apply (erule LoopTE)
    using CollectionLoopT.hyps(2) CollectionLoopT.hyps(3)
          CollectionLoopT.hyps(7) any_collection_type_det apply fastforce
    using CollectionLoopT.hyps(2) CollectionLoopT.hyps(3)
          collection_type_det(1) by blast
  thus ?case by (simp add: CollectionLoopT.prems)
next
  case (MapLoopT \<Gamma> src \<tau> \<sigma> \<upsilon> its_key_ty its_val_ty its body \<rho>)
  have "\<And>ys. \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_key_ty, Some its_val_ty), body) : ys \<Longrightarrow>
        (\<tau>, \<sigma>, \<rho>) = ys"
    apply (erule LoopTE, auto simp add: MapLoopT.hyps)
    using MapLoopT.hyps(2) MapLoopT.hyps(3) map_type_det(1) by blast
  thus ?case by (simp add: MapLoopT.prems)
next
  case (IterateT \<Gamma> src its its_ty res res_t res_init body \<tau> \<sigma> \<rho>) thus ?case by blast
next
  case (AnyIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case by blast
next
  case (ClosureIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> k \<phi> \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<upsilon> = \<sigma>"
    apply (erule ClosureIterationTE)
    by (metis ClosureIterationT.hyps(2) ClosureIterationT.hyps(4)
              ClosureIterationT.hyps(7) Pair_inject collection_type_det(1)
              unique_collection_type_det)
  thus ?case by (simp add: ClosureIterationT.prems)
next
  case (CollectionCollectIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<rho>' k \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E CollectIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<upsilon> = \<sigma>"
    apply (erule CollectIterationTE)
    apply (metis CollectionCollectIterationT.hyps(2)
                 CollectionCollectIterationT.hyps(4)
                 CollectionCollectIterationT.hyps(5)
                 CollectionCollectIterationT.hyps(6)
                 Pair_inject collection_type_det(1)
                 non_unique_collection_type_det to_single_type_det)
    by (metis CollectionCollectIterationT.hyps(2)
              CollectionCollectIterationT.hyps(5)
              Pair_inject collection_type_and_map_type_distinct)
  thus ?case by (simp add: CollectionCollectIterationT.prems)
next
  case (MapCollectIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> uz va \<rho>' \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E CollectIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<upsilon> = \<sigma>"
    apply (erule CollectIterationTE)
    using MapCollectIterationT.hyps(2) MapCollectIterationT.hyps(5)
          collection_type_and_map_type_distinct apply fastforce
    using MapCollectIterationT.hyps(2) MapCollectIterationT.hyps(4)
          MapCollectIterationT.hyps(6) collection_type_det(2)
          to_single_type_det by fastforce
  thus ?case by (simp add: MapCollectIterationT.prems)
next
  case (CollectByIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E CollectByIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<upsilon> = \<sigma>"
    apply (erule CollectByIterationTE)
    using CollectByIterationT.hyps map_type_det(2) by fastforce
  thus ?case by (simp add: CollectByIterationT.prems)
next
  case (CollectionCollectNestedIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon> \<phi>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<phi> = \<sigma>"
    apply (erule CollectNestedIterationTE)
    apply (metis CollectionCollectNestedIterationT.hyps(2)
                 CollectionCollectNestedIterationT.hyps(4)
                 CollectionCollectNestedIterationT.hyps(5)
                 Pair_inject collection_type_det(1) non_unique_collection_type_det)
    using CollectionCollectNestedIterationT.hyps(2)
          CollectionCollectNestedIterationT.hyps(4)
          collection_type_and_map_type_distinct by fastforce
  thus ?case by (simp add: CollectionCollectNestedIterationT.prems)
next
  case (MapCollectNestedIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon> vb \<phi>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<phi> = \<sigma>"
    apply (erule CollectNestedIterationTE)
    using MapCollectNestedIterationT.hyps(2)
          MapCollectNestedIterationT.hyps(4)
          collection_type_and_map_type_distinct apply fastforce
    using MapCollectNestedIterationT.hyps(2)
          MapCollectNestedIterationT.hyps(4)
          MapCollectNestedIterationT.hyps(5)
          map_type_det(1) map_type_det(2) by fastforce
  thus ?case by (simp add: MapCollectNestedIterationT.prems)
next
  case (ExistsIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case
    by (metis ExistsIterationTE snd_conv)
next
  case (ForAllIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case
    by (metis ForAllIterationTE snd_conv)
next
  case (OneIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case by blast
next
  case (IsUniqueIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case by blast
next
  case (SelectIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case by blast
next
  case (RejectIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case by blast
next
  case (SortedByIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> k \<upsilon>)
  have "\<And>\<sigma>. \<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src its its_ty body : \<sigma> \<Longrightarrow> \<upsilon> = \<sigma>"
    apply (erule SortedByIterationTE)
    by (metis Pair_inject SortedByIterationT.hyps(2)
              SortedByIterationT.hyps(4) SortedByIterationT.hyps(5)
              collection_type_det(1) ordered_collection_type_det(2))
  thus ?case by (simp add: SortedByIterationT.prems)
next
  case (ExprListNilT \<Gamma>) thus ?case by auto
next
  case (ExprListConsT \<Gamma> expr \<tau> exprs \<pi>) thus ?case by blast
qed

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred [show_modes] mataop_type .
code_pred [show_modes] typeop_type .
code_pred [show_modes] non_strict_op .
code_pred [show_modes] op_type .
code_pred (modes:
    typing: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
    iterator_typing: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
    expr_list_typing: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
    collection_part_typing: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] typing .

end

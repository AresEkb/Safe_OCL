(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Typing\<close>
theory OCL_Typing
  imports OCL_Object_Model "HOL-Library.Transitive_Closure_Table"
begin

inductive non_strict_op :: "op \<Rightarrow> bool" where
  "non_strict_op OclIsUndefinedOp"
| "non_strict_op OclIsInvalidOp"
| "non_strict_op AndOp"
| "non_strict_op OrOp"
| "non_strict_op XorOp"
| "non_strict_op ImpliesOp"

abbreviation "strict_op op \<equiv> \<not> non_strict_op op"



text \<open>
  The following rules are more restrictive than rules given in
  the OCL specification. This allows one to identify more errors
  in expressions. However, these restrictions may be revised if necessary.
  Perhaps some of them could be separated and should cause warnings
  instead of errors.\<close>

(*** Operations Typing ******************************************************)

section \<open>Operations Typing\<close>

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
  "is_finite_type\<^sub>N \<tau> \<Longrightarrow>
   mataop_type (ErrorFree \<tau>) AllInstancesOp (Set \<tau>)[1]"

subsection \<open>Type Operations\<close>

text \<open>
  At first we decided to allow casting only to subtypes.
  However sometimes it is necessary to cast expressions to supertypes,
  for example, to access overridden attributes of a supertype.
  So we allow casting to subtypes and supertypes.
  Casting to other types is meaningless.\<close>

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

(* TODO: Для коллекций и возможно кортежей ошибка должна подниматься наверх *)

inductive is_unsafe_cast\<^sub>T where
  "is_unsafe_cast\<^sub>T UnlimitedNatural Integer"
| "is_unsafe_cast\<^sub>T UnlimitedNatural Real"

inductive is_unsafe_cast\<^sub>N where
  "is_unsafe_cast\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   is_unsafe_cast\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "is_unsafe_cast\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   is_unsafe_cast\<^sub>N (Required \<tau>) (Optional \<sigma>)"
| "is_unsafe_cast\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   is_unsafe_cast\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

inductive is_unsafe_cast where
  "is_unsafe_cast\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   is_unsafe_cast (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "is_unsafe_cast\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   is_unsafe_cast (ErrorFree \<tau>) (Errorable \<sigma>)"
| "is_unsafe_cast\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   is_unsafe_cast (Errorable \<tau>) (Errorable \<sigma>)"

inductive typeop_type where
  "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> (to_errorable \<sigma>)"
| "\<tau> < \<sigma> \<Longrightarrow> is_unsafe_cast \<tau> \<sigma> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> (to_errorable \<sigma>)"
| "\<tau> < \<sigma> \<Longrightarrow> \<not> is_unsafe_cast \<tau> \<sigma> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> \<sigma>"

| "\<sigma> < \<tau> \<Longrightarrow>
   is_required_type \<tau> \<Longrightarrow>
   is_error_free \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsTypeOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   is_optional_type \<tau> \<or> is_errorable_type \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsTypeOfOp \<tau> \<sigma> Boolean[1!]"

| "\<sigma> < \<tau> \<Longrightarrow>
   is_required_type \<tau> \<Longrightarrow>
   is_error_free \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsKindOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   is_optional_type \<tau> \<or> is_errorable_type \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsKindOfOp \<tau> \<sigma> Boolean[1!]"

| "is_required_type \<tau> \<Longrightarrow>
   is_error_free \<sigma> \<Longrightarrow>
   element_type \<tau> \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<upsilon> \<Longrightarrow>
   typeop_type ArrowCall SelectByKindOp \<tau> \<sigma> \<upsilon>"

| "is_required_type \<tau> \<Longrightarrow>
   is_error_free \<sigma> \<Longrightarrow>
   element_type \<tau> \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<upsilon> \<Longrightarrow>
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
  "\<not> is_collection_type \<tau> \<Longrightarrow>
   any_unop_type OclAsSetOp \<tau> (map_errorable_type (\<lambda>\<tau>. (Set \<tau>)[1]\<^sub>N) (to_required_type \<tau>))"

| "is_object_type \<tau> \<Longrightarrow>
   any_unop_type OclIsNewOp \<tau> Boolean[1]"

| "is_optional_type \<tau> \<or> is_errorable_type \<tau> \<Longrightarrow>
   any_unop_type OclIsUndefinedOp \<tau> Boolean[1]"

| "is_errorable_type \<tau> \<Longrightarrow>
   any_unop_type OclIsInvalidOp \<tau> Boolean[1]"

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
  Please take a note that @{text "abs()"} is not defined for
  @{text "UnlimitedNatural"}. @{text "floor()"}, @{text "round()"} are
  also undefined for @{text "Integer"}. At first glance, this contradicts
  the fact that types must inherit operations from their super types.
  However, it makes no sense to apply these operations in this way.
  The purpose of the type system is to reduce errors in programs.
  Probably, numeric types should not form such a hierarchy.\<close>

text \<open>
  The difference between @{text "oclAsType(Integer)"} and
  @{text "toInteger()"} for unlimited naturals is unclear.\<close>

inductive numeric_unop_type where
  "numeric_unop_type UMinusOp Real[1] Real[1]"
| "numeric_unop_type UMinusOp Integer[1] Integer[1]"
| "numeric_unop_type UMinusOp UnlimitedNatural[1] Integer[1]"

| "numeric_unop_type AbsOp Real[1] Real[1]"
| "numeric_unop_type AbsOp Integer[1] Integer[1]"

| "numeric_unop_type FloorOp Real[1] Integer[1]"
| "numeric_unop_type RoundOp Real[1] Integer[1]"

| "numeric_unop_type numeric_unop.ToIntegerOp UnlimitedNatural[1] Integer[1!]"

inductive numeric_binop_type where
  "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> \<rho>"

| "\<tau> \<squnion> \<sigma> = Real[1] \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> Integer[1]"

| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> \<rho>"

| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type DivideOp \<tau> \<sigma> Real[1!]"

| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_binop_type DivOp \<tau> \<sigma> (to_errorable \<rho>)"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   numeric_binop_type ModOp \<tau> \<sigma> (to_errorable \<rho>)"

| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MaxOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> \<rho> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type MinOp \<tau> \<sigma> \<rho>"

| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.LessOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.LessEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterOp \<tau> \<sigma> Boolean[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterEqOp \<tau> \<sigma> Boolean[1]"

subsection \<open>String Operations\<close>

inductive string_unop_type where
  "string_unop_type SizeOp String[1] Integer[1]"
| "string_unop_type CharactersOp String[1] (Sequence String[1]\<^sub>N)[1]"
| "string_unop_type ToUpperCaseOp String[1] String[1]"
| "string_unop_type ToLowerCaseOp String[1] String[1]"
| "string_unop_type ToBooleanOp String[1] Boolean[1!]"
| "string_unop_type ToRealOp String[1] Real[1!]"
| "string_unop_type ToIntegerOp String[1] Integer[1!]"

inductive string_binop_type where
  "string_binop_type ConcatOp String[1] String[1] String[1]"
| "string_binop_type EqualsIgnoreCaseOp String[1] String[1] Boolean[1]"
| "string_binop_type LessOp String[1] String[1] Boolean[1]"
| "string_binop_type LessEqOp String[1] String[1] Boolean[1]"
| "string_binop_type GreaterOp String[1] String[1] Boolean[1]"
| "string_binop_type GreaterEqOp String[1] String[1] Boolean[1]"
| "string_binop_type IndexOfOp String[1] String[1] Integer[1]"
| "\<tau> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   string_binop_type AtOp String[1] \<tau> String[1!]"

inductive string_ternop_type where
  "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   string_ternop_type SubstringOp String[1] \<sigma> \<rho> String[1!]"

subsection \<open>Collection Operations\<close>

text \<open>
  Please take a note, that @{text "flatten()"} preserves a collection kind.\<close>

inductive collection_unop_type where
  "is_collection_type \<tau> \<Longrightarrow>
   is_required_type \<tau> \<Longrightarrow>
   collection_unop_type CollectionSizeOp \<tau> Integer[1]"
| "is_collection_type \<tau> \<Longrightarrow>
   is_required_type \<tau> \<Longrightarrow>
   collection_unop_type IsEmptyOp \<tau> Boolean[1]"
| "is_collection_type \<tau> \<Longrightarrow>
   is_required_type \<tau> \<Longrightarrow>
   collection_unop_type NotEmptyOp \<tau> Boolean[1]"

| "element_type \<tau> \<sigma> \<Longrightarrow> is_required_type \<tau> \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow> is_required_type \<tau> \<Longrightarrow> operation \<sigma> STR ''max'' [\<sigma>] oper \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> \<sigma>"

| "element_type \<tau> \<sigma> \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow> operation \<sigma> STR ''min'' [\<sigma>] oper \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> \<sigma>"

| "element_type \<tau> \<sigma> \<Longrightarrow> \<sigma> = UnlimitedNatural[1]\<midarrow>Real[1] \<Longrightarrow>
   collection_unop_type SumOp \<tau> \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow> operation \<sigma> STR ''+'' [\<sigma>] oper \<Longrightarrow>
   collection_unop_type SumOp \<tau> \<sigma>"

| "element_type \<tau>[1] (ErrorFree \<sigma>) \<Longrightarrow>
   collection_unop_type AsSetOp \<tau>[1] (Set \<sigma>)[1]"
| "element_type \<tau>[1] (ErrorFree \<sigma>) \<Longrightarrow>
   collection_unop_type AsOrderedSetOp \<tau>[1] (OrderedSet \<sigma>)[1]"
| "element_type \<tau>[1] (ErrorFree \<sigma>) \<Longrightarrow>
   collection_unop_type AsBagOp \<tau>[1] (Bag \<sigma>)[1]"
| "element_type \<tau>[1] (ErrorFree \<sigma>) \<Longrightarrow>
   collection_unop_type AsSequenceOp \<tau>[1] (Sequence \<sigma>)[1]"

| "inner_element_type \<tau> \<rho> \<Longrightarrow>
   update_element_type \<tau> \<rho> \<sigma> \<Longrightarrow>
   collection_unop_type FlattenOp \<tau> \<sigma>"

| "collection_unop_type FirstOp (OrderedSet \<tau>)[1] (Errorable \<tau>)"
| "collection_unop_type FirstOp (Sequence \<tau>)[1] (Errorable \<tau>)"
| "collection_unop_type LastOp (OrderedSet \<tau>)[1] (Errorable \<tau>)"
| "collection_unop_type LastOp (Sequence \<tau>)[1] (Errorable \<tau>)"
| "collection_unop_type ReverseOp (OrderedSet \<tau>)[1] (OrderedSet \<tau>)[1]"
| "collection_unop_type ReverseOp (Sequence \<tau>)[1] (Sequence \<tau>)[1]"

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

inductive collection_binop_type where
  "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type IncludesOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type ExcludesOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type CountOp \<tau> \<sigma> Integer[1]"

| "element_type \<tau> \<rho> \<Longrightarrow> element_type \<sigma> \<upsilon> \<Longrightarrow> \<upsilon> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type IncludesAllOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow> element_type \<sigma> \<upsilon> \<Longrightarrow> \<upsilon> \<le> to_optional_type_nested \<rho> \<Longrightarrow>
   collection_binop_type ExcludesAllOp \<tau> \<sigma> Boolean[1]"

| "element_type \<tau> (ErrorFree \<rho>) \<Longrightarrow> element_type \<sigma> (ErrorFree \<upsilon>) \<Longrightarrow>
   collection_binop_type ProductOp \<tau> \<sigma>
      (Set (Tuple (fmap_of_list [(STR ''first'', \<rho>), (STR ''second'', \<upsilon>)]))[1]\<^sub>N)[1]"

| "collection_binop_type UnionOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "collection_binop_type UnionOp (Set \<tau>)[1] (Bag \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"
| "collection_binop_type UnionOp (Bag \<tau>)[1] (Set \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"
| "collection_binop_type UnionOp (Bag \<tau>)[1] (Bag \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"

| "collection_binop_type IntersectionOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "collection_binop_type IntersectionOp (Set \<tau>)[1] (Bag \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "collection_binop_type IntersectionOp (Bag \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"
| "collection_binop_type IntersectionOp (Bag \<tau>)[1] (Bag \<sigma>)[1] (Bag (\<tau> \<squnion> \<sigma>))[1]"

| "\<tau> \<le> \<sigma> \<or> \<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type SetMinusOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set \<tau>)[1]"
| "collection_binop_type SymmetricDifferenceOp (Set \<tau>)[1] (Set \<sigma>)[1] (Set (\<tau> \<squnion> \<sigma>))[1]"

| "element_type \<tau> \<rho> \<Longrightarrow> update_element_type \<tau> (\<rho> \<squnion> \<sigma>) \<upsilon> \<Longrightarrow>
   collection_binop_type IncludingOp \<tau> \<sigma> \<upsilon>"
| "element_type \<tau> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow>
   collection_binop_type ExcludingOp \<tau> \<sigma> \<tau>"

| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type AppendOp (OrderedSet \<tau>)[1] (ErrorFree \<sigma>) (OrderedSet \<tau>)[1]"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type AppendOp (Sequence \<tau>)[1] (ErrorFree \<sigma>) (Sequence \<tau>)[1]"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type PrependOp (OrderedSet \<tau>)[1] (ErrorFree \<sigma>) (OrderedSet \<tau>)[1]"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type PrependOp (Sequence \<tau>)[1] (ErrorFree \<sigma>) (Sequence \<tau>)[1]"

| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_binop_type CollectionAtOp (OrderedSet \<tau>)[1] \<sigma> (Errorable \<tau>)"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_binop_type CollectionAtOp (Sequence \<tau>)[1] \<sigma> (Errorable \<tau>)"

| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (OrderedSet \<tau>)[1] (ErrorFree \<sigma>) Integer[1]"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (Sequence \<tau>)[1] (ErrorFree \<sigma>) Integer[1]"

(*code_pred [show_modes] collection_binop_type .*)

inductive collection_ternop_type where
  "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow> \<rho> \<le> \<tau> \<Longrightarrow>
   collection_ternop_type InsertAtOp (OrderedSet \<tau>)[1] \<sigma> (ErrorFree \<rho>) (OrderedSet \<tau>)[1!]"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow> \<rho> \<le> \<tau> \<Longrightarrow>
   collection_ternop_type InsertAtOp (Sequence \<tau>)[1] \<sigma> (ErrorFree \<rho>) (Sequence \<tau>)[1!]"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_ternop_type SubOrderedSetOp (OrderedSet \<tau>)[1] \<sigma> \<rho> (OrderedSet \<tau>)[1!]"
| "\<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<rho> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   collection_ternop_type SubSequenceOp (Sequence \<tau>)[1] \<sigma> \<rho> (Sequence \<tau>)[1!]"

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
| "collection_unop_type op \<tau> \<sigma> \<Longrightarrow>
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
| "collection_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inr op)))) ArrowCall \<tau> \<sigma> \<rho>"

inductive ternop_type where
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inl op) DotCall \<tau> \<sigma> \<rho> \<upsilon>"
| "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inr op) ArrowCall \<tau> \<sigma> \<rho> \<upsilon>"
(*
code_pred [show_modes] unop_type .
code_pred [show_modes] binop_type .
code_pred [show_modes] ternop_type .
*)

definition "op_result_type_is_errorable op \<pi> \<equiv>
  strict_op op \<and> fBex \<pi> is_errorable_type"

inductive op_type where
  "unop_type op k (to_error_free \<tau>) \<upsilon> \<Longrightarrow>
   op_result_type_is_errorable (Inl op) {|\<tau>|} \<Longrightarrow>
   op_type (Inl op) k \<tau> [] (to_errorable \<upsilon>)"
| "unop_type op k (to_error_free \<tau>) \<upsilon> \<Longrightarrow>
   \<not> op_result_type_is_errorable (Inl op) {|\<tau>|} \<Longrightarrow>
   op_type (Inl op) k \<tau> [] \<upsilon>"

| "binop_type op k (to_error_free \<tau>) (to_error_free \<sigma>) \<upsilon> \<Longrightarrow>
   op_result_type_is_errorable (Inr (Inl op)) {|\<tau>, \<sigma>|} \<Longrightarrow>
   op_type (Inr (Inl op)) k \<tau> [\<sigma>] (to_errorable \<upsilon>)"
| "binop_type op k (to_error_free \<tau>) (to_error_free \<sigma>) \<upsilon> \<Longrightarrow>
   \<not> op_result_type_is_errorable (Inr (Inl op)) {|\<tau>, \<sigma>|} \<Longrightarrow>
   op_type (Inr (Inl op)) k \<tau> [\<sigma>] \<upsilon>"

| "ternop_type op k (to_error_free \<tau>) (to_error_free \<sigma>) (to_error_free \<rho>) \<upsilon> \<Longrightarrow>
   op_result_type_is_errorable (Inr (Inr (Inl op))) {|\<tau>, \<sigma>, \<rho>|} \<Longrightarrow>
   op_type (Inr (Inr (Inl op))) k \<tau> [\<sigma>, \<rho>] (to_errorable \<upsilon>)"
| "ternop_type op k (to_error_free \<tau>) (to_error_free \<sigma>) (to_error_free \<rho>) \<upsilon> \<Longrightarrow>
   \<not> op_result_type_is_errorable (Inr (Inr (Inl op))) {|\<tau>, \<sigma>, \<rho>|} \<Longrightarrow>
   op_type (Inr (Inr (Inl op))) k \<tau> [\<sigma>, \<rho>] \<upsilon>"

| "operation \<tau> op \<pi> oper \<Longrightarrow>
   op_type (Inr (Inr (Inr op))) DotCall \<tau> \<pi> (oper_type oper)"

(* TODO: Remove *)
code_pred [show_modes] op_type .

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
"collection_unop_type op \<tau> \<sigma>"

"any_binop_type op \<tau> \<sigma> \<rho>"
"boolean_binop_type op \<tau> \<sigma> \<rho>"
"numeric_binop_type op \<tau> \<sigma> \<rho>"
"string_binop_type op \<tau> \<sigma> \<rho>"
"collection_binop_type op \<tau> \<sigma> \<rho>"

"string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"
"collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"

(*** Determinism ************************************************************)

subsection \<open>Determinism\<close>

lemma mataop_type_det:
  "mataop_type \<tau> op \<sigma> \<Longrightarrow>
   mataop_type \<tau> op \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: mataop_type.simps)

lemma typeop_type_det:
  "typeop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   typeop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: typeop_type.induct;
      auto simp add: typeop_type.simps update_element_type_det)

lemma any_unop_type_det:
  "any_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   any_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: any_unop_type.induct; simp add: any_unop_type.simps)

lemma boolean_unop_type_det:
  "boolean_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   boolean_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: boolean_unop_type.induct; simp add: boolean_unop_type.simps)

lemma numeric_unop_type_det:
  "numeric_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   numeric_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: numeric_unop_type.induct; auto simp add: numeric_unop_type.simps)

lemma string_unop_type_det:
  "string_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   string_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: string_unop_type.induct; simp add: string_unop_type.simps)

lemma collection_unop_type_det:
  "collection_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   collection_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  apply (simp add: collection_unop_type.simps)
  using element_type_det apply auto
  using update_element_type_det inner_element_type_det by blast

lemma unop_type_det:
  "unop_type op k \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   unop_type op k \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: unop_type.induct;
      simp add: unop_type.simps any_unop_type_det
                boolean_unop_type_det numeric_unop_type_det
                string_unop_type_det collection_unop_type_det)

lemma any_binop_type_det:
  "any_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   any_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: any_binop_type.induct; auto simp add: any_binop_type.simps)

lemma boolean_binop_type_det:
  "boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: boolean_binop_type.induct; simp add: boolean_binop_type.simps)

lemma numeric_binop_type_det:
  "numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: numeric_binop_type.induct;
      auto simp add: numeric_binop_type.simps split: if_splits)

lemma string_binop_type_det:
  "string_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   string_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: string_binop_type.induct; simp add: string_binop_type.simps)

lemma collection_binop_type_det:
  "collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (induct rule: collection_binop_type.induct; simp add: collection_binop_type.simps)
  using element_type_det update_element_type_det by blast+

lemma binop_type_det:
  "binop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   binop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: binop_type.induct;
      simp add: binop_type.simps any_binop_type_det
                boolean_binop_type_det numeric_binop_type_det
                string_binop_type_det collection_binop_type_det)

lemma string_ternop_type_det:
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: string_ternop_type.induct; simp add: string_ternop_type.simps)

lemma collection_ternop_type_det:
  "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: collection_ternop_type.induct; simp add: collection_ternop_type.simps)

lemma ternop_type_det:
  "ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: ternop_type.induct;
      simp add: ternop_type.simps string_ternop_type_det collection_ternop_type_det)

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

inductive map_type\<^sub>T where
  "map_type\<^sub>T (Map \<sigma> \<rho>) \<sigma> \<rho>"

inductive map_type\<^sub>N where
  "map_type\<^sub>T \<tau> \<sigma> \<rho> \<Longrightarrow>
   map_type\<^sub>N (Required \<tau>) \<sigma> \<rho> False"
| "map_type\<^sub>T \<tau> \<sigma> \<rho> \<Longrightarrow>
   map_type\<^sub>N (Optional \<tau>) \<sigma> \<rho> True"

(* Тут нужен комментарий, почему мы спускаем ошибочность до элементов *)

inductive map_type where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> nullable \<Longrightarrow>
   map_type (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) nullable"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> nullable \<Longrightarrow>
   map_type (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) nullable"

inductive map_type' where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> nullable \<Longrightarrow>
   map_type' (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) nullable"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> nullable \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (ErrorFree \<rho>) nullable"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> nullable \<Longrightarrow>
   map_type' (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>) nullable"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> nullable \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) nullable"

code_pred [show_modes] map_type .
code_pred [show_modes] map_type' .

values "{(x, y, n). map_type (Map (Boolean[1]\<^sub>N :: nat type\<^sub>N) Integer[?]\<^sub>N)[1] x y n}"
values "{(x, y, n). map_type (Map (Boolean[1]\<^sub>N :: nat type\<^sub>N) Integer[?]\<^sub>N)[1!] x y n}"
values "{(x, y, n). map_type (Map (Boolean[1]\<^sub>N :: nat type\<^sub>N) Integer[?]\<^sub>N)[?] x y n}"
values "{x. map_type' x (Boolean[1] :: nat type\<^sub>N\<^sub>E) Integer[?] False}"
values "{x. map_type' x (Boolean[1] :: nat type\<^sub>N\<^sub>E) Integer[?] True}"
values "{x. map_type' x (Boolean[1!] :: nat type\<^sub>N\<^sub>E) Integer[?!] True}"
values "{x. map_type' x (Boolean[1] :: nat type\<^sub>N\<^sub>E) Integer[?!] True}"

inductive collection_type\<^sub>T where
  "collection_type\<^sub>T (Collection \<tau>) CollectionKind \<tau>"
| "collection_type\<^sub>T (Set \<tau>) SetKind \<tau>"
| "collection_type\<^sub>T (OrderedSet \<tau>) OrderedSetKind \<tau>"
| "collection_type\<^sub>T (Bag \<tau>) BagKind \<tau>"
| "collection_type\<^sub>T (Sequence \<tau>) SequenceKind \<tau>"

inductive collection_type\<^sub>N where
  "collection_type\<^sub>T \<tau> k \<sigma> \<Longrightarrow>
   collection_type\<^sub>N (Required \<tau>) k \<sigma> False"
| "collection_type\<^sub>T \<tau> k \<sigma> \<Longrightarrow>
   collection_type\<^sub>N (Optional \<tau>) k \<sigma> True"

inductive collection_type where
  "collection_type\<^sub>N \<tau> k \<sigma> nullable \<Longrightarrow>
   collection_type (ErrorFree \<tau>) k (ErrorFree \<sigma>) nullable"
| "collection_type\<^sub>N \<tau> k \<sigma> nullable \<Longrightarrow>
   collection_type (Errorable \<tau>) k (Errorable \<sigma>) nullable"

code_pred [show_modes] collection_type .

values "{(k, x, n). collection_type (Set (Boolean[1]\<^sub>N :: nat type\<^sub>N))[1] k x n}"
values "{(k, x, n). collection_type (Set (Boolean[1]\<^sub>N :: nat type\<^sub>N))[?!] k x n}"
values "{x. collection_type x BagKind (Boolean[?] :: nat type\<^sub>N\<^sub>E) False}"
values "{x. collection_type x SetKind (Boolean[1!] :: nat type\<^sub>N\<^sub>E) True}"

inductive tuple_type\<^sub>T
      and tuple_type\<^sub>N where
  "tuple_type\<^sub>T (Tuple \<pi>) \<pi>"

| "tuple_type\<^sub>T \<tau> \<pi> \<Longrightarrow>
   tuple_type\<^sub>N (Required \<tau>) \<pi> False"
| "tuple_type\<^sub>T \<tau> \<pi> \<Longrightarrow>
   tuple_type\<^sub>N (Optional \<tau>) \<pi> True"

(* Тут нужен комментарий, почему мы спускаем ошибочность до элементов *)

inductive tuple_type where
  "tuple_type\<^sub>N \<tau> \<pi> nullable \<Longrightarrow>
   tuple_type (ErrorFree \<tau>) (fmmap ErrorFree \<pi>) nullable"
| "tuple_type\<^sub>N \<tau> \<pi> nullable \<Longrightarrow>
   tuple_type (Errorable \<tau>) (fmmap Errorable \<pi>) nullable"

inductive tuple_type' where
  "tuple_type\<^sub>N \<tau> (fmmap unwrap_errorable_type \<pi>) nullable \<Longrightarrow>
   \<not> fBex (fmran \<pi>) is_errorable_type \<Longrightarrow>
   tuple_type' (ErrorFree \<tau>) \<pi> nullable"
| "tuple_type\<^sub>N \<tau> (fmmap unwrap_errorable_type \<pi>) nullable \<Longrightarrow>
   fBex (fmran \<pi>) is_errorable_type \<Longrightarrow>
   tuple_type' (Errorable \<tau>) \<pi> nullable"

(* Доказать эквивалентность предикатов *)

term fBex
term to_errorable
term unwrap_errorable_type

code_pred [show_modes] tuple_type .
code_pred [show_modes] tuple_type' .

values "{x. tuple_type' x (fmempty(STR ''a'' \<mapsto>\<^sub>f Boolean[1] :: nat type\<^sub>N\<^sub>E)
  (STR ''b'' \<mapsto>\<^sub>f Real[1] :: nat type\<^sub>N\<^sub>E)) False}"
values "{x. tuple_type' x (fmempty(STR ''a'' \<mapsto>\<^sub>f Boolean[1!] :: nat type\<^sub>N\<^sub>E)
  (STR ''b'' \<mapsto>\<^sub>f Real[?] :: nat type\<^sub>N\<^sub>E)) False}"
values "{(x, n). tuple_type (Tuple (fmap_of_list
  [(STR ''a'', Boolean[1]\<^sub>N :: nat type\<^sub>N), (STR ''b'', Real[1]\<^sub>N)]))[1] x n}"
values "{(x, n). tuple_type (Tuple (fmap_of_list
  [(STR ''a'', Boolean[1]\<^sub>N :: nat type\<^sub>N), (STR ''b'', Real[1]\<^sub>N)]))[?!] x n}"

code_pred [show_modes] is_unsafe_cast . 
code_pred [show_modes] typeop_type . 
code_pred [show_modes] mataop_type .

term filter


abbreviation "iterators its \<tau> \<equiv>
  fmap_of_list (map (\<lambda>it. (fst it, \<tau>)) its)"

abbreviation "coiterators its \<tau> \<equiv>
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
  "has_literal enum lit \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E EnumLiteral enum lit : (Enum enum)[1]"

\<comment> \<open>Collection Literals\<close>

|CollectionLiteralNilT:
  "k \<noteq> CollectionKind \<Longrightarrow>
   collection_type \<sigma> k OclVoid[1] False \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral k [] : \<sigma>"
|CollectionLiteralConsT:
  "k \<noteq> CollectionKind \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C x : \<tau> \<Longrightarrow>
   collection_type \<sigma> k \<tau> False \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral k xs : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectionLiteral k (x # xs) : \<tau> \<squnion> \<sigma>"

|CollectionPartItemT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionItem a : \<tau>"
|CollectionPartRangeT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E b : \<sigma> \<Longrightarrow>
   \<tau> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<sigma> = UnlimitedNatural[1]\<midarrow>Integer[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>C CollectionRange a b : Integer[1]"

\<comment> \<open>Map Literals\<close>

(* Я думаю, стоит доказать, что система типов - это полная решетка.
   И сказать что-то про наименьшие элементы (вообще, для коллекций, отображений),
   чтобы показать, что такие правила обоснованы.
   И про наибольшие написать (вообще, для кортежей, коллекций, ...)

   Возможно стоит доказать, что некоторые правила всегда возвращают нужные типы.
   Сейчас это не очевидно, там просто задан "начальный" элемент и операция супремума *)

|MapNilT:
  "map_type' \<tau> OclVoid[1] OclVoid[1] False \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MapLiteral [] : \<tau>"
|MapConsT:
  "\<Gamma> \<turnstile>\<^sub>E map_literal_element_key x : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E map_literal_element_value x : \<sigma> \<Longrightarrow>
   map_type' \<rho> \<tau> \<sigma> False \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MapLiteral xs : \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MapLiteral (x # xs) : \<rho> \<squnion> \<upsilon>"

\<comment> \<open>Tuple Literals\<close>

|TupleLiteralNilT:
  "\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : (Tuple fmempty)[1]"
|TupleLiteralConsT:
  "\<Gamma> \<turnstile>\<^sub>E tuple_literal_element_expr el : \<tau> \<Longrightarrow>
   tuple_literal_element_type el = Some \<sigma> \<Longrightarrow>
   \<tau> \<le> \<sigma> \<Longrightarrow>
   tuple_type' \<rho> (fmap_of_list [(tuple_literal_element_name el, \<sigma>)]) False \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleLiteral elems : \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleLiteral (el # elems) : \<rho> \<squnion> \<upsilon>"

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
  "\<Gamma> \<turnstile>\<^sub>E a : Boolean[1] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E b : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E c : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E If a b c : \<sigma> \<squnion> \<rho>"

\<comment> \<open>Call Expressions\<close>

|MetaOperationCallT:
  "mataop_type \<tau> op \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
|StaticOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   static_operation \<tau> op \<pi> oper \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op params : oper_type oper"

|TypeOperationCallT:
  "\<Gamma> \<turnstile>\<^sub>E a : \<tau> \<Longrightarrow>
   typeop_type k op \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<rho>"

|AttributeCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   attribute \<C> prop \<D> \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AttributeCall src DotCall prop : \<tau>"
|AssociationEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   association_end \<C> from role \<D> end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationEndCall src DotCall from role : assoc_end_type end"
|AssociationClassCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   referred_by_association_class \<C> from \<A> \<D> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassCall src DotCall from \<A> : class_assoc_type \<A>"
|AssociationClassEndCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<langle>\<A>\<rangle>\<^sub>\<T>[1] \<Longrightarrow>
   association_class_end \<A> role end \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src DotCall role : class_assoc_end_type end"
|OperationCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L params : \<pi> \<Longrightarrow>
   op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<sigma>"

|TupleElementCallT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<sigma> \<Longrightarrow>
   tuple_type \<sigma> \<pi> n \<Longrightarrow>
   fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E TupleElementCall src DotCall elem : \<tau>"

\<comment> \<open>Iterator Expressions\<close>

|CollectionIterationT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   collection_type \<tau> _ \<sigma> _ \<Longrightarrow>
   \<sigma> \<le> its_ty \<Longrightarrow>
   list_all (\<lambda>it. snd it = None) its \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its its_ty \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_ty, None), body) : (\<tau>, \<sigma>, \<rho>)"
|MapIterationT:
  "\<Gamma> \<turnstile>\<^sub>E src : \<tau> \<Longrightarrow>
   map_type \<tau> \<sigma> \<upsilon> _ \<Longrightarrow>
   \<sigma> \<le> its_key_ty \<Longrightarrow>
   \<upsilon> \<le> its_val_ty \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its its_key_ty ++\<^sub>f coiterators its its_val_ty \<turnstile>\<^sub>E body : \<rho> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>I (src, its, (Some its_key_ty, Some its_val_ty), body) : (\<tau>, \<sigma>, \<rho>)"

|IterateT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, Let res (Some res_t) res_init body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> res_t \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E IterateCall src ArrowCall its its_ty res (Some res_t) res_init body : \<rho>"

|AnyIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E AnyIterationCall src ArrowCall its its_ty body : to_errorable \<sigma>"
|ClosureIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   (* По-моему тут ошибка, должен быть просто element_type?
      Согласно спецификации может быть либо простое значение, либо коллекция *)
   to_single_type \<rho> \<rho>' \<Longrightarrow>
   \<rho>' \<le> \<sigma> \<Longrightarrow>
   to_unique_collection_type \<tau> \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src ArrowCall its its_ty body : \<upsilon>"
|CollectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_nonunique_collection_type \<tau> \<upsilon> \<Longrightarrow>
   to_single_type \<rho> \<rho>' \<Longrightarrow>
   update_element_type \<upsilon> \<rho>' \<phi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectIterationCall src ArrowCall its its_ty body : \<phi>"
|CollectByIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   map_type' \<upsilon> \<sigma> \<rho> False \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src ArrowCall its its_ty body : \<upsilon>"
|CollectNestedIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_nonunique_collection_type \<tau> \<upsilon> \<Longrightarrow>
   update_element_type \<upsilon> \<rho> \<phi> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src ArrowCall its its_ty body : \<phi>"
|ExistsIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ExistsIterationCall src ArrowCall its its_ty body : \<rho>"
|ForAllIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E ForAllIterationCall src ArrowCall its its_ty body : \<rho>"
|OneIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E OneIterationCall src ArrowCall its its_ty body : Boolean[1]"
|IsUniqueIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E IsUniqueIterationCall src ArrowCall its its_ty body : Boolean[1]"
|SelectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E SelectIterationCall src ArrowCall its its_ty body : \<tau>"
|RejectIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E RejectIterationCall src ArrowCall its its_ty body : \<tau>"
|SortedByIterationT:
  "\<Gamma> \<turnstile>\<^sub>I (src, its, its_ty, body) : (\<tau>, \<sigma>, \<rho>) \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_ordered_collection_type \<tau> \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src ArrowCall its its_ty body : \<upsilon>"

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
inductive_cases CollectionLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau>"
inductive_cases MapLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E MapLiteral elems : \<tau>"
inductive_cases TupleLiteralTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleLiteral elems : \<tau>"

inductive_cases LetTE [elim]: "\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
inductive_cases VarTE [elim]: "\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
inductive_cases IfTE [elim]: "\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

inductive_cases MetaOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
inductive_cases StaticOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

inductive_cases TypeOperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
inductive_cases AttributeCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AttributeCall src k prop : \<tau>"
inductive_cases AssociationEndCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src k role from : \<tau>"
inductive_cases AssociationClassCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src k a from : \<tau>"
inductive_cases AssociationClassEndCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src k role : \<tau>"
inductive_cases OperationCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
inductive_cases TupleElementCallTE [elim]: "\<Gamma> \<turnstile>\<^sub>E TupleElementCall src k elem : \<tau>"

inductive_cases IterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
inductive_cases IterateTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IterateCall src k its its_ty res res_t res_init body : \<tau>"
inductive_cases AnyIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E AnyIterationCall src k its its_ty body : \<tau>"
inductive_cases ClosureIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src k its its_ty body : \<tau>"
inductive_cases CollectIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectIterationCall src k its its_ty body : \<tau>"
inductive_cases CollectByIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectByIterationCall src k its its_ty body : \<tau>"
inductive_cases CollectNestedIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src k its its_ty body : \<tau>"
inductive_cases ExistsIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ExistsIterationCall src k its its_ty body : \<tau>"
inductive_cases ForAllIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E ForAllIterationCall src k its its_ty body : \<tau>"
inductive_cases OneIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E OneIterationCall src k its its_ty body : \<tau>"
inductive_cases IsUniqueIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E IsUniqueIterationCall src k its its_ty body : \<tau>"
inductive_cases SelectIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E SelectIterationCall src k its its_ty body : \<tau>"
inductive_cases RejectIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E RejectIterationCall src k its its_ty body : \<tau>"
inductive_cases SortedByIterationTE [elim]: "\<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src k its its_ty body : \<tau>"

(*inductive_cases CollectionPartsTE [elim]: "\<Gamma> \<turnstile>\<^sub>C x : \<tau>"*)
(*
inductive_cases CollectionPartsNilTE [elim]: "\<Gamma> \<turnstile>\<^sub>C x : \<tau>"
inductive_cases CollectionPartsItemTE [elim]: "\<Gamma> \<turnstile>\<^sub>C x # xs : \<tau>"
*)
inductive_cases CollectionItemTE [elim]: "\<Gamma> \<turnstile>\<^sub>C CollectionItem a : \<tau>"
inductive_cases CollectionRangeTE [elim]: "\<Gamma> \<turnstile>\<^sub>C CollectionRange a b : \<tau>"

inductive_cases ExprListTE [elim]: "\<Gamma> \<turnstile>\<^sub>L exprs : \<pi>"

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
"\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E MapLiteral prts : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral (x # xs) : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

"\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AttributeCall src k prop : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src k role from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src k a from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src k role : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleElementCall src k elem : \<tau>"

"\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
"\<Gamma> \<turnstile>\<^sub>E IterateCall src k its its_ty res res_t res_init body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AnyIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ClosureIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectByIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectNestedIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ExistsIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ForAllIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OneIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IsUniqueIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SelectIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RejectIterationCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SortedByIterationCall src k its its_ty body : \<tau>"

(*"\<Gamma> \<turnstile>\<^sub>C [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>C x # xs : \<tau>"*)

"\<Gamma> \<turnstile>\<^sub>C CollectionItem a : \<tau>"
"\<Gamma> \<turnstile>\<^sub>C CollectionRange a b : \<tau>"

"\<Gamma> \<turnstile>\<^sub>L [] : \<pi>"
"\<Gamma> \<turnstile>\<^sub>L x # xs : \<pi>"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma collection_type\<^sub>T_det:
  "collection_type\<^sub>T \<tau> k\<^sub>1 \<sigma>\<^sub>N \<Longrightarrow>
   collection_type\<^sub>T \<tau> k\<^sub>2 \<rho>\<^sub>N \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>N = \<rho>\<^sub>N"
  "collection_type\<^sub>T \<tau>\<^sub>1 k \<sigma>\<^sub>N \<Longrightarrow>
   collection_type\<^sub>T \<tau>\<^sub>2 k \<sigma>\<^sub>N \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: collection_type\<^sub>T.simps)

lemma collection_type\<^sub>N_det:
  "collection_type\<^sub>N \<tau>\<^sub>N k\<^sub>1 \<sigma>\<^sub>N n\<^sub>1 \<Longrightarrow>
   collection_type\<^sub>N \<tau>\<^sub>N k\<^sub>2 \<rho>\<^sub>N n\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>N = \<rho>\<^sub>N \<and> n\<^sub>1 = n\<^sub>2"
  "collection_type\<^sub>N \<tau>\<^sub>N\<^sub>1 k \<sigma>\<^sub>N n \<Longrightarrow>
   collection_type\<^sub>N \<tau>\<^sub>N\<^sub>2 k \<sigma>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>N\<^sub>1 = \<tau>\<^sub>N\<^sub>2"
  by (auto simp add: collection_type\<^sub>N.simps collection_type\<^sub>T_det)

lemma collection_type_det:
  "collection_type \<tau> k\<^sub>1 \<sigma>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   collection_type \<tau> k\<^sub>2 \<sigma>\<^sub>2 n\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "collection_type \<tau>\<^sub>1 k \<sigma> n \<Longrightarrow>
   collection_type \<tau>\<^sub>2 k \<sigma> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (elim collection_type.cases; simp add: collection_type\<^sub>N_det)+


lemma map_type\<^sub>T_det:
  "map_type\<^sub>T \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 \<Longrightarrow>
   map_type\<^sub>T \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2"
  "map_type\<^sub>T \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N \<Longrightarrow>
   map_type\<^sub>T \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: map_type\<^sub>T.simps)

lemma map_type\<^sub>N_det:
  "map_type\<^sub>N \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 \<Longrightarrow>
   map_type\<^sub>N \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "map_type\<^sub>N \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow>
   map_type\<^sub>N \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: map_type\<^sub>N.simps map_type\<^sub>T_det)

lemma map_type_det:
  "map_type \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 \<Longrightarrow>
   map_type \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "map_type' \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow>
   map_type' \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim map_type.cases; simp add: map_type\<^sub>N_det(1))
  by (elim map_type'.cases; simp add: map_type\<^sub>N_det(2))


lemma tuple_type\<^sub>T_det:
  "tuple_type\<^sub>T \<tau> \<pi>\<^sub>1 \<Longrightarrow>
   tuple_type\<^sub>T \<tau> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2"
  "tuple_type\<^sub>T \<tau>\<^sub>1 \<pi> \<Longrightarrow>
   tuple_type\<^sub>T \<tau>\<^sub>2 \<pi> \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: tuple_type\<^sub>T.simps)

lemma tuple_type\<^sub>N_det:
  "tuple_type\<^sub>N \<tau> \<pi>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   tuple_type\<^sub>N \<tau> \<pi>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<and>  n\<^sub>1 =  n\<^sub>2"
  "tuple_type\<^sub>N \<tau>\<^sub>1 \<pi> n \<Longrightarrow>
   tuple_type\<^sub>N \<tau>\<^sub>2 \<pi> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: tuple_type\<^sub>N.simps tuple_type\<^sub>T_det)

lemma tuple_type_det:
  "tuple_type \<tau> \<pi>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   tuple_type \<tau> \<pi>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<and>  n\<^sub>1 =  n\<^sub>2"
  "tuple_type' \<tau>\<^sub>1 \<pi> n \<Longrightarrow>
   tuple_type' \<tau>\<^sub>2 \<pi> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim tuple_type.cases)
  using tuple_type\<^sub>N_det(1) apply blast+
  apply (elim tuple_type'.cases)
  using tuple_type\<^sub>N_det(2) by blast+


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
proof (induct arbitrary: \<sigma> and \<sigma> and \<sigma> and ys and \<xi>
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
  case (EnumLiteralT \<Gamma> \<tau> lit) thus ?case by auto
next
  case (CollectionLiteralNilT k \<sigma> \<Gamma>) thus ?case
    using collection_type_det(2) by blast
next
  case (CollectionLiteralConsT k \<Gamma> x \<tau> \<sigma> xs) thus ?case
    using collection_type_det(2) by blast
next
  case (CollectionPartItemT \<Gamma> a \<tau>) thus ?case by blast
next
  case (CollectionPartRangeT \<Gamma> a \<tau> b \<sigma>) thus ?case by blast
next
  case (MapNilT \<tau> \<Gamma>) thus ?case
    using map_type_det(2) by blast
next
  case (MapConsT \<Gamma> x \<tau> \<sigma> \<rho> xs \<upsilon>) show ?case
    apply (insert MapConsT.prems)
    apply (erule MapLiteralTE, simp)
    using MapConsT.hyps map_type_det(2) by fastforce
next
  case (TupleLiteralNilT \<Gamma>) thus ?case by auto
next
  case (TupleLiteralConsT \<Gamma> el \<tau> \<sigma> \<rho> elems \<upsilon>) show ?case
    apply (insert TupleLiteralConsT.prems)
    apply (erule TupleLiteralTE, simp)
    using TupleLiteralConsT.hyps tuple_type_det(2) by fastforce
next
  case (LetT \<Gamma> \<M> init \<sigma> \<tau> v body \<rho>) thus ?case by blast
next
  case (VarT \<Gamma> v \<tau> \<M>) thus ?case by auto
next
  case (IfT \<Gamma> a \<tau> b \<sigma> c \<rho>) thus ?case
    apply (insert IfT.prems)
    apply (erule IfTE)
    by (simp add: IfT.hyps)
next
  case (MetaOperationCallT \<tau> op \<sigma> \<Gamma>) thus ?case
    by (meson MetaOperationCallTE mataop_type_det)
next
  case (StaticOperationCallT \<tau> op \<pi> oper \<Gamma> as) thus ?case
    apply (insert StaticOperationCallT.prems)
    apply (erule StaticOperationCallTE)
(*    using StaticOperationCallT.hyps static_operation_det by blast*)
    sorry
next
  case (TypeOperationCallT \<Gamma> a \<tau> op \<sigma> \<rho>) thus ?case
    by (metis TypeOperationCallTE typeop_type_det)
next
  case (AttributeCallT \<Gamma> src \<tau> \<C> "prop" \<D> \<sigma>) show ?case
    apply (insert AttributeCallT.prems)
    apply (erule AttributeCallTE)
    using AttributeCallT.hyps attribute_det by blast
next
  case (AssociationEndCallT \<Gamma> src \<C> "from" role \<D> "end") show ?case
    apply (insert AssociationEndCallT.prems)
    apply (erule AssociationEndCallTE)
    using AssociationEndCallT.hyps association_end_det by blast
next
  case (AssociationClassCallT \<Gamma> src \<C> "from" \<A>) thus ?case by blast
next
  case (AssociationClassEndCallT \<Gamma> src \<tau> \<A> role "end") show ?case
    apply (insert AssociationClassEndCallT.prems)
    apply (erule AssociationClassEndCallTE)
    using AssociationClassEndCallT.hyps association_class_end_det by blast
next
  case (OperationCallT \<Gamma> src \<tau> params \<pi> op k) show ?case
    apply (insert OperationCallT.prems)
    apply (erule OperationCallTE)
(*    using OperationCallT.hyps op_type_det by blast*)
    sorry
next
  case (TupleElementCallT \<Gamma> src \<pi> elem \<tau>) thus ?case 
    apply (insert TupleElementCallT.prems)
    apply (erule TupleElementCallTE)
    using TupleElementCallT.hyps tuple_type_det(1) by fastforce
next
  case (CollectionIterationT \<Gamma> src \<tau> k \<sigma> n its_ty its body \<rho>) show ?case
    apply (insert CollectionIterationT.prems)
    apply (erule IterationTE)
    using CollectionIterationT.hyps OCL_Typing.collection_type_det(1) apply blast
    by simp
next
  case (MapIterationT \<Gamma> src \<tau> \<sigma> \<upsilon> uu its_key_ty its_val_ty its body \<rho>) show ?case
    apply (insert MapIterationT.prems)
    apply (erule IterationTE)
    apply simp
    using MapIterationT.hyps map_type_det(1) by fastforce
next
  case (IterateT \<Gamma> src its its_ty res res_t res_init body \<tau> \<sigma> \<rho>) show ?case
    apply (insert IterateT.prems)
(*    using IterateT.hyps by blast*)
    sorry
next
  case (AnyIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) thus ?case
(*    by (meson AnyIterationTE Pair_inject)*)
    sorry
next
  case (ClosureIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert ClosureIterationT.prems)
    apply (erule ClosureIterationTE)
    apply (erule IterationTE)
(*    using ClosureIterationT.hyps to_unique_collection_type_det by blast*)
    sorry
next
  case (CollectIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert CollectIterationT.prems)
    apply (erule CollectIterationTE)
    apply (erule IterationTE)
(*    using CollectIterationT.hyps to_nonunique_collection_type_det
      update_element_type_det Pair_inject to_single_type_det by metis*)
    sorry
next
  case (CollectByIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>)
    then show ?case sorry
next
  case (CollectNestedIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert CollectNestedIterationT.prems)
    apply (erule CollectNestedIterationTE)
(*    using CollectNestedIterationT.hyps to_nonunique_collection_type_det
      update_element_type_det Pair_inject by metis*)
    sorry
next
  case (ExistsIterationT \<Gamma> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert ExistsIterationT.prems)
    apply (erule ExistsIterationTE)
(*    using ExistsIterationT.hyps Pair_inject by metis*)
    sorry
next
  case (ForAllIterationT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert ForAllIterationT.prems)
    apply (erule ForAllIterationTE)
(*    using ForAllIterationT.hyps Pair_inject by metis*)
    sorry
next
  case (OneIterationT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert OneIterationT.prems)
    apply (erule OneIterationTE)
    by simp
next
  case (IsUniqueIterationT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert IsUniqueIterationT.prems)
    apply (erule IsUniqueIterationTE)
    by simp
next
  case (SelectIterationT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert SelectIterationT.prems)
    apply (erule SelectIterationTE)
(*    using SelectIterationT.hyps by blast*)
    sorry
next
  case (RejectIterationT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho>) show ?case
    apply (insert RejectIterationT.prems)
    apply (erule RejectIterationTE)
(*    using RejectIterationT.hyps by blast*)
    sorry
next
  case (SortedByIterationT \<Gamma> \<M> src its its_ty body \<tau> \<sigma> \<rho> \<upsilon>) show ?case
    apply (insert SortedByIterationT.prems)
    apply (erule SortedByIterationTE)
(*    using SortedByIterationT.hyps to_ordered_collection_type_det by blast*)
    sorry
next
  case (ExprListNilT \<Gamma>) thus ?case
    using expr_list_typing.cases by auto
next
  case (ExprListConsT \<Gamma> expr \<tau> exprs \<pi>) show ?case
    apply (insert ExprListConsT.prems)
    apply (erule ExprListTE)
    apply simp
    by (simp_all add: ExprListConsT.hyps)
qed

lemma CollectionLiteral_has_Collection_type:
  "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral SetKind prts : \<tau> \<Longrightarrow> \<exists>\<sigma>. \<tau> = (Set \<sigma>)[1]"
  "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral OrderedSetKind prts : \<tau> \<Longrightarrow> \<exists>\<sigma>. \<tau> = (OrderedSet \<sigma>)[1]"
  "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral BagKind prts : \<tau> \<Longrightarrow> \<exists>\<sigma>. \<tau> = (Bag \<sigma>)[1]"
  "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral SequenceKind prts : \<tau> \<Longrightarrow> \<exists>\<sigma>. \<tau> = (Sequence \<sigma>)[1]"
  by auto
(*
lemma q11:
  "       (\<And>\<tau>. \<Gamma> \<turnstile>\<^sub>E Literal (MapLiteral xs) : \<tau> \<Longrightarrow>
             \<exists>\<sigma> \<rho>. \<tau> = (Map \<sigma> \<rho>)[1]) \<Longrightarrow>
       \<tau> =
       (case \<rho> of
        ErrorFree \<rho> \<Rightarrow> ErrorFree ((Map \<tau>' \<sigma>)[1]\<^sub>N \<squnion> \<rho>)
        | Errorable \<rho> \<Rightarrow>
            Errorable ((Map \<tau>' \<sigma>)[1]\<^sub>N \<squnion> \<rho>)) \<Longrightarrow>
       \<Gamma> \<turnstile>\<^sub>E Literal (MapLiteral xs) : \<rho> \<Longrightarrow>
       \<exists>\<sigma> \<rho>. \<tau> = (Map \<sigma> \<rho>)[1]"
  apply auto

lemma MapLiteral_has_Map_type:
  "\<Gamma> \<turnstile>\<^sub>E MapLiteral prts : \<tau> \<Longrightarrow> \<exists>\<sigma> \<rho>. \<tau> = (Map \<sigma> \<rho>)[1]"
  apply (induct prts arbitrary: \<tau>)
  apply auto[1]
  apply (erule MapLiteralTE)
  apply auto[1]

  thm MapLiteralTE
  thm TupleLiteralTE


lemma type\<^sub>N_less_right_simps [simp]:
  "\<tau> < Required \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> < \<upsilon>)"
  "\<tau> < Optional \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Optional \<rho> \<and> \<rho> < \<upsilon>)"
  by auto

lemma type\<^sub>N_less_eq_right_simps [simp]:
  "\<tau> \<le> Required \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> \<le> \<upsilon>)"
  "\<tau> \<le> Optional \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Optional \<rho> \<and> \<rho> \<le> \<upsilon>)"
  by auto
*)
(*
lemma q11:
  "ErrorFree \<rho> \<le> (Map OclAny[?]\<^sub>N OclAny[?]\<^sub>N)[1] \<Longrightarrow>
   \<tau> = ErrorFree ((Map \<tau>' \<sigma>)[1]\<^sub>N \<squnion> \<rho>) \<Longrightarrow>
   \<tau> \<le> (Map OclAny[?]\<^sub>N OclAny[?]\<^sub>N)[1]"
  by (smt less_eq_errorable_type.simps(1) sup.boundedI sup.orderI sup_ge1
          type.inject(8) type\<^sub>N_less_eq_left_simps(2) type\<^sub>N_less_eq_right_simps(1)
          type_less_eq_left_simps(1) type_less_eq_x_Map_intro)

lemma q12:
  "       (\<And>\<tau>. \<Gamma> \<turnstile>\<^sub>E Literal (MapLiteral xs) : \<tau> \<Longrightarrow>
             \<tau> \<le> (Map OclAny[?]\<^sub>N OclAny[?]\<^sub>N)[1]) \<Longrightarrow>
       \<tau> =
       (case \<rho> of
        ErrorFree \<rho> \<Rightarrow> ErrorFree ((Map \<tau>' \<sigma>)[1]\<^sub>N \<squnion> \<rho>)
        | Errorable \<rho> \<Rightarrow>
            Errorable ((Map \<tau>' \<sigma>)[1]\<^sub>N \<squnion> \<rho>)) \<Longrightarrow>
       \<Gamma> \<turnstile>\<^sub>E map_literal_element_key x : ErrorFree \<tau>' \<Longrightarrow>
       \<Gamma> \<turnstile>\<^sub>E map_literal_element_value x : ErrorFree \<sigma> \<Longrightarrow>
       \<Gamma> \<turnstile>\<^sub>E Literal (MapLiteral xs) : \<rho> \<Longrightarrow>
       \<tau> \<le> (Map OclAny[?]\<^sub>N OclAny[?]\<^sub>N)[1]"
  by (metis (no_types, lifting) OCL_Typing.q11 errorable_type.simps(5)
        type\<^sub>N\<^sub>E_less_eq_right_simps(1))

lemma q13:
  "a # prts = x # xs \<Longrightarrow> prts = xs"
  by auto

lemma MapLiteral_has_Map_type:
  "\<Gamma> \<turnstile>\<^sub>E MapLiteral prts : \<tau> \<Longrightarrow> \<tau> \<le> (Map OclAny[?]\<^sub>N OclAny[?]\<^sub>N)[1]"
  apply (induct prts arbitrary: \<tau>)
  apply auto[1]
  apply (erule MapLiteralTE)
  apply auto[1]
*)

lemma TupleLiteral_has_Tuple_type:
  "\<Gamma> \<turnstile>\<^sub>E TupleLiteral prts : \<tau> \<Longrightarrow> \<exists>\<pi>. \<tau> = (Tuple \<pi>)[1]"
  by auto



















(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred [show_modes] op_type .
code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] iterator_typing .

end

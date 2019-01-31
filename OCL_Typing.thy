(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Typing Rules\<close>
theory OCL_Typing
  imports OCL_Object_Model
begin

text \<open>
  The following rules are more restrictive than rules given in
  the OCL specification. This allows one to identify more errors
  in expressions. However, these restrictions may be revised if necessary.
  Perhaps some of them could be separated and should cause warnings
  instead of errors.\<close>

(*** Operations Typing ******************************************************)

section \<open>Operations\<close>

subsection \<open>Metaclass Operations\<close>

text \<open>
  All primitive types in the theory are either nullable or non-nullable.
  For example, instead of @{text Boolean} type we have two types:
  @{text "Boolean[1]"} and @{text "Boolean[?]"}.
  The @{text "allInstances()"} operation is extended accordingly:
  \<^verbatim>\<open>Boolean[1].allInstances() = Set{true, false}
Boolean[?].allInstances() = Set{true, false, null}\<close>\<close>

inductive mataop_type where
  "mataop_type \<tau> AllInstancesOp (Set \<tau>)"

subsection \<open>Type Operations\<close>

text \<open>
  At first we decided to allow casting only to subtypes.
  However sometimes it's necessary to cast expressions to supertypes,
  for example, to access overridden attributes of a supertype.
  So we prohibit casting to types not related to a current type by a subtype relation.\<close>

text \<open>
  According to the section 7.4.7 of the OCL specification
  @{text "oclAsType()"} can be applied to collections as well as
  to single values. I guess we can allow @{text "oclIsTypeOf()"}
  and @{text "oclIsKindOf()"} for collections too.\<close>

text \<open>
  Please take a note that:
  \<^verbatim>\<open>Set{1,2,null,'abc'}->selectByKind(Integer[1]) = Set{1,2}
Set{1,2,null,'abc'}->selectByKind(Integer[?]) = Set{1,2,null}\<close>
  And the following expressions are prohibited, because they always
  returns either the same or empty collections:
  \<^verbatim>\<open>Set{1,2,null,'abc'}->selectByKind(OclAny[?])
Set{1,2,null,'abc'}->selectByKind(Collection(Boolean[1]))\<close>\<close>

inductive typeop_type where
  "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow>
   typeop_type DotCall OclAsTypeOp \<tau> \<sigma> \<sigma>"
| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsTypeOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type DotCall OclIsKindOfOp \<tau> \<sigma> Boolean[1]"
| "strict_subcollection \<tau> \<sigma> \<rho> \<Longrightarrow>
   typeop_type ArrowCall SelectByKindOp \<tau> \<sigma> \<rho>"
| "strict_subcollection \<tau> \<sigma> \<rho> \<Longrightarrow>
   typeop_type ArrowCall SelectByTypeOp \<tau> \<sigma> \<rho>"

text \<open>
  It makes sense to compare values only with compatible types.\<close>

subsection \<open>SupType Operations\<close>

(* We have to specify predicate type explicitly to let
   a generated code work *)
inductive suptype_binop_type
  :: "suptype_binop \<Rightarrow> ('a :: order) type \<Rightarrow> 'a type \<Rightarrow> 'a type \<Rightarrow> bool" where
  "\<tau> \<le> \<sigma> \<Longrightarrow>
   suptype_binop_type EqualOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   suptype_binop_type EqualOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<le> \<sigma> \<Longrightarrow>
   suptype_binop_type NotEqualOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   suptype_binop_type NotEqualOp \<tau> \<sigma> Boolean[1]"

subsection \<open>OclAny Operations\<close>

text \<open>
  The OCL specification defines @{text "toString()"} operation
  only for boolean and numeric types. However, I guess it's a good
  idea to define it once for all basic types.\<close>

inductive any_unop_type where
  "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclAsSetOp \<tau> (Set \<tau>)"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsNewOp \<tau> Boolean[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsUndefinedOp \<tau> Boolean[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsInvalidOp \<tau> Boolean[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclLocaleOp \<tau> String[1]"
| "\<tau> \<le> OclAny[?] \<Longrightarrow>
   any_unop_type ToStringOp \<tau> String[1]"

subsection \<open>Boolean Operations\<close>

inductive boolean_unop_type where
  "\<tau> \<le> Boolean[?] \<Longrightarrow>
   boolean_unop_type NotOp \<tau> \<tau>"

inductive boolean_binop_type where
  "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type AndOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type OrOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type XorOp \<tau> \<sigma> \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   boolean_binop_type ImpliesOp \<tau> \<sigma> \<rho>"

subsection \<open>Numeric Operations\<close>

text \<open>
  Formally null conforms to numeric types. However expressions
  like @{text "null + null"} makes no sense. So we use
  @{text "UnlimitedNatural[1]"} as a lower bound.\<close>

text \<open>
  Please take a note that many operations automatically casts
  unlimited naturals to integers.\<close>

text \<open>
  The difference between @{text "oclAsType(Integer)"} and
  @{text "toInteger()"} for unlimited naturals is unclear.\<close>

inductive numeric_unop_type where
  "\<tau> \<simeq> Real \<Longrightarrow>
   numeric_unop_type UMinusOp \<tau> Real[1]"
| "\<tau> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   numeric_unop_type UMinusOp \<tau> Integer[1]"

| "\<tau> \<simeq> Real \<Longrightarrow>
   numeric_unop_type AbsOp \<tau> Real[1]"
| "\<tau> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   numeric_unop_type AbsOp \<tau> Integer[1]"

| "\<tau> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_unop_type FloorOp \<tau> Integer[1]"
| "\<tau> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_unop_type RoundOp \<tau> Integer[1]"

| "\<tau> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_unop_type numeric_unop.ToIntegerOp \<tau> Integer[1]"

inductive numeric_binop_type where
  "\<tau> \<squnion> \<sigma> \<simeq> Real \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> Integer \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_binop_type PlusOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> Real \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   numeric_binop_type MinusOp \<tau> \<sigma> Integer[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> Real \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> Integer \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_binop_type MultOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_binop_type DivideOp \<tau> \<sigma> Real[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> Integer \<Longrightarrow>
   numeric_binop_type DivOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_binop_type DivOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> Integer \<Longrightarrow>
   numeric_binop_type ModOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_binop_type ModOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> Real \<Longrightarrow>
   numeric_binop_type MaxOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> Integer \<Longrightarrow>
   numeric_binop_type MaxOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_binop_type MaxOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> Real \<Longrightarrow>
   numeric_binop_type MinOp \<tau> \<sigma> Real[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> Integer \<Longrightarrow>
   numeric_binop_type MinOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural \<Longrightarrow>
   numeric_binop_type MinOp \<tau> \<sigma> UnlimitedNatural[1]"

| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_binop_type numeric_binop.LessOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_binop_type numeric_binop.LessEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterEqOp \<tau> \<sigma> Boolean[1]"

subsection \<open>String Operations\<close>

inductive string_unop_type where
  "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type SizeOp \<tau> Integer[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type CharactersOp \<tau> (Sequence String[1])"
| "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type ToUpperCaseOp \<tau> String[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type ToLowerCaseOp \<tau> String[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type ToBooleanOp \<tau> Boolean[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type ToIntegerOp \<tau> Integer[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   string_unop_type ToRealOp \<tau> Real[1]"

inductive string_binop_type where
  "\<tau> \<squnion> \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type ConcatOp \<tau> \<sigma> String[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type EqualsIgnoreCaseOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type LessOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type LessEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type GreaterOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<squnion> \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type GreaterEqOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   \<sigma> \<simeq> String \<Longrightarrow>
   string_binop_type IndexOfOp \<tau> \<sigma> Integer[1]"
| "\<tau> \<simeq> String \<Longrightarrow>
   \<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   string_binop_type AtOp \<tau> \<sigma> String[1]"

inductive string_ternop_type where
  "\<tau> \<simeq> String \<Longrightarrow>
   \<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   \<rho> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   string_ternop_type SubstringOp \<tau> \<sigma> \<rho> String[1]"

subsection \<open>Collection Operations\<close>

text \<open>
  Please take a note, that @{text "flatten()"} preserves a collection kind.\<close>

inductive collection_unop_type where
  "element_type \<tau> _ \<Longrightarrow>
   collection_unop_type CollectionSizeOp \<tau> Integer[1]"
| "element_type \<tau> _ \<Longrightarrow>
   collection_unop_type IsEmptyOp \<tau> Boolean[1]"
| "element_type \<tau> _ \<Longrightarrow>
   collection_unop_type NotEmptyOp \<tau> Boolean[1]"

| "element_type \<tau> \<sigma> \<Longrightarrow>
   \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> (to_required_type \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> (to_required_type \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real \<Longrightarrow>
   collection_unop_type SumOp \<tau> (to_required_type \<sigma>)"

| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsSetOp \<tau> (Set \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsOrderedSetOp \<tau> (OrderedSet \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsBagOp \<tau> (Bag \<sigma>)"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   collection_unop_type AsSequenceOp \<tau> (Sequence \<sigma>)"

| "element_type \<tau> \<sigma> \<Longrightarrow>
   update_element_type \<tau> (to_single_type \<sigma>) \<rho> \<Longrightarrow>
   collection_unop_type FlattenOp \<tau> \<rho>"

| "collection_unop_type FirstOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type FirstOp (Sequence \<tau>) \<tau>"
| "collection_unop_type LastOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type LastOp (Sequence \<tau>) \<tau>"
| "collection_unop_type ReverseOp (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "collection_unop_type ReverseOp (Sequence \<tau>) (Sequence \<tau>)"

text \<open>
  Please take a note that if both arguments are collections,
  then an element type of the resulting collection is a super type
  of element types of orginal collections. However for single-valued
  operations (@{text "including()"}, @{text "insertAt()"}, ...)
  this behavior looks undesirable. So we restrict such arguments
  to have a subtype of the collection element type.\<close>

text \<open>
  It's unclear what is the result of the @{text "indexOf()"}
  operation if the item not found: @{text "null"} or @{text "invalid"}?\<close>

(* including и excluding почему-то не определены для OrderedSet, хотя
 определены для остальных коллекций включая Sequence. А у меня для Sequence
 не определено! Нужно внимательно проверить все операции!
 excluding используется в определении selectByKind, который определен для
 Collection. По идее excluding должно быть определено и для Collection?
*)

(*
 Правило для excluding(null) нужно подробно описать.
 Это выглядит как хак, но реально это очень простой способ определить
 правила для безопасной навигации

 Подумать про excludingNested
*)

fun to_required_type' where
  "to_required_type' OclInvalid = OclInvalid"
| "to_required_type' OclVoid = OclInvalid"
| "to_required_type' \<tau>[1] = \<tau>[1]"
| "to_required_type' \<tau>[?] = \<tau>[1]"
| "to_required_type' \<tau> = \<tau>"


inductive collection_binop_type where
  "element_type \<tau> \<rho> \<Longrightarrow>
   \<sigma> \<le> to_optional_type \<rho> \<Longrightarrow>
   collection_binop_type IncludesOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow>
   \<sigma> \<le> to_optional_type \<rho> \<Longrightarrow>
   collection_binop_type ExcludesOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow>
   \<sigma> \<le> to_optional_type \<rho> \<Longrightarrow>
   collection_binop_type CountOp \<tau> \<sigma> Integer[1]"
| "element_type \<tau> \<rho> \<Longrightarrow>
   element_type \<sigma> \<upsilon> \<Longrightarrow>
   \<upsilon> \<le> to_optional_type \<rho> \<Longrightarrow>
   collection_binop_type IncludesAllOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow>
   element_type \<sigma> \<upsilon> \<Longrightarrow>
   \<upsilon> \<le> to_optional_type \<rho> \<Longrightarrow>
   collection_binop_type ExcludesAllOp \<tau> \<sigma> Boolean[1]"
| "element_type \<tau> \<rho> \<Longrightarrow>
   element_type \<sigma> \<upsilon> \<Longrightarrow>
   collection_binop_type ProductOp \<tau> \<sigma> (Tuple (fmap_of_list [(STR ''first'', \<rho>), (STR ''second'', \<upsilon>)]))"
| "collection_binop_type UnionOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Set \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Bag \<tau>) (Set \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Bag \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Set \<tau>) (Bag \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Bag \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Bag \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type IncludingOp (Set \<tau>) \<sigma> (Set \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type IncludingOp (Bag \<tau>) \<sigma> (Bag \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   \<sigma> \<noteq> OclVoid \<Longrightarrow>
   collection_binop_type ExcludingOp (Set \<tau>) \<sigma> (Set \<tau>)"
| "collection_binop_type ExcludingOp (Set \<tau>) OclVoid (Set (to_required_type' \<tau>))"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type ExcludingOp (Bag \<tau>) \<sigma> (Bag \<tau>)"
| "collection_binop_type SetMinusOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type SymmetricDifferenceOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type AppendOp (OrderedSet \<tau>) \<sigma> (OrderedSet \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type AppendOp (Sequence \<tau>) \<sigma> (Sequence \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type PrependOp (OrderedSet \<tau>) \<sigma> (OrderedSet \<tau>)"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type PrependOp (Sequence \<tau>) \<sigma> (Sequence \<tau>)"
| "\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   collection_binop_type CollectionAtOp (OrderedSet \<tau>) \<sigma> \<tau>"
| "\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   collection_binop_type CollectionAtOp (Sequence \<tau>) \<sigma> \<tau>"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (OrderedSet \<tau>) \<sigma> Integer[1]"
| "\<sigma> \<le> \<tau> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (Sequence \<tau>) \<sigma> Integer[1]"


inductive collection_ternop_type where
  "\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   \<rho> \<le> \<tau> \<Longrightarrow>
   collection_ternop_type InsertAtOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   \<rho> \<le> \<tau> \<Longrightarrow>
   collection_ternop_type InsertAtOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"
| "\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   \<rho> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   collection_ternop_type SubOrderedSetOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   \<rho> \<simeq> UnlimitedNatural\<midarrow>Integer \<Longrightarrow>
   collection_ternop_type SubSequenceOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"

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
  "suptype_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
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

inductive op_type where
  "unop_type op k \<tau> \<upsilon> \<Longrightarrow>
   op_type (Inl op) k \<tau> [] \<upsilon>"
| "binop_type op k \<tau> \<sigma> \<upsilon> \<Longrightarrow>
   op_type (Inr (Inl op)) k \<tau> [\<sigma>] \<upsilon>"
| "ternop_type op k \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   op_type (Inr (Inr (Inl op))) k \<tau> [\<sigma>, \<rho>] \<upsilon>"
| "find_operation \<tau> op \<pi> = Some oper \<Longrightarrow>
   op_type (Inr (Inr (Inr op))) DotCall \<tau> \<pi> (oper_type oper)"

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma typeop_type_det:
  "typeop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   typeop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: typeop_type.induct;
      auto simp add: typeop_type.simps strict_subcollection_det)

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
  apply (induct rule: collection_unop_type.induct)
  apply (erule collection_unop_type.cases;
         auto simp add: element_type_det update_element_type_det)+
  using element_type_det update_element_type_det apply blast+
  apply (erule collection_unop_type.cases; auto)
  using element_type_det update_element_type_det apply blast+
  apply (erule collection_unop_type.cases; auto)
  using element_type_det update_element_type_det apply blast+
  apply (erule collection_unop_type.cases; auto simp add: element_type_det)+
  using element_type_det update_element_type_det apply blast
  apply (erule collection_unop_type.cases; auto)+
  done

lemma unop_type_det:
  "unop_type op k \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   unop_type op k \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: unop_type.induct;
      simp add: unop_type.simps any_unop_type_det
                boolean_unop_type_det numeric_unop_type_det
                string_unop_type_det collection_unop_type_det)

lemma suptype_binop_type_det:
  "suptype_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   suptype_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: suptype_binop_type.induct; auto simp add: suptype_binop_type.simps)

lemma boolean_binop_type_det:
  "boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: boolean_binop_type.induct; simp add: boolean_binop_type.simps)

lemma numeric_binop_type_det:
  "numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (induct rule: numeric_binop_type.induct; auto simp add: numeric_binop_type.simps)
  by (metis basic_type.distinct(3) basic_type.distinct(27) basic_type.distinct(29))+

lemma string_binop_type_det:
  "string_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   string_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: string_binop_type.induct; simp add: string_binop_type.simps)

lemma collection_binop_type_det:
  "collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (induct rule: collection_binop_type.induct; simp add: collection_binop_type.simps)
  using element_type_det by blast

lemma binop_type_det:
  "binop_type op k \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   binop_type op k \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: binop_type.induct;
      simp add: binop_type.simps suptype_binop_type_det
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
  "op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow> op_type op k \<tau> \<pi> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (induct rule: op_type.induct)
  apply (erule op_type.cases; simp add: unop_type_det)
  apply (erule op_type.cases; simp add: binop_type_det)
  apply (erule op_type.cases; simp add: ternop_type_det)
  apply (erule op_type.cases; simp)
  done

(*** Expressions Typing *****************************************************)

section \<open>Expressions Typing\<close>

inductive typing
    :: "('a :: ocl_object_model) type env \<Rightarrow> 'a expr \<Rightarrow> 'a type \<Rightarrow> bool"
       ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
    and collection_parts_typing
    and iterator_typing
    and expr_list_typing where

\<comment> \<open>Primitive Literals\<close>
 NullLiteralT:
  "\<Gamma> \<turnstile> NullLiteral : OclVoid"
|InvalidLiteralT:
  "\<Gamma> \<turnstile> InvalidLiteral : OclInvalid"
|BooleanLiteralT:
  "\<Gamma> \<turnstile> BooleanLiteral c : Boolean[1]"
|RealLiteralT:
  "\<Gamma> \<turnstile> RealLiteral c : Real[1]"
|IntegerLiteralT:
  "\<Gamma> \<turnstile> IntegerLiteral c : Integer[1]"
|UnlimNatLiteralT:
  "\<Gamma> \<turnstile> UnlimitedNaturalLiteral c : UnlimitedNatural[1]"
|StringLiteralT:
  "\<Gamma> \<turnstile> StringLiteral c : String[1]"
|EnumLiteralT:
  "has_literal enum lit \<Longrightarrow>
   \<Gamma> \<turnstile> EnumLiteral enum lit : (Enum enum)[1]"

\<comment> \<open>Collection Literals\<close>
|SetLiteralT:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral SetKind prts : Set \<tau>"
|OrderedSetLiteralT:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral OrderedSetKind prts : OrderedSet \<tau>"
|BagLiteralT:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral BagKind prts : Bag \<tau>"
|SequenceLiteralT:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral SequenceKind prts : Sequence \<tau>"
|CollectionLiteralT:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral CollectionKind prts : Collection \<tau>"

|CollectionPartsNilT:
  "collection_parts_typing \<Gamma> [] OclInvalid"
|CollectionPartsItemT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; collection_parts_typing \<Gamma> xs \<sigma>\<rbrakk> \<Longrightarrow>
   collection_parts_typing \<Gamma> (CollectionItem a # xs) (\<tau> \<squnion> \<sigma>)"
|CollectionPartsRangeT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; \<tau> \<simeq> UnlimitedNatural\<midarrow>Integer;
    \<Gamma> \<turnstile> b : \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer;
    collection_parts_typing \<Gamma> xs \<rho>\<rbrakk> \<Longrightarrow>
   collection_parts_typing \<Gamma> (CollectionRange a b # xs) (Integer[1] \<squnion> \<rho>)"

\<comment> \<open>Tuple Literals\<close>
|EmptyTupleLiteralT:
  "\<Gamma> \<turnstile> TupleLiteral [] : Tuple fmempty"
|TupleLiteralT:
  "\<lbrakk>\<Gamma> \<turnstile> TupleLiteral elems : Tuple \<xi>; \<Gamma> \<turnstile> tuple_element_expr el : \<tau>; \<tau> \<le> tuple_element_type el\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> TupleLiteral (el # elems) : Tuple (fmupd (tuple_element_name el) (tuple_element_type el) \<xi>)"

\<comment> \<open>Misc Expressions\<close>
|LetT:
  "\<lbrakk>\<Gamma> \<turnstile> init : \<sigma>; \<sigma> \<le> \<tau>; fmupd v \<tau> \<Gamma> \<turnstile> body : \<rho>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> Let v \<tau> init body : \<rho>"
|VarT:
  "fmlookup \<Gamma> v = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> Var v : \<tau>"
|IfT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; \<tau> \<le> Boolean[?]; \<Gamma> \<turnstile> b : \<sigma>; \<Gamma> \<turnstile> c : \<rho>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> If a b c : \<sigma> \<squnion> \<rho>"

\<comment> \<open>Call Expressions\<close>
|MetaOperationCallT:
  "mataop_type \<tau> op \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> MetaOperationCall \<tau> op : \<sigma>"
|StaticOperationCallT:
  "expr_list_typing \<Gamma> params \<pi> \<Longrightarrow>
   find_static_operation \<tau> op \<pi> = Some oper \<Longrightarrow>
   \<Gamma> \<turnstile> StaticOperationCall \<tau> op params : oper_type oper"

|TypeOperationCallT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; typeop_type k op \<tau> \<sigma> \<rho>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> TypeOperationCall a k op \<sigma> : \<rho>"

|IteratorT:
  "\<Gamma> \<turnstile> src : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile> body : \<rho> \<Longrightarrow>
   iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho>"

|IterateT:
  "\<lbrakk>iterator_typing \<Gamma> src its (Let res res_t res_init body) \<tau> \<sigma> \<rho>; \<rho> \<le> res_t\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> IterateCall src its res res_t res_init body : \<rho>"

|AnyIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> AnyIteratorCall src its body : \<sigma>"
|ClosureIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_single_type \<rho> \<le> \<sigma> \<Longrightarrow>
   to_unique_collection \<tau> \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile> ClosureIteratorCall src its body : \<upsilon>"
|CollectIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<upsilon> \<Longrightarrow>
   update_element_type \<upsilon> (to_single_type \<rho>) \<phi> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectIteratorCall src its body : \<phi>"
|CollectNestedIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<upsilon> \<Longrightarrow>
   update_element_type \<upsilon> \<rho> \<phi> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectNestedIteratorCall src its body : \<phi>"
|ExistsIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> ExistsIteratorCall src its body : \<rho>"
|ForAllIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> ForAllIteratorCall src its body : \<rho>"
|OneIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> OneIteratorCall src its body : Boolean[1]"
|IsUniqueIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<Gamma> \<turnstile> IsUniqueIteratorCall src its body : Boolean[1]"
|SelectIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> SelectIteratorCall src its body : \<tau>"
|RejectIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> RejectIteratorCall src its body : \<tau>"
|SortedByIteratorT:
  "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_ordered_collection \<tau> \<upsilon> \<Longrightarrow>
   \<Gamma> \<turnstile> SortedByIteratorCall src its body : \<upsilon>"

|AttributeCallT:
  "\<Gamma> \<turnstile> src : \<tau> \<Longrightarrow>
   class_of \<tau> cls \<Longrightarrow>
   find_attribute cls prop = Some (cls2, \<sigma>) \<Longrightarrow>
   \<Gamma> \<turnstile> AttributeCall src prop : \<sigma>"
|AssociationEndCallT:
  "\<Gamma> \<turnstile> src : \<tau> \<Longrightarrow>
   class_of \<tau> cls \<Longrightarrow>
   find_association_end cls role = Some end \<Longrightarrow>
   \<Gamma> \<turnstile> AssociationEndCall src role : assoc_end_type end"
|OperationCallT:
  "\<Gamma> \<turnstile> src : \<tau> \<Longrightarrow>
   expr_list_typing \<Gamma> params \<pi> \<Longrightarrow>
   op_type op k \<tau> \<pi> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> OperationCall src k op params : \<sigma>"

|TupleElementCallT:
  "\<Gamma> \<turnstile> src : Tuple \<pi> \<Longrightarrow>
   fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> TupleElementCall src elem : \<tau>"

|ExprListNilT:
  "expr_list_typing \<Gamma> [] []"
|ExprListConsT:
  "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow>
   expr_list_typing \<Gamma> exprs \<pi> \<Longrightarrow>
   expr_list_typing \<Gamma> (expr # exprs) (\<tau> # \<pi>)"

inductive_cases NullLiteral_typing [elim]: "\<Gamma> \<turnstile> NullLiteral : \<tau>"
inductive_cases InvalidLiteral_typing [elim]: "\<Gamma> \<turnstile> InvalidLiteral : \<tau>"
inductive_cases BooleanLiteral_typing [elim]: "\<Gamma> \<turnstile> BooleanLiteral c : \<tau>"
inductive_cases RealLiteral_typing [elim]: "\<Gamma> \<turnstile> RealLiteral c : \<tau>"
inductive_cases IntegerLiteral_typing [elim]: "\<Gamma> \<turnstile> IntegerLiteral c : \<tau>"
inductive_cases UnlimitedNaturalLiteral_typing [elim]: "\<Gamma> \<turnstile> UnlimitedNaturalLiteral c : \<tau>"
inductive_cases StringLiteral_typing [elim]: "\<Gamma> \<turnstile> StringLiteral c : \<tau>"
inductive_cases EnumLiteral_typing [elim]: "\<Gamma> \<turnstile> EnumLiteral enm lit : \<tau>"
inductive_cases CollectionLiteral_typing [elim]: "\<Gamma> \<turnstile> CollectionLiteral k prts : \<tau>"
inductive_cases collection_parts_typing [elim]: "collection_parts_typing \<Gamma> prts \<tau>"
inductive_cases collection_parts_item_typing [elim]: "collection_parts_typing \<Gamma> (CollectionItem x # xs) \<tau>"
inductive_cases collection_parts_range_typing [elim]: "collection_parts_typing \<Gamma> (CollectionRange x y # xs) \<tau>"
inductive_cases TupleLiteral_typing [elim]: "\<Gamma> \<turnstile> TupleLiteral elems : \<tau>"
inductive_cases Let_typing [elim]: "\<Gamma> \<turnstile> Let v \<tau> init body : \<sigma>"
inductive_cases Var_typing [elim]: "\<Gamma> \<turnstile> Var v : \<tau>"
inductive_cases If_typing [elim]: "\<Gamma> \<turnstile> If a b c : \<tau>"
inductive_cases Call_typing [elim]: "\<Gamma> \<turnstile> Call a k c : \<tau>"
inductive_cases MetaOperationCall_typing [elim]: "\<Gamma> \<turnstile> MetaOperationCall \<tau> op : \<sigma>"
inductive_cases StaticOperationCall_typing [elim]: "\<Gamma> \<turnstile> StaticOperationCall \<tau> op as : \<sigma>"
inductive_cases TypeOperationCall_typing [elim]: "\<Gamma> \<turnstile> TypeOperationCall a k op \<sigma> : \<tau>"
inductive_cases iterator_typing [elim]: "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho>"
inductive_cases Iterate_typing [elim]: "\<Gamma> \<turnstile> IterateCall src its res res_t res_init body : \<tau>"
inductive_cases AnyIterator_typing [elim]: "\<Gamma> \<turnstile> AnyIteratorCall src its body : \<tau>"
inductive_cases ClosureIterator_typing [elim]: "\<Gamma> \<turnstile> ClosureIteratorCall src its body : \<tau>"
inductive_cases CollectIterator_typing [elim]: "\<Gamma> \<turnstile> CollectIteratorCall src its body : \<tau>"
inductive_cases CollectNestedIterator_typing [elim]: "\<Gamma> \<turnstile> CollectNestedIteratorCall src its body : \<tau>"
inductive_cases ExistsIterator_typing [elim]: "\<Gamma> \<turnstile> ExistsIteratorCall src its body : \<tau>"
inductive_cases ForAllIterator_typing [elim]: "\<Gamma> \<turnstile> ForAllIteratorCall src its body : \<tau>"
inductive_cases OneIterator_typing [elim]: "\<Gamma> \<turnstile> OneIteratorCall src its body : \<tau>"
inductive_cases IsUniqueIterator_typing [elim]: "\<Gamma> \<turnstile> IsUniqueIteratorCall src its body : \<tau>"
inductive_cases SelectIterator_typing [elim]: "\<Gamma> \<turnstile> SelectIteratorCall src its body : \<tau>"
inductive_cases RejectIterator_typing [elim]: "\<Gamma> \<turnstile> RejectIteratorCall src its body : \<tau>"
inductive_cases SortedByIterator_typing [elim]: "\<Gamma> \<turnstile> SortedByIteratorCall src its body : \<tau>"
inductive_cases AttributeCall_typing [elim]: "\<Gamma> \<turnstile> AttributeCall src prop : \<tau>"
inductive_cases AssociationEndCall_typing [elim]: "\<Gamma> \<turnstile> AssociationEndCall src role : \<tau>"
inductive_cases OperationCall_typing [elim]: "\<Gamma> \<turnstile> OperationCall src k op params : \<tau>"
inductive_cases expr_list_typing [elim]: "expr_list_typing \<Gamma> exprs \<pi>"
inductive_cases TupleElementCall_typing [elim]: "\<Gamma> \<turnstile> TupleElementCall src elem : \<tau>"

(*** Properties *************************************************************)

section \<open>Properties\<close>

lemma
  typing_det: "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  collection_parts_typing_det:
    "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
     collection_parts_typing \<Gamma> prts \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  iterator_typing_det:
    "iterator_typing \<Gamma> src its body \<tau>\<^sub>1 \<sigma>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
     iterator_typing \<Gamma> src its body \<tau>\<^sub>2 \<sigma>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
     \<tau>\<^sub>1 = \<tau>\<^sub>2 \<and> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> \<rho>\<^sub>1 = \<rho>\<^sub>2" and
  expr_list_typing_det:
    "expr_list_typing \<Gamma> exprs \<pi> \<Longrightarrow>
     expr_list_typing \<Gamma> exprs \<xi> \<Longrightarrow> \<pi> = \<xi>"
proof (induct (*\<Gamma> expr \<tau> and \<Gamma> prts \<tau> and \<Gamma> src its body \<tau>\<^sub>1 \<sigma>\<^sub>1 \<rho>\<^sub>1*)
       arbitrary: \<sigma> and \<sigma> and \<tau>\<^sub>2 \<sigma>\<^sub>2 \<rho>\<^sub>2 and \<xi>
       rule: typing_collection_parts_typing_iterator_typing_expr_list_typing.inducts)
  case (NullLiteralT \<Gamma>) thus ?case by auto
next
  case (InvalidLiteralT \<Gamma>) thus ?case by auto
next
  case (BooleanLiteralT \<Gamma> c) thus ?case by auto
next
  case (RealLiteralT \<Gamma> c) thus ?case by auto
next
  case (IntegerLiteralT \<Gamma> c) thus ?case by auto
next
  case (UnlimNatLiteralT \<Gamma> c) thus ?case by auto
next
  case (StringLiteralT \<Gamma> c) thus ?case by auto
next
  case (EnumLiteralT \<Gamma> \<tau> lit) thus ?case by auto
next
  case (CollectionLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (SetLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (OrderedSetLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (BagLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (SequenceLiteralT \<Gamma> prts \<tau>) thus ?case by blast
next
  case (CollectionPartsNilT \<Gamma>) thus ?case by auto
next
  case (CollectionPartsItemT \<Gamma> a \<tau> xs \<sigma>) thus ?case by blast
next
  case (CollectionPartsRangeT \<Gamma> a \<tau> b \<sigma> xs \<rho>) thus ?case
    apply (insert CollectionPartsRangeT.prems)
    apply (erule collection_parts_range_typing)
    by (simp add: CollectionPartsRangeT.hyps(8))
next
  case (EmptyTupleLiteralT \<Gamma>) thus ?case by auto
next
  case (TupleLiteralT \<Gamma> elems \<xi> el \<tau>) thus ?case by blast
next
  case (LetT \<Gamma> \<M> init \<sigma> \<tau> v body \<rho>) thus ?case by blast
next
  case (VarT \<Gamma> v \<tau> \<M>) thus ?case by auto
next
  case (IfT \<Gamma> a \<tau> b \<sigma> c \<rho>) thus ?case
    apply (insert IfT.prems)
    apply (erule If_typing)
    using IfT.hyps(5) IfT.hyps(7) by auto
next
  case (TypeOperationCallT \<Gamma> a \<tau> op \<sigma> \<rho>) thus ?case
    by (metis TypeOperationCall_typing typeop_type_det)
next
  case (IteratorT \<Gamma> \<M> src \<tau> \<sigma> its body \<rho>) thus ?case
    apply (insert IteratorT.prems)
    apply (erule iterator_typing)
    using IteratorT.hyps(2) IteratorT.hyps(3)
          IteratorT.hyps(5) element_type_det by fastforce
next
  case (IterateT \<Gamma> \<M> src its res res_t res_init body \<tau> \<sigma> \<rho>) thus ?case
    by (insert IterateT.prems) (auto simp add: IterateT.hyps(2))
next
  case (AnyIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    by (insert AnyIteratorT.prems) (auto simp add: AnyIteratorT.hyps(2))
next
  case (ClosureIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho> \<upsilon>) thus ?case
    apply (insert ClosureIteratorT.prems)
    apply (erule ClosureIterator_typing)
    using ClosureIteratorT.hyps(2) ClosureIteratorT.hyps(5)
          to_unique_collection_det by blast
next
  case (CollectIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho> \<upsilon>) thus ?case
    apply (insert CollectIteratorT.prems)
    apply (erule CollectIterator_typing)
    using CollectIteratorT.hyps(2) CollectIteratorT.hyps(4)
          CollectIteratorT.hyps(5) to_nonunique_collection_det
          update_element_type_det by blast
next
  case (CollectNestedIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho> \<upsilon>) thus ?case
    apply (insert CollectNestedIteratorT.prems)
    apply (erule CollectNestedIterator_typing)
    using CollectNestedIteratorT.hyps(2) CollectNestedIteratorT.hyps(4)
          CollectNestedIteratorT.hyps(5) to_nonunique_collection_det
          update_element_type_det by blast
next
  case (ExistsIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    apply (insert ExistsIteratorT.prems)
    apply (erule ExistsIterator_typing)
    by (simp add: ExistsIteratorT.hyps(2))
next
  case (ForAllIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    apply (insert ForAllIteratorT.prems)
    apply (erule ForAllIterator_typing)
    by (simp add: ForAllIteratorT.hyps(2))
next
  case (OneIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    apply (insert OneIteratorT.prems)
    apply (erule OneIterator_typing)
    by simp
next
  case (IsUniqueIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    apply (insert IsUniqueIteratorT.prems)
    apply (erule IsUniqueIterator_typing)
    by simp
next
  case (RejectIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    apply (insert RejectIteratorT.prems)
    apply (erule RejectIterator_typing)
    by (simp add: RejectIteratorT.hyps(2))
next
  case (SelectIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho>) thus ?case
    apply (insert SelectIteratorT.prems)
    apply (erule SelectIterator_typing)
    by (simp add: SelectIteratorT.hyps(2))
next
  case (SortedByIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho> \<upsilon>) thus ?case
    apply (insert SortedByIteratorT.prems)
    apply (erule SortedByIterator_typing)
    using SortedByIteratorT.hyps(2) SortedByIteratorT.hyps(4)
          to_ordered_collection_det by blast
next
  case (AttributeCallT \<Gamma> src \<tau> cls "prop" cls2 \<sigma>) thus ?case
    apply (insert AttributeCallT.prems)
    apply (erule AttributeCall_typing)
    using AttributeCallT.hyps(2) AttributeCallT.hyps(3)
          AttributeCallT.hyps(4) class_of_det by fastforce
next
  case (AssociationEndCallT \<Gamma> src \<tau> cls role "end") thus ?case
    apply (insert AssociationEndCallT.prems)
    apply (erule AssociationEndCall_typing)
    using AssociationEndCallT.hyps(2) AssociationEndCallT.hyps(3)
          AssociationEndCallT.hyps(4) class_of_det by fastforce
next
  case (OperationCallT \<Gamma> src \<tau> params \<pi> op k) show ?case
    apply (insert OperationCallT.prems)
    apply (erule OperationCall_typing)
    using OperationCallT.hyps(2) OperationCallT.hyps(4)
          OperationCallT.hyps(5) op_type_det by blast
next
  case (ExprListNilT \<Gamma>) thus ?case
    using expr_list_typing.cases by auto
next
  case (ExprListConsT \<Gamma> expr \<tau> exprs \<pi>) show ?case
    apply (insert ExprListConsT.prems)
    apply (erule expr_list_typing)
    by (simp_all add: ExprListConsT.hyps(2) ExprListConsT.hyps(4))
next
  case (TupleElementCallT \<Gamma> src \<pi> elem \<tau>)
  then show ?case 
    apply (insert TupleElementCallT.prems)
    apply (erule TupleElementCall_typing)
    using TupleElementCallT.hyps(2) TupleElementCallT.hyps(3) by fastforce
next
  case (MetaOperationCallT \<tau> op \<sigma> \<Gamma>) thus ?case
    by (metis MetaOperationCall_typing mataop_type.cases)
next
  case (StaticOperationCallT \<tau> op \<pi> oper \<Gamma> as)
  then show ?case
    apply (insert StaticOperationCallT.prems)
    apply (erule StaticOperationCall_typing)
    using StaticOperationCallT.hyps(2) StaticOperationCallT.hyps(3) by auto
qed

(*
non_strict_op both for null and error
=, <>, oclAsType, oclIsInState, oclIsKindOf, oclIsTypeOf,
oclIsInvalid, oclIsUndefined, oclType, oclIsNew, oclAsSet
and, implies, not, or, xor

и ещё особый случай:
null.oclAsSet() = Set{}
invalid.oclAsSet() = invalid

Видимо в спецификации ошибка:

для null результат этих операций тоже будет invalid:
oclIsKindOf, oclIsTypeOf
Не понимаю зачем это сделано.
На самом деле там определено так для OclVoid, а не null

для invalid результат этих операций тоже будет invalid:
=, <>, oclAsType, oclIsInState, oclIsKindOf, oclIsTypeOf,
oclIsNew, oclAsSet

По идее должно быть так:
null.oclIsTypeOf(OclVoid) = true
null.oclIsTypeOf(OclInvalid) = false
invalid.oclIsTypeOf(OclVoid) = true
invalid.oclIsTypeOf(OclInvalid) = true

Сравнение invalid не имеет смысла, иначе можно получить:
1/0 = 2/0
Т.е. это обычная strict операция

*)


(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>
(*
code_pred [show_modes] typeop_type .
code_pred [show_modes] unop_type .
code_pred [show_modes] binop_type .
code_pred [show_modes] ternop_type .
code_pred [show_modes] class_of .
code_pred [show_modes] typing .

code_pred [show_modes] collection_binop_type .
*)
code_pred (modes:
  i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as check_type,
  i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as synthesize_type) [show_modes] typing .

end

(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* OCL Typing Rules *}
theory OCL_Typing
  imports OCL_Syntax OCL_Types Object_Model "HOL-Library.Transitive_Closure_Table"
begin

(*** Standard Library Operations Typing *************************************)

subsection{* Standard Library Operations Typing *}

text{* The following rules are more restrictive than rules given in
 the OCL Specification. This allows one to identify more errors
 in expressions. However, these restrictions may be revised if necessary.
 Perhaps some of them could be separated and should cause warnings
 instead of errors. *}

text{* Only casting to a subtype makes sense. *}

text{* According to the section 7.4.7 of the OCL specification
 oclAsType() can be applied to collections as well as to single
 values. I guess we can allow oclIsTypeOf() and oclIsKindOf()
 for collections too. *}

inductive typeop_type where
  "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type OclAsTypeOp \<tau> \<sigma> \<sigma>"
| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type OclIsTypeOfOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   typeop_type OclIsKindOfOp \<tau> \<sigma> Boolean[1]"
| "strict_subcollection \<tau> \<sigma> \<rho> \<Longrightarrow>
   typeop_type SelectByKindOp \<tau> \<sigma> \<rho>"
| "strict_subcollection \<tau> \<sigma> \<rho> \<Longrightarrow>
   typeop_type SelectByTypeOp \<tau> \<sigma> \<rho>"

code_pred [show_modes] typeop_type .

values "{x. typeop_type SelectByKindOp (Set Real[?] :: classes1 type) Integer[1] x}"

text{* It makes sense to compare values only with compatible types. *}

inductive suptype_binop_type where
  "\<tau> \<le> \<sigma> \<Longrightarrow>
   suptype_binop_type EqualOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   suptype_binop_type EqualOp \<tau> \<sigma> Boolean[1]"
| "\<tau> \<le> \<sigma> \<Longrightarrow>
   suptype_binop_type NotEqualOp \<tau> \<sigma> Boolean[1]"
| "\<sigma> < \<tau> \<Longrightarrow>
   suptype_binop_type NotEqualOp \<tau> \<sigma> Boolean[1]"

text{* The OCL specification defines toString() operation only for
 boolean and numeric types. However, I guess it's a good idea to
 define it once for all basic types. *}

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

inductive boolean_unop_type where
  "\<tau> \<le> Boolean[?] \<Longrightarrow>
   boolean_unop_type NotOp \<tau> \<tau>"

inductive boolean_binop_type where
  "\<lbrakk>\<tau> \<squnion> \<sigma> = \<rho>; \<rho> \<le> Boolean[?]\<rbrakk> \<Longrightarrow>
   boolean_binop_type AndOp \<tau> \<sigma> \<rho>"
| "\<lbrakk>\<tau> \<squnion> \<sigma> = \<rho>; \<rho> \<le> Boolean[?]\<rbrakk> \<Longrightarrow>
   boolean_binop_type OrOp \<tau> \<sigma> \<rho>"
| "\<lbrakk>\<tau> \<squnion> \<sigma> = \<rho>; \<rho> \<le> Boolean[?]\<rbrakk> \<Longrightarrow>
   boolean_binop_type XorOp \<tau> \<sigma> \<rho>"
| "\<lbrakk>\<tau> \<squnion> \<sigma> = \<rho>; \<rho> \<le> Boolean[?]\<rbrakk> \<Longrightarrow>
   boolean_binop_type ImpliesOp \<tau> \<sigma> \<rho>"

text{* Formally null conforms to numeric types. However expressions
 like 'null + null' makes no sense. So we use UnlimitedNatural[1]
 as a lower bound. *}

text{* Please take a note that many operations automatically casts
 unlimited naturals to integers. *}

text{* The difference between oclAsType(Integer) and toInteger()
 for unlimited naturals is unclear. *}

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
| "\<lbrakk>\<tau> \<simeq> String; \<sigma> \<simeq> String\<rbrakk> \<Longrightarrow>
   string_binop_type IndexOfOp \<tau> \<sigma> Integer[1]"
| "\<lbrakk>\<tau> \<simeq> String; \<sigma> \<simeq> Integer\<rbrakk> \<Longrightarrow>
   string_binop_type AtOp \<tau> \<sigma> String[1]"

inductive string_ternop_type where
  "\<lbrakk>\<tau> \<simeq> String; \<sigma> \<simeq> Integer; \<rho> \<simeq> Integer\<rbrakk> \<Longrightarrow>
   string_ternop_type SubstringOp \<tau> \<sigma> \<rho> String[1]"

text{* Please take a note, that flatten() preserves collection kind. *}

inductive collection_unop_type where
  "\<lbrakk>is_collection_of \<tau> _\<rbrakk> \<Longrightarrow>
   collection_unop_type CollectionSizeOp \<tau> Integer[1]"
| "\<lbrakk>is_collection_of \<tau> _\<rbrakk> \<Longrightarrow>
   collection_unop_type IsEmptyOp \<tau> Boolean[1]"
| "\<lbrakk>is_collection_of \<tau> _\<rbrakk> \<Longrightarrow>
   collection_unop_type NotEmptyOp \<tau> Boolean[1]"

| "\<lbrakk>is_collection_of \<tau> \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real\<rbrakk> \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> \<sigma>"
| "\<lbrakk>is_collection_of \<tau> \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real\<rbrakk> \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> \<sigma>"
| "\<lbrakk>is_collection_of \<tau> \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real\<rbrakk> \<Longrightarrow>
   collection_unop_type SumOp \<tau> \<sigma>"

| "\<lbrakk>is_collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsSetOp \<tau> (Set \<sigma>)"
| "\<lbrakk>is_collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsOrderedSetOp \<tau> (OrderedSet \<sigma>)"
| "\<lbrakk>is_collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsBagOp \<tau> (Bag \<sigma>)"
| "\<lbrakk>is_collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsSequenceOp \<tau> (Sequence \<sigma>)"

| "\<lbrakk>inner_element_type \<tau> \<sigma>; update_element_type \<tau> \<sigma> \<rho>\<rbrakk> \<Longrightarrow>
   collection_unop_type FlattenOp \<tau> \<rho>"

| "collection_unop_type FirstOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type FirstOp (Sequence \<tau>) \<tau>"
| "collection_unop_type LastOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type LastOp (Sequence \<tau>) \<tau>"
| "collection_unop_type ReverseOp (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "collection_unop_type ReverseOp (Sequence \<tau>) (Sequence \<tau>)"

code_pred [show_modes] collection_unop_type .

values "{x. collection_unop_type FlattenOp
    (Set Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type FlattenOp
    (Sequence (Set Boolean[?] :: classes1 type)) (x :: classes1 type)}"
values "{x. collection_unop_type FlattenOp
    (Bag (Set (Sequence Real[?] :: classes1 type))) (x :: classes1 type)}"
values "{x. collection_unop_type CollectionMaxOp
    (Collection Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type CollectionMaxOp
    (Set Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type CollectionSizeOp
    (Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type CollectionSizeOp
    (Set Boolean[1] :: classes1 type) (x :: classes1 type)}"

text{* Tuples must support string keys and the rule for the product()
 operation must be updated. *}

text{* Please take a note that if both arguments are collections,
 then an element type of the resulting collection is a super type
 of element types of orginal collections. However for single-valued
 operations (including(), insertAt(), ...) this behavior looks
 undesirable. So we restrict such arguments to have a subtype of
 the collection element type. *}

text{* It's unclear what is the result of the indexOf() operation
 if the item not found: null or invalid? *}

fun type_to_optional where
  "type_to_optional SupType = SupType"
| "type_to_optional OclInvalid = OclVoid"
| "type_to_optional OclVoid = OclVoid"
| "type_to_optional \<tau>[1] = \<tau>[?]"
| "type_to_optional \<tau>[?] = \<tau>[?]"
| "type_to_optional (Collection \<tau>) = Collection (type_to_optional \<tau>)"
| "type_to_optional (Set \<tau>) = Set (type_to_optional \<tau>)"
| "type_to_optional (OrderedSet \<tau>) = OrderedSet (type_to_optional \<tau>)"
| "type_to_optional (Bag \<tau>) = Bag (type_to_optional \<tau>)"
| "type_to_optional (Sequence \<tau>) = Sequence (type_to_optional \<tau>)"
| "type_to_optional (Tuple \<pi>) = Tuple (fmmap type_to_optional \<pi>)"

inductive collection_binop_type where
(*  "\<lbrakk>is_collection_of \<tau> \<rho>; \<sigma> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type IncludesOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>is_collection_of \<tau> \<rho>; \<sigma> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type ExcludesOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>is_collection_of \<tau> \<rho>; \<sigma> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type CountOp \<tau> \<sigma> Integer[1]"
| "\<lbrakk>is_collection_of \<tau> \<rho>; is_collection_of \<sigma> \<upsilon>; \<upsilon> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type IncludesAllOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>is_collection_of \<tau> \<rho>; is_collection_of \<sigma> \<upsilon>; \<upsilon> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type ExcludesAllOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>is_collection_of \<tau> \<rho>; is_collection_of \<sigma> \<upsilon>\<rbrakk> \<Longrightarrow>
   collection_binop_type ProductOp \<tau> \<sigma> (Tuple (fmap_of_list [(0, \<rho>), (1, \<upsilon>)]))"
|*) "collection_binop_type UnionOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Set \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Bag \<tau>) (Set \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type UnionOp (Bag \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Set \<tau>) (Bag \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Bag \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type IntersectionOp (Bag \<tau>) (Bag \<sigma>) (Bag (\<tau> \<squnion> \<sigma>))"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type IncludingOp (Set \<tau>) \<sigma> (Set \<tau>)"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type IncludingOp (Bag \<tau>) \<sigma> (Bag \<tau>)"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type ExcludingOp (Set \<tau>) \<sigma> (Set \<tau>)"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type ExcludingOp (Bag \<tau>) \<sigma> (Bag \<tau>)"
| "collection_binop_type SetMinusOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "collection_binop_type SymmetricDifferenceOp (Set \<tau>) (Set \<sigma>) (Set (\<tau> \<squnion> \<sigma>))"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type AppendOp (OrderedSet \<tau>) \<sigma> (OrderedSet \<tau>)"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type AppendOp (Sequence \<tau>) \<sigma> (Sequence \<tau>)"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type PrependOp (OrderedSet \<tau>) \<sigma> (OrderedSet \<tau>)"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type PrependOp (Sequence \<tau>) \<sigma> (Sequence \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> Integer\<rbrakk> \<Longrightarrow>
   collection_binop_type CollectionAtOp (OrderedSet \<tau>) \<sigma> \<tau>"
| "\<lbrakk>\<sigma> \<simeq> Integer\<rbrakk> \<Longrightarrow>
   collection_binop_type CollectionAtOp (Sequence \<tau>) \<sigma> \<tau>"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (OrderedSet \<tau>) \<sigma> Integer[1]"
| "\<lbrakk>\<sigma> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_binop_type CollectionIndexOfOp (Sequence \<tau>) \<sigma> Integer[1]"

code_pred [show_modes] collection_binop_type .

values "{x. collection_binop_type ProductOp
    (Set Boolean[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_binop_type IncludesOp
    (Set Integer[1] :: classes1 type) (Integer[?] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_binop_type IncludesAllOp
    (Set Real[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"

inductive collection_ternop_type where
  "\<lbrakk>\<sigma> \<simeq> Integer; \<rho> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_ternop_type InsertAtOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> Integer; \<rho> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_ternop_type InsertAtOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> Integer; \<rho> \<simeq> Integer\<rbrakk> \<Longrightarrow>
   collection_ternop_type SubOrderedSetOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> Integer; \<rho> \<simeq> Integer\<rbrakk> \<Longrightarrow>
   collection_ternop_type SubSequenceOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"

inductive unop_type where
  "any_unop_type op t1 t \<Longrightarrow>
   unop_type (Inl op) t1 t"
| "boolean_unop_type op t1 t \<Longrightarrow>
   unop_type (Inr (Inl op)) t1 t"
| "numeric_unop_type op t1 t \<Longrightarrow>
   unop_type (Inr (Inr (Inl op))) t1 t"
| "string_unop_type op t1 t \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inl op)))) t1 t"
| "collection_unop_type op t1 t \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inr op)))) t1 t"

inductive binop_type where
  "suptype_binop_type op t1 t2 t \<Longrightarrow>
   binop_type (Inl op) t1 t2 t"
| "boolean_binop_type op t1 t2 t \<Longrightarrow>
   binop_type (Inr (Inl op)) t1 t2 t"
| "numeric_binop_type op t1 t2 t \<Longrightarrow>
   binop_type (Inr (Inr (Inl op))) t1 t2 t"
| "string_binop_type op t1 t2 t \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inl op)))) t1 t2 t"
| "collection_binop_type op t1 t2 t \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inr op)))) t1 t2 t"

inductive ternop_type where
  "string_ternop_type op t1 t2 t3 t \<Longrightarrow>
   ternop_type (Inl op) t1 t2 t3 t"
| "collection_ternop_type op t1 t2 t3 t \<Longrightarrow>
   ternop_type (Inr op) t1 t2 t3 t"

code_pred [show_modes] typeop_type .
code_pred [show_modes] unop_type .
code_pred [show_modes] binop_type .
code_pred [show_modes] ternop_type .

(*** Expressions Typing *****************************************************)

subsection{* Expressions Typing *}

term "map (\<lambda>x. (fst x, fst (snd x)))"

inductive class_of :: "'a type \<Rightarrow> 'a \<Rightarrow> bool" where
  "class_of (ObjectType cls)[1] cls"
| "class_of (ObjectType cls)[?] cls"
(*
fun collection_parts_type where
  "collection_parts_type [] = OclVoid"
| "collection_parts_type (x # xs) = x \<squnion> collection_parts_type xs"
*)

inductive typing :: "('a :: semilattice_sup) type env \<times> 'a model \<Rightarrow> 'a expr \<Rightarrow> 'a type \<Rightarrow> bool"
    ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
    and collection_parts_type
    and iterator_typing where
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
  "\<Gamma> \<turnstile> EnumLiteral t lit : t"

|CollectionLiteralT:
  "collection_parts_type \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral CollectionKind prts : Collection \<tau>"
|SetLiteralT:
  "collection_parts_type \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral SetKind prts : Set \<tau>"
|OrderedSetLiteralT:
  "collection_parts_type \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral OrderedSetKind prts : OrderedSet \<tau>"
|BagLiteralT:
  "collection_parts_type \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral BagKind prts : Bag \<tau>"
|SequenceLiteralT:
  "collection_parts_type \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral SequenceKind prts : Sequence \<tau>"

| "collection_parts_type \<Gamma> [] OclInvalid"
| "\<Gamma> \<turnstile> x : t1 \<Longrightarrow> collection_parts_type \<Gamma> xs t2 \<Longrightarrow>
   collection_parts_type \<Gamma> (CollectionItem x # xs) (t1 \<squnion> t2)"
| "\<lbrakk>\<Gamma> \<turnstile> a : t1; Integer[1] \<le> t1; t1 \<le> Integer[?];
    \<Gamma> \<turnstile> b : t2; Integer[1] \<le> t2; t2 \<le> Integer[?];
    collection_parts_type \<Gamma> xs t3\<rbrakk> \<Longrightarrow>
   collection_parts_type \<Gamma> (CollectionRange a b # xs) (Integer[1] \<squnion> t3)"

|TupleLiteralT:
  "\<Gamma> \<turnstile> TupleLiteral el : Tuple (fmap_of_list (map (\<lambda>x. (fst x, fst (snd x))) el))"

|LetT:
  "(\<Gamma>, \<M>) \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   \<tau>\<^sub>1 \<le> t \<Longrightarrow>
   (\<Gamma>(v\<mapsto>t), \<M>) \<turnstile> body : \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Let v t init body : \<tau>"
|VarT:
  "\<Gamma> v = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Var v : \<tau>"

|IfT:
  "\<Gamma> \<turnstile> a : t1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : t2 \<Longrightarrow>
   \<Gamma> \<turnstile> c : t3 \<Longrightarrow>
   t1 \<le> Boolean[?] \<Longrightarrow>
   t2 \<squnion> t3 = \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> If a b c : \<tau>"

|TypeOperationCallT:
  "\<Gamma> \<turnstile> a : t1 \<Longrightarrow>
   typeop_type op t1 t2 \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> TypeOperationCall op a t2 : \<tau>"
|UnaryOperationCallT:
  "\<Gamma> \<turnstile> a : t1 \<Longrightarrow>
   unop_type op t1 \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> UnaryOperationCall op a : \<tau>"
|BinaryOperationCallT:
  "\<Gamma> \<turnstile> a : t1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : t2 \<Longrightarrow>
   binop_type op t1 t2 \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> BinaryOperationCall op a b : \<tau>"
|TernaryOperationCallT:
  "\<Gamma> \<turnstile> a : t1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : t2 \<Longrightarrow>
   \<Gamma> \<turnstile> c : t3 \<Longrightarrow>
   ternop_type op t1 t2 t3 \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> TernaryOperationCall op a b c : \<tau>"

|IterateT:
  "(\<Gamma>, \<M>) \<turnstile> src : t \<Longrightarrow>
   is_collection_of t t1 \<Longrightarrow>
   (\<Gamma> ++ (map_of (map (\<lambda>it. (it, t1)) its)), \<M>) \<turnstile> Let res res_t res_init body : \<tau> \<Longrightarrow>
   \<tau> \<le> res_t \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterate src its res res_t res_init body : \<tau>"

|AnyIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator AnyIter src its body : t1"
|ClosureIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<le> Set t1 \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator ClosureIter src its body : Set t1"
|CollectIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<le> t1 \<Longrightarrow>
   (* TODO *)
   (\<Gamma>, \<M>) \<turnstile> Iterator CollectIter src its body : t1"
|CollectNestedIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   (* TODO *)
   (\<Gamma>, \<M>) \<turnstile> Iterator CollectNestedIter src its body : \<tau>"
|ExistsIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator ExistsIter src its body : \<tau>"
|ForAllIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator ForAllIter src its body : \<tau>"
|IsUniqueIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator IsUniqueIter src its body : Boolean[1]"
|OneIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator OneIter src its body : Boolean[1]"
|RejectIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator RejectIter src its body : t"
|SelectIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator SelectIter src its body : t"

| "(\<Gamma>, \<M>) \<turnstile> src : t \<Longrightarrow>
   is_collection_of t t1 \<Longrightarrow>
   (\<Gamma> ++ (map_of (map (\<lambda>it. (it, t1)) its)), \<M>) \<turnstile> body : \<tau> \<Longrightarrow>
   iterator_typing (\<Gamma>, \<M>) src its body t t1 \<tau>"

|AttributeCallT:
  "\<M> = (attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : t \<Longrightarrow>
   class_of t cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> AttributeCall src prop : \<tau>"
|AssociationEndCallT:
  "\<M> = (attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : t \<Longrightarrow>
   class_of t cls \<Longrightarrow>
   find_assoc_end assocs cls role = Some end \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> AssociationEndCall src role : assoc_end_type end"

(*** Code Setup *************************************************************)

section{* Code Setup *}

code_pred [show_modes] typing .

(*
code_pred (modes:
    i * i * i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as check_type,
    i * i * i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as synthesize_type) typing .
*)

(*** Test Cases *************************************************************)

section{* Test Cases *}

abbreviation BinaryOperationCall'
  :: "binop \<Rightarrow> classes1 expr \<Rightarrow> classes1 expr \<Rightarrow> classes1 call_expr" where
  "BinaryOperationCall' \<equiv> BinaryOperationCall"

abbreviation Let'
  :: "string \<Rightarrow> classes1 type \<Rightarrow> classes1 expr \<Rightarrow> classes1 expr \<Rightarrow> classes1 expr" where
  "Let' \<equiv> Let"

term model1

values "{x :: classes1 type. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let' ''x'' Integer[1] (IntegerLiteral 5)
    (Var ''x'') : x}"

values "{x :: classes1 type. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Integer[1] (IntegerLiteral 5)
    (BinaryOperationCall' PlusOp (Var ''x'') (IntegerLiteral 7)) : x}"
values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Real[?] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (IntegerLiteral 7)): x}"
values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Real[1] (IntegerLiteral 5)
    (BinaryOperationCall AndOp (Var ''x'') (BooleanLiteral True)): x}"
values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Boolean[1] (IntegerLiteral 5)
    (BinaryOperationCall AndOp (Var ''x'') (BooleanLiteral True)): x}"
values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Integer[1] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (BooleanLiteral True)): x}"

values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5), CollectionItem (RealLiteral 5)]) : x}"

values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Iterate (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem (RealLiteral 5)]) [''x'']
      ''acc'' Integer[1] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (Var ''acc'')): x}"

(*values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  BinaryOperationCall OrOp (BooleanLiteral True) (BooleanLiteral False) : x}"
values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  BinaryOperationCall OrOp (IntegerLiteral 1) (BooleanLiteral False) : x}"
values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  BinaryOperationCall PlusOp (IntegerLiteral 1) (IntegerLiteral 3) : x}"
values "{x. ([''self'' \<mapsto> (ObjectType Employee)[1]] :: classes1 type env, model1) \<turnstile>
  (Var ''self'') : x}"
values "{x. ([''self'' \<mapsto> (ObjectType Employee)[1]] :: classes1 type env, model1) \<turnstile>
  AttributeCall (Var ''self'') ''position'' : x}"
values "{x. ([''self'' \<mapsto> (ObjectType Employee)[?]] :: classes1 type env, model1) \<turnstile>
  AssociationEndCall (Var ''self'') ''manages'' : x}"
values "{x. ([''self'' \<mapsto> (ObjectType Project)[?]] :: classes1 type env, model1) \<turnstile>
  AssociationEndCall (Var ''self'') ''manager'' : x}"*)

end

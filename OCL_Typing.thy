(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* OCL Typing Rules *}
theory OCL_Typing
  imports OCL_Syntax Object_Model
begin

(*** Standard Library Operations Typing *************************************)

section{* Standard Library Operations Typing *}

text{* The following rules are more restrictive than rules given in
 the OCL Specification. This allows one to identify more errors
 in expressions. However, these restrictions may be revised if necessary.
 Perhaps some of them could be separated and should cause warnings
 instead of errors. *}

text{* Only casting to a subtype makes sense. *}

text{* According to the section 7.4.7 of the OCL Specification
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
(*
code_pred [show_modes] typeop_type .

values "{x. typeop_type SelectByKindOp (Set Real[?] :: classes1 type) Integer[1] x}"
*)
text{* It makes sense to compare values only with compatible types. *}

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
(*
code_pred [show_modes] suptype_binop_type .
*)
text{* The OCL Specification defines toString() operation only for
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
| "\<lbrakk>\<tau> \<simeq> String; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer\<rbrakk> \<Longrightarrow>
   string_binop_type AtOp \<tau> \<sigma> String[1]"

inductive string_ternop_type where
  "\<lbrakk>\<tau> \<simeq> String; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer; \<rho> \<simeq> UnlimitedNatural\<midarrow>Integer\<rbrakk> \<Longrightarrow>
   string_ternop_type SubstringOp \<tau> \<sigma> \<rho> String[1]"

text{* Please take a note, that flatten() preserves collection kind. *}

inductive collection_unop_type where
  "\<lbrakk>collection_of \<tau> _\<rbrakk> \<Longrightarrow>
   collection_unop_type CollectionSizeOp \<tau> Integer[1]"
| "\<lbrakk>collection_of \<tau> _\<rbrakk> \<Longrightarrow>
   collection_unop_type IsEmptyOp \<tau> Boolean[1]"
| "\<lbrakk>collection_of \<tau> _\<rbrakk> \<Longrightarrow>
   collection_unop_type NotEmptyOp \<tau> Boolean[1]"

| "\<lbrakk>collection_of \<tau> \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real\<rbrakk> \<Longrightarrow>
   collection_unop_type CollectionMaxOp \<tau> \<sigma>"
| "\<lbrakk>collection_of \<tau> \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real\<rbrakk> \<Longrightarrow>
   collection_unop_type CollectionMinOp \<tau> \<sigma>"
| "\<lbrakk>collection_of \<tau> \<sigma>; \<sigma> \<simeq> UnlimitedNatural\<midarrow>Real\<rbrakk> \<Longrightarrow>
   collection_unop_type SumOp \<tau> \<sigma>"

| "\<lbrakk>collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsSetOp \<tau> (Set \<sigma>)"
| "\<lbrakk>collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsOrderedSetOp \<tau> (OrderedSet \<sigma>)"
| "\<lbrakk>collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsBagOp \<tau> (Bag \<sigma>)"
| "\<lbrakk>collection_of \<tau> \<sigma>\<rbrakk> \<Longrightarrow>
   collection_unop_type AsSequenceOp \<tau> (Sequence \<sigma>)"

(*| "\<lbrakk>inner_element_type \<tau> \<sigma>; update_element_type \<tau> \<sigma> \<rho>\<rbrakk> \<Longrightarrow>*)
| "\<lbrakk>collection_of \<tau> \<sigma>; update_element_type \<tau> (type_to_single \<sigma>) \<rho>\<rbrakk> \<Longrightarrow>
   collection_unop_type FlattenOp \<tau> \<rho>"

| "collection_unop_type FirstOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type FirstOp (Sequence \<tau>) \<tau>"
| "collection_unop_type LastOp (OrderedSet \<tau>) \<tau>"
| "collection_unop_type LastOp (Sequence \<tau>) \<tau>"
| "collection_unop_type ReverseOp (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "collection_unop_type ReverseOp (Sequence \<tau>) (Sequence \<tau>)"
(*
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
*)
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

inductive collection_binop_type where
  "\<lbrakk>collection_of \<tau> \<rho>; \<sigma> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type IncludesOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>collection_of \<tau> \<rho>; \<sigma> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type ExcludesOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>collection_of \<tau> \<rho>; \<sigma> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type CountOp \<tau> \<sigma> Integer[1]"
| "\<lbrakk>collection_of \<tau> \<rho>; collection_of \<sigma> \<upsilon>; \<upsilon> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type IncludesAllOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>collection_of \<tau> \<rho>; collection_of \<sigma> \<upsilon>; \<upsilon> \<le> type_to_optional \<rho>\<rbrakk> \<Longrightarrow>
   collection_binop_type ExcludesAllOp \<tau> \<sigma> Boolean[1]"
| "\<lbrakk>collection_of \<tau> \<rho>; collection_of \<sigma> \<upsilon>\<rbrakk> \<Longrightarrow>
   collection_binop_type ProductOp \<tau> \<sigma> (Tuple (fmap_of_list [(0, \<rho>), (1, \<upsilon>)]))"
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
   collection_binop_type ExcludingOp (Set \<tau>) \<sigma> (Set \<tau>)"
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
(*
code_pred [show_modes] collection_binop_type .

values "{x. collection_binop_type ProductOp
    (Set Boolean[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_binop_type IncludesOp
    (Set Integer[1] :: classes1 type) (Integer[?] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_binop_type IncludesAllOp
    (Set Real[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"
*)
inductive collection_ternop_type where
  "\<lbrakk>\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer; \<rho> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_ternop_type InsertAtOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer; \<rho> \<le> \<tau>\<rbrakk> \<Longrightarrow>
   collection_ternop_type InsertAtOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer; \<rho> \<simeq> UnlimitedNatural\<midarrow>Integer\<rbrakk> \<Longrightarrow>
   collection_ternop_type SubOrderedSetOp (OrderedSet \<tau>) \<sigma> \<rho> (OrderedSet \<tau>)"
| "\<lbrakk>\<sigma> \<simeq> UnlimitedNatural\<midarrow>Integer; \<rho> \<simeq> UnlimitedNatural\<midarrow>Integer\<rbrakk> \<Longrightarrow>
   collection_ternop_type SubSequenceOp (Sequence \<tau>) \<sigma> \<rho> (Sequence \<tau>)"

inductive unop_type where
  "any_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inl op) \<tau> \<sigma>"
| "boolean_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inl op)) \<tau> \<sigma>"
| "numeric_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inl op))) \<tau> \<sigma>"
| "string_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inl op)))) \<tau> \<sigma>"
| "collection_unop_type op \<tau> \<sigma> \<Longrightarrow>
   unop_type (Inr (Inr (Inr (Inr op)))) \<tau> \<sigma>"

inductive binop_type where
  "suptype_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inl op) \<tau> \<sigma> \<rho>"
| "boolean_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inl op)) \<tau> \<sigma> \<rho>"
| "numeric_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inl op))) \<tau> \<sigma> \<rho>"
| "string_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inl op)))) \<tau> \<sigma> \<rho>"
| "collection_binop_type op \<tau> \<sigma> \<rho> \<Longrightarrow>
   binop_type (Inr (Inr (Inr (Inr op)))) \<tau> \<sigma> \<rho>"

inductive ternop_type where
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inl op) \<tau> \<sigma> \<rho> \<upsilon>"
| "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon> \<Longrightarrow>
   ternop_type (Inr op) \<tau> \<sigma> \<rho> \<upsilon>"
(*
code_pred [show_modes] typeop_type .
code_pred [show_modes] unop_type .
code_pred [show_modes] binop_type .
code_pred [show_modes] ternop_type .
*)
(*** Expressions Typing *****************************************************)

section{* Expressions Typing *}

inductive typing
    :: "('a :: semilattice_sup) type env \<times> 'a model \<Rightarrow> 'a expr \<Rightarrow> 'a type \<Rightarrow> bool"
       ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
    and collection_parts_typing
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
  "\<Gamma> \<turnstile> EnumLiteral \<tau> lit : \<tau>"

|CollectionLiteralT:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> CollectionLiteral CollectionKind prts : Collection \<tau>"
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

|TupleLiteralT:
  "\<Gamma> \<turnstile> TupleLiteral elems : Tuple (fmap_of_list (map (\<lambda>x. (fst x, fst (snd x))) elems))"

|LetT:
  "\<lbrakk>(\<Gamma>, \<M>) \<turnstile> init : \<sigma>; \<sigma> \<le> \<tau>; (\<Gamma>(v\<mapsto>\<tau>), \<M>) \<turnstile> body : \<rho>\<rbrakk> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Let v \<tau> init body : \<rho>"
|VarT:
  "\<Gamma> v = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Var v : \<tau>"

|IfT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; \<tau> \<le> Boolean[?]; \<Gamma> \<turnstile> b : \<sigma>; \<Gamma> \<turnstile> c : \<rho>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> If a b c : \<sigma> \<squnion> \<rho>"

|OclTypeT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> OclType a : \<tau>"
|TypeOperationCallT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; typeop_type op \<tau> \<sigma> \<rho>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> TypeOperationCall op a \<sigma> : \<rho>"
|UnaryOperationCallT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; unop_type op \<tau> \<sigma> \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> UnaryOperationCall op a : \<sigma>"
|BinaryOperationCallT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; \<Gamma> \<turnstile> b : \<sigma>; binop_type op \<tau> \<sigma> \<rho>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> BinaryOperationCall op a b : \<rho>"
|TernaryOperationCallT:
  "\<lbrakk>\<Gamma> \<turnstile> a : \<tau>; \<Gamma> \<turnstile> b : \<sigma>; \<Gamma> \<turnstile> c : \<rho>; ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> TernaryOperationCall op a b c : \<upsilon>"

|IteratorT:
  "(\<Gamma>, \<M>) \<turnstile> src : \<tau> \<Longrightarrow>
   collection_of \<tau> \<sigma> \<Longrightarrow>
   (\<Gamma> ++ (map_of (map (\<lambda>it. (it, \<sigma>)) its)), \<M>) \<turnstile> body : \<rho> \<Longrightarrow>
   iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho>"

|IterateT:
  "\<lbrakk>iterator_typing (\<Gamma>, \<M>) src its (Let res res_t res_init body) \<tau> \<sigma> \<rho>; \<rho> \<le> res_t\<rbrakk> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterate src its res res_t res_init body : \<rho>"

|AnyIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator AnyIter src its body : \<sigma>"
|ClosureIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   type_to_single \<rho> \<le> \<sigma> \<Longrightarrow>
   to_unique_collection \<tau> \<upsilon> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator ClosureIter src its body : \<upsilon>"
|CollectIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   update_element_type \<tau> (type_to_single \<rho>) \<upsilon> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator CollectIter src its body : \<upsilon>"
|CollectNestedIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   update_element_type \<tau> \<rho> \<upsilon> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator CollectNestedIter src its body : \<upsilon>"
|ExistsIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator ExistsIter src its body : \<rho>"
|ForAllIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator ForAllIter src its body : \<rho>"
|OneIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator OneIter src its body : Boolean[1]"
|IsUniqueIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator IsUniqueIter src its body : Boolean[1]"
|RejectIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator RejectIter src its body : \<tau>"
|SelectIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   \<rho> \<le> Boolean[?] \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator SelectIter src its body : \<tau>"
|SortedByIteratorT:
  "iterator_typing (\<Gamma>, \<M>) src its body \<tau> \<sigma> \<rho> \<Longrightarrow>
   length its \<le> 1 \<Longrightarrow>
   to_ordered_collection \<tau> \<upsilon> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Iterator SortedByIter src its body : \<upsilon>"

|AttributeCallT:
  "\<M> = (attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : \<tau> \<Longrightarrow>
   class_of \<tau> cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<sigma> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> AttributeCall src prop : \<sigma>"
|AssociationEndCallT:
  "\<M> = (attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : \<tau> \<Longrightarrow>
   class_of \<tau> cls \<Longrightarrow>
   find_assoc_end assocs cls role = Some end \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> AssociationEndCall src role : assoc_end_type end"

(*** Properties *************************************************************)

section{* Properties *}

inductive_cases NullLiteral_typing[elim]: "\<Gamma> \<turnstile> NullLiteral : \<tau>"
inductive_cases InvalidLiteral_typing[elim]: "\<Gamma> \<turnstile> InvalidLiteral : \<tau>"
inductive_cases BooleanLiteral_typing[elim]: "\<Gamma> \<turnstile> BooleanLiteral c : \<tau>"
inductive_cases RealLiteral_typing[elim]: "\<Gamma> \<turnstile> RealLiteral c : \<tau>"
inductive_cases IntegerLiteral_typing[elim]: "\<Gamma> \<turnstile> IntegerLiteral c : \<tau>"
inductive_cases UnlimitedNaturalLiteral_typing[elim]: "\<Gamma> \<turnstile> UnlimitedNaturalLiteral c : \<tau>"
inductive_cases StringLiteral_typing[elim]: "\<Gamma> \<turnstile> StringLiteral c : \<tau>"
inductive_cases EnumLiteral_typing[elim]: "\<Gamma> \<turnstile> EnumLiteral enm lit : \<tau>"
inductive_cases CollectionLiteral_typing[elim]: "\<Gamma> \<turnstile> CollectionLiteral k prts : \<tau>"
inductive_cases collection_parts_typing[elim]: "collection_parts_typing \<Gamma> prts \<tau>"
inductive_cases collection_parts_item_typing[elim]: "collection_parts_typing \<Gamma> (CollectionItem x # xs) \<tau>"
inductive_cases collection_parts_range_typing[elim]: "collection_parts_typing \<Gamma> (CollectionRange x y # xs) \<tau>"
inductive_cases TupleLiteral_typing[elim]: "\<Gamma> \<turnstile> TupleLiteral elems : \<tau>"
inductive_cases Let_typing[elim]: "\<Gamma> \<turnstile> Let v \<tau> init body : \<sigma>"
inductive_cases Var_typing[elim]: "\<Gamma> \<turnstile> Var v : \<tau>"
inductive_cases If_typing[elim]: "\<Gamma> \<turnstile> If a b c : \<tau>"
inductive_cases Call_typing[elim]: "\<Gamma> \<turnstile> Call a : \<tau>"
inductive_cases OclType_typing[elim]: "\<Gamma> \<turnstile> OclType a : \<tau>"
inductive_cases TypeOperationCall_typing[elim]: "\<Gamma> \<turnstile> TypeOperationCall op a \<sigma> : \<tau>"
inductive_cases UnaryOperationCall_typing[elim]: "\<Gamma> \<turnstile> UnaryOperationCall op a : \<tau>"
inductive_cases BinaryOperationCall_typing[elim]: "\<Gamma> \<turnstile> BinaryOperationCall op a b : \<tau>"
inductive_cases TernaryOperationCall_typing[elim]: "\<Gamma> \<turnstile> TernaryOperationCall op a b c : \<tau>"
inductive_cases iterator_typing[elim]: "iterator_typing \<Gamma> src its body \<tau> \<sigma> \<rho>"
inductive_cases Iterate_typing[elim]: "\<Gamma> \<turnstile> Iterate src its res res_t res_init body : \<tau>"
inductive_cases ClosureIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator ClosureIter src its body : \<tau>"
inductive_cases CollectIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator CollectIter src its body : \<tau>"
inductive_cases CollectNestedIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator CollectNestedIter src its body : \<tau>"
inductive_cases ExistsIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator ExistsIter src its body : \<tau>"
inductive_cases ForAllIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator ForAllIter src its body : \<tau>"
inductive_cases OneIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator OneIter src its body : \<tau>"
inductive_cases IsUniqueIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator IsUniqueIter src its body : \<tau>"
inductive_cases RejectIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator RejectIter src its body : \<tau>"
inductive_cases SelectIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator SelectIter src its body : \<tau>"
inductive_cases SortedByIterator_typing[elim]: "\<Gamma> \<turnstile> Iterator SortedByIter src its body : \<tau>"
inductive_cases AttributeCall_typing[elim]: "\<Gamma> \<turnstile> AttributeCall src prop : \<tau>"
inductive_cases AssociationEndCall_typing[elim]: "\<Gamma> \<turnstile> AssociationEndCall src role : \<tau>"

lemma strict_subcollection_det:
  "strict_subcollection \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   strict_subcollection \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: strict_subcollection.induct;
      simp add: strict_subcollection.simps)

lemma typeop_type_det:
  "typeop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   typeop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: typeop_type.induct;
      simp add: typeop_type.simps strict_subcollection_det)

lemma any_unop_type_det:
  "any_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   any_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: any_unop_type.induct;
      simp add: any_unop_type.simps)

lemma boolean_unop_type_det:
  "boolean_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   boolean_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: boolean_unop_type.induct;
      simp add: boolean_unop_type.simps)

lemma numeric_unop_type_det:
  "numeric_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   numeric_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: numeric_unop_type.induct;
      auto simp add: numeric_unop_type.simps)

lemma string_unop_type_det:
  "string_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   string_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: string_unop_type.induct;
      simp add: string_unop_type.simps)

lemma collection_of_det:
  "collection_of \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   collection_of \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: collection_of.induct;
      simp add: collection_of.simps)

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: update_element_type.induct;
      simp add: update_element_type.simps)

lemma collection_unop_type_det:
  "collection_unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   collection_unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  apply (induct rule: collection_unop_type.induct)
  apply (erule collection_unop_type.cases;
         auto simp add: collection_of_det
           update_element_type_det)+
  using collection_of_det update_element_type_det apply blast
  apply (erule collection_unop_type.cases; auto)+
  done 

lemma unop_type_det:
  "unop_type op \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   unop_type op \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: unop_type.induct;
      simp add: unop_type.simps any_unop_type_det
                boolean_unop_type_det numeric_unop_type_det
                string_unop_type_det collection_unop_type_det)

lemma suptype_binop_type_det:
  "suptype_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   suptype_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: suptype_binop_type.induct;
      auto simp add: suptype_binop_type.simps)

lemma boolean_binop_type_det:
  "boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   boolean_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: boolean_binop_type.induct;
      simp add: boolean_binop_type.simps)

lemma numeric_binop_type_det:
  "numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   numeric_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: numeric_binop_type.induct;
      auto simp add: numeric_binop_type.simps;
      drule_tac ?y="\<tau>" and ?z="\<sigma>" in sup_least; auto)

lemma string_binop_type_det:
  "string_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   string_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: string_binop_type.induct;
      simp add: string_binop_type.simps)

lemma collection_binop_type_det:
  "collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   collection_binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  apply (induct rule: collection_binop_type.induct;
         simp add: collection_binop_type.simps)
  using collection_of_det by blast

lemma binop_type_det:
  "binop_type op \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   binop_type op \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: binop_type.induct;
      simp add: binop_type.simps suptype_binop_type_det
                boolean_binop_type_det numeric_binop_type_det
                string_binop_type_det collection_binop_type_det)

lemma string_ternop_type_det:
  "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: string_ternop_type.induct;
      simp add: string_ternop_type.simps)

lemma collection_ternop_type_det:
  "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: collection_ternop_type.induct;
      simp add: collection_ternop_type.simps)

lemma ternop_type_det:
  "ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>1 \<Longrightarrow>
   ternop_type op \<tau> \<sigma> \<rho> \<upsilon>\<^sub>2 \<Longrightarrow> \<upsilon>\<^sub>1 = \<upsilon>\<^sub>2"
  by (induct rule: ternop_type.induct;
      simp add: ternop_type.simps string_ternop_type_det
                collection_ternop_type_det)

lemma to_unique_collection_det:
  "to_unique_collection \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (induct rule: to_unique_collection.induct;
      simp add: to_unique_collection.simps)

lemma to_ordered_collection_det:
  "to_ordered_collection \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (induct rule: to_ordered_collection.induct;
      simp add: to_ordered_collection.simps)

lemma class_of_det:
  "class_of \<tau> c \<Longrightarrow> class_of \<tau> d \<Longrightarrow> c = d"
  by (induct rule: class_of.induct;
      simp add: class_of.simps)

lemma
  typing_det: "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  collection_parts_typing_det:
    "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
     collection_parts_typing \<Gamma> prts \<sigma> \<Longrightarrow> \<tau> = \<sigma>" and
  iterator_typing_det:
    "iterator_typing \<Gamma> src its body \<tau>\<^sub>1 \<sigma>\<^sub>1 \<rho>\<^sub>1 \<Longrightarrow>
     iterator_typing \<Gamma> src its body \<tau>\<^sub>2 \<sigma>\<^sub>2 \<rho>\<^sub>2 \<Longrightarrow>
     \<tau>\<^sub>1 = \<tau>\<^sub>2 \<and> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> \<rho>\<^sub>1 = \<rho>\<^sub>2"
proof (induct \<Gamma> expr \<tau> and \<Gamma> prts \<tau> and \<Gamma> src its body \<tau>\<^sub>1 \<sigma>\<^sub>1 \<rho>\<^sub>1
         arbitrary: \<sigma> and \<sigma> and \<tau>\<^sub>2 \<sigma>\<^sub>2 \<rho>\<^sub>2
         rule: typing_collection_parts_typing_iterator_typing.inducts)
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
  case (TupleLiteralT \<Gamma> elems) thus ?case by auto
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
  case (OclTypeT \<Gamma> a \<tau>) thus ?case by blast
next
  case (TypeOperationCallT \<Gamma> a \<tau> op \<sigma> \<rho>) thus ?case
    by (metis TypeOperationCall_typing typeop_type_det)
next
  case (UnaryOperationCallT \<Gamma> a \<tau> op \<sigma>) thus ?case
    by (metis UnaryOperationCall_typing unop_type_det)
next
  case (BinaryOperationCallT \<Gamma> a \<tau> b \<sigma> op \<rho>) thus ?case
    by (metis BinaryOperationCall_typing binop_type_det)
next
  case (TernaryOperationCallT \<Gamma> a \<tau> b \<sigma> c \<rho> op \<upsilon>) thus ?case
    by (metis TernaryOperationCall_typing ternop_type_det)
next
  case (IteratorT \<Gamma> \<M> src \<tau> \<sigma> its body \<rho>) thus ?case
    apply (insert IteratorT.prems)
    apply (erule iterator_typing)
    using IteratorT.hyps(2) IteratorT.hyps(3)
          IteratorT.hyps(5) collection_of_det
    by fastforce
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
          to_unique_collection_det
    by blast
next
  case (CollectIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho> \<upsilon>) thus ?case
    apply (insert CollectIteratorT.prems)
    apply (erule CollectIterator_typing)
    using CollectIteratorT.hyps(2) CollectIteratorT.hyps(4)
          update_element_type_det
    by blast
next
  case (CollectNestedIteratorT \<Gamma> \<M> src its body \<tau> \<sigma> \<rho> \<upsilon>) thus ?case
    apply (insert CollectNestedIteratorT.prems)
    apply (erule CollectNestedIterator_typing)
    using CollectNestedIteratorT.hyps(2) CollectNestedIteratorT.hyps(4)
          update_element_type_det
    by blast
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
          to_ordered_collection_det
    by blast
next
  case (AttributeCallT \<M> attrs assocs \<Gamma> src \<tau> cls cls_attrs "prop" \<sigma>) thus ?case
    apply (insert AttributeCallT.prems)
    apply (erule AttributeCall_typing)
    using AttributeCallT.hyps(1) AttributeCallT.hyps(3)
          AttributeCallT.hyps(4) AttributeCallT.hyps(5)
          AttributeCallT.hyps(6) class_of_det
    by fastforce
next
  case (AssociationEndCallT \<M> attrs assocs \<Gamma> src \<tau> cls role "end") thus ?case
    apply (insert AssociationEndCallT.prems)
    apply (erule AssociationEndCall_typing)
    using AssociationEndCallT.hyps(1) AssociationEndCallT.hyps(3)
          AssociationEndCallT.hyps(4) AssociationEndCallT.hyps(5)
          class_of_det
    by fastforce
qed


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


values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Iterate (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5)]) [''x'']
      ''acc'' Real[?] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (Var ''acc'')): x}"


values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' (Sequence String[?]) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (Iterator AnyIter (Var ''x'') [''it'']
    (BinaryOperationCall EqualOp (Var ''it'') (StringLiteral ''test''))): x}"


values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' (Sequence String[?]) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (Iterator ClosureIter (Var ''x'') [''it'']
    (Var ''it'')): x}"

values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' (Sequence String[?]) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (Iterator ClosureIter (Var ''x'') [''it'']
    (Var ''x'')): x}"

values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' (Sequence String[?]) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (Iterator ClosureIter (Var ''x'') [''it'']
    (IntegerLiteral 1)): x}"


values "{x :: classes1 type. (Map.empty :: classes1 type env, model1) \<turnstile>
  (IntegerLiteral 5) : x}"

values "{x :: classes1 type. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Integer[1] (IntegerLiteral 5)
    (Var ''x'') : x}"

values "{x :: classes1 type. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Integer[1] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (IntegerLiteral 7)) : x}"
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
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5)]) [''x'']
      ''acc'' Integer[?] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (Var ''acc'')): x}"

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

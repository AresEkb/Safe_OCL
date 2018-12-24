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

code_pred [show_modes] typeop_type .

values "{x. typeop_type SelectByKindOp (Set Real[?] :: classes1 type) Integer[1] x}"

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

code_pred [show_modes] suptype_binop_type .

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

code_pred [show_modes] collection_binop_type .

values "{x. collection_binop_type ProductOp
    (Set Boolean[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_binop_type IncludesOp
    (Set Integer[1] :: classes1 type) (Integer[?] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_binop_type IncludesAllOp
    (Set Real[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"

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

code_pred [show_modes] typeop_type .
code_pred [show_modes] unop_type .
code_pred [show_modes] binop_type .
code_pred [show_modes] ternop_type .

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
inductive_cases TupleLiteral_typing[elim]: "\<Gamma> \<turnstile> TupleLiteral elems : \<tau>"
inductive_cases Let_typing[elim]: "\<Gamma> \<turnstile> Let v \<tau> init body : \<sigma>"
inductive_cases Var_typing[elim]: "\<Gamma> \<turnstile> Var v : \<tau>"
inductive_cases If_typing[elim]: "\<Gamma> \<turnstile> If a b c : \<tau>"
inductive_cases Call_typing[elim]: "\<Gamma> \<turnstile> Call a : \<tau>"
inductive_cases Call_OclType_typing[elim]: "\<Gamma> \<turnstile> Call (OclType a) : \<tau>"

inductive_cases collection_parts_typing[elim]: "collection_parts_typing \<Gamma> prts \<tau>"

lemma collection_parts_typing_det:
  "collection_parts_typing \<Gamma> prts \<tau> \<Longrightarrow>
   collection_parts_typing \<Gamma> prts \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  apply (induct prts, auto)
  apply (
         erule typing_collection_parts_typing_iterator_typing.inducts(2), auto)
  sorry
(*  apply (induct arbitrary: prts
         rule: typing_collection_parts_typing_iterator_typing.inducts(2), auto)*)
(*  using collection_parts_typing.cases apply blast*)


lemma literal_typing_det:
  "\<Gamma> \<turnstile> Literal expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Literal expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  apply (induct expr, auto)
  by (erule CollectionLiteral_typing;
      erule CollectionLiteral_typing;
      auto simp add: collection_parts_typing_det)

term Call

thm Call_OclType_typing OclTypeT

lemma OclType_typing_det:
  "\<Gamma> \<turnstile> OclType expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> OclType expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  apply (erule Call_OclType_typing)

  thm expr.simps

  thm list_all2_conv_all_nth listrel_iff_nth

  term listrel

lemma set_listrel_eq_list_all2: 
  "listrel {(x, y). r x y} = {(xs, ys). list_all2 r xs ys}"
  using list_all2_conv_all_nth listrel_iff_nth by fastforce

thm listrel_rtrancl_eq_rtrancl_listrel1

term listrel1

lemma listrel_tclosure_1: "(listrel r)\<^sup>* \<subseteq> listrel (r\<^sup>*)"
  by (simp add: listrel_rtrancl_eq_rtrancl_listrel1 
      listrel_subset_rtrancl_listrel1 rtrancl_subset_rtrancl)

lemma listrel_tclosure_2: "refl r \<Longrightarrow> listrel (r\<^sup>*) \<subseteq> (listrel r)\<^sup>*"
  by (simp add: listrel1_subset_listrel listrel_rtrancl_eq_rtrancl_listrel1 
      rtrancl_mono)

context includes lifting_syntax
begin

lemma listrel_list_all2_transfer [transfer_rule]:
  "((=) ===> (=) ===> (=) ===> (=)) 
  (\<lambda>r xs ys. (xs, ys) \<in> listrel {(x, y). r x y}) list_all2"
  unfolding rel_fun_def using set_listrel_eq_list_all2 listrel_iff_nth by blast

end

lemma list_all2_rtrancl_1:
  "(list_all2 r)\<^sup>*\<^sup>* xs ys \<Longrightarrow> list_all2 r\<^sup>*\<^sup>* xs ys"
proof(transfer)
  fix r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fix xs :: "'a list"
  fix ys:: "'a list"
  assume "(\<lambda>xs ys. (xs, ys) \<in> listrel {(x, y). r x y})\<^sup>*\<^sup>* xs ys"
  then have "(xs, ys) \<in> (listrel {(x, y). r x y})\<^sup>*"
    unfolding rtranclp_def rtrancl_def by auto  
  then have "(xs, ys) \<in> listrel ({(x, y). r x y}\<^sup>*)" 
    using listrel_tclosure_1 by auto
  then show "(xs, ys) \<in> listrel {(x, y). r\<^sup>*\<^sup>* x y}"
    unfolding rtranclp_def rtrancl_def by auto  
qed

lemma list_all2_rtrancl_2:
  "reflp r \<Longrightarrow> list_all2 r\<^sup>*\<^sup>* xs ys \<Longrightarrow> (list_all2 r)\<^sup>*\<^sup>* xs ys"
proof(transfer)
  fix r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fix xs :: "'a list"
  fix ys :: "'a list"
  assume as_reflp: "reflp r" 
  assume p_in_lr: "(xs, ys) \<in> listrel {(x, y). r\<^sup>*\<^sup>* x y}"
  from as_reflp have refl: "refl {(x, y). r x y}" 
    using reflp_refl_eq by fastforce
  from p_in_lr have "(xs, ys) \<in> listrel ({(x, y). r x y}\<^sup>*)"
    unfolding rtranclp_def rtrancl_def by auto
  with refl have "(xs, ys) \<in> (listrel {(x, y). r x y})\<^sup>*"
    using listrel_tclosure_2 by auto
  then show "(\<lambda>xs ys. (xs, ys) \<in> listrel {(x, y). r x y})\<^sup>*\<^sup>* xs ys" 
    unfolding rtranclp_def rtrancl_def by auto
qed

end






datatype t1 = A | B t2
     and t2 = C | D t1

inductive rel1 and rel2 where
  "rel1 A 0"
| "rel2 x n \<Longrightarrow>
   rel1 (B x) n"
| "rel2 C 1"
| "rel1 x n \<Longrightarrow>
   rel2 (D x) n"

print_theorems

lemma rel1_det:
  "rel1 x n \<Longrightarrow> rel1 x m \<Longrightarrow> n = m"
  apply (induct rule: rel1_rel2.inducts(1), auto)
  apply (simp add: rel1.simps)
  apply (simp add: rel1.simps)

fun rel1_fun and rel2_fun where
  "rel1_fun A = 0"
| "rel1_fun (B x) = rel2_fun x"
| "rel2_fun C = 1"
| "rel2_fun (D x) = rel1_fun x"

print_theorems

lemma q:
  "rel1_fun x = n \<Longrightarrow> rel1 x n"
  apply (erule rel1_fun.elims, auto)
  apply (simp add: rel1_rel2.intros(1))


lemma call_typing_det:
  "\<Gamma> \<turnstile> Call expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Call expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  apply (induct expr)
(*  apply (erule Call_typing, auto)
  apply (erule Call_OclType_typing)*)

lemma typing_det':
  "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  apply (induct arbitrary: \<Gamma> \<tau> \<sigma> rule: typing_collection_parts_typing_iterator_typing.induct)

lemma typing_det:
  "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  apply (induct expr arbitrary: \<Gamma> \<tau> \<sigma>, auto)
      apply (simp add: literal_typing_det)
  apply (erule Let_typing; erule Let_typing; auto)
  apply fastforce
  apply fastforce
(*
  apply (induct rule: typing_collection_parts_typing_iterator_typing.inducts(1),
         auto simp add: collection_parts_typing_det)
*)

  apply (erule If_typing, auto)




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

(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* OCL Typing Rules *}
theory OCL_Typing
  imports OCL_Syntax OCL_Types Object_Model "HOL-Library.Transitive_Closure_Table"
begin

inductive is_collection_of where
  "is_collection_of (Collection t) t"
| "is_collection_of (Set t) t"
| "is_collection_of (OrderedSet t) t"
| "is_collection_of (Bag t) t"
| "is_collection_of (Sequence t) t"

(*** Standard Library Operations Typing *************************************)

subsection{* Standard Library Operations Typing *}

inductive typeop_type where
  "t1 \<le> OclAny[?] \<Longrightarrow>
   typeop_type OclAsTypeOp t1 t2 t2"
| "t1 \<le> OclAny[?] \<Longrightarrow>
   typeop_type OclIsTypeOfOp t1 t2 Boolean[1]"
| "t1 \<le> OclAny[?] \<Longrightarrow>
   typeop_type OclIsKindOfOp t1 t2 Boolean[1]"
| "is_collection_of t1 _ \<Longrightarrow>
   typeop_type SelectByKindOp t1 t2 t1"
| "is_collection_of t1 _ \<Longrightarrow>
   typeop_type SelectByTypeOp t1 t2 t1"

inductive any_unop_type where
  "t \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclAsSetOp t (Set t)"
| "t \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsNewOp t Boolean[1]"
| "t \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsUndefinedOp t Boolean[1]"
| "t \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclIsInvalidOp t Boolean[1]"
| "t \<le> OclAny[?] \<Longrightarrow>
   any_unop_type OclLocaleOp t String[1]"

inductive any_binop_type where
  "\<lbrakk>t1 \<le> OclAny[?]; t2 \<le> OclAny[?]\<rbrakk> \<Longrightarrow>
   any_binop_type any_binop.EqualOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<le> OclAny[?]; t2 \<le> OclAny[?]\<rbrakk> \<Longrightarrow>
   any_binop_type any_binop.NotEqualOp t1 t2 Boolean[1]"

inductive boolean_unop_type where
  "t \<le> Boolean[?] \<Longrightarrow>
   boolean_unop_type NotOp t t"
| "t \<le> Boolean[?] \<Longrightarrow>
   boolean_unop_type boolean_unop.ToStringOp t String[1]"

inductive boolean_binop_type where
  "\<lbrakk>t1 \<squnion> t2 = t; t \<le> Boolean[?]\<rbrakk> \<Longrightarrow>
   boolean_binop_type (op :: boolean_binop) t1 t2 t"

inductive numeric_unop_type where
  "\<lbrakk>Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type UMinusOp t Real[1]"
| "\<lbrakk>Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type UMinusOp t Integer[1]"
| "\<lbrakk>t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type UMinusOp t UnlimitedNatural[1]"

| "\<lbrakk>Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type AbsOp t Real[1]"
| "\<lbrakk>t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type AbsOp t Integer[1]"

| "\<lbrakk>t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type FloorOp t Real[1]"
| "\<lbrakk>t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type RoundOp t Real[1]"

| "\<lbrakk>t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type numeric_unop.ToStringOp t String[1]"

| "\<lbrakk>t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_unop_type numeric_unop.ToIntegerOp t Integer[1]"

inductive numeric_binop_type where
  "\<lbrakk>t1 \<squnion> t2 = t; Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type PlusOp t1 t2 Real[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type PlusOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type PlusOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type MinusOp t1 t2 Real[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type MinusOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type MinusOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type MultOp t1 t2 Real[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type MultOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type MultOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type DivideOp t1 t2 Real[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type DivOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type DivOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type ModOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type ModOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.MaxOp t1 t2 Real[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.MaxOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.MaxOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; Real[1] \<le> t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.MinOp t1 t2 Real[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; Integer[1] \<le> t; t \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.MinOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> UnlimitedNatural[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.MinOp t1 t2 UnlimitedNatural[1]"

| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.LessOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.LessEqOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> Real[?]\<rbrakk> \<Longrightarrow>
   numeric_binop_type numeric_binop.GreaterEqOp t1 t2 Boolean[1]"

inductive string_unop_type where
  "t \<le> String[?] \<Longrightarrow>
   string_unop_type string_unop.SizeOp t Integer[1]"
| "t \<le> String[?] \<Longrightarrow>
   string_unop_type CharactersOp t (Sequence String[1])"
| "t \<le> String[?] \<Longrightarrow>
   string_unop_type ToUpperCaseOp t String[1]"
| "t \<le> String[?] \<Longrightarrow>
   string_unop_type ToLowerCaseOp t String[1]"
| "t \<le> String[?] \<Longrightarrow>
   string_unop_type ToBooleanOp t Boolean[1]"
| "t \<le> String[?] \<Longrightarrow>
   string_unop_type ToIntegerOp t Integer[1]"
| "t \<le> String[?] \<Longrightarrow>
   string_unop_type ToRealOp t Real[1]"

inductive string_binop_type where
  "\<lbrakk>t1 \<squnion> t2 = t; t \<le> String[?]\<rbrakk> \<Longrightarrow>
   string_binop_type ConcatOp t1 t2 String[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> String[?]\<rbrakk> \<Longrightarrow>
   string_binop_type EqualsIgnoreCaseOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> String[?]\<rbrakk> \<Longrightarrow>
   string_binop_type LessOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> String[?]\<rbrakk> \<Longrightarrow>
   string_binop_type LessEqOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> String[?]\<rbrakk> \<Longrightarrow>
   string_binop_type GreaterOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<squnion> t2 = t; t \<le> String[?]\<rbrakk> \<Longrightarrow>
   string_binop_type GreaterEqOp t1 t2 Boolean[1]"
| "\<lbrakk>t1 \<le> String[?]; t2 \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   string_binop_type IndexOfOp t1 t2 Integer[1]"
| "\<lbrakk>t1 \<le> String[?]; t2 \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   string_binop_type AtOp t1 t2 String[1]"

inductive string_ternop_type where
  "\<lbrakk>t1 \<le> String[?]; t2 \<le> Integer[?]; t3 \<le> Integer[?]\<rbrakk> \<Longrightarrow>
   string_ternop_type SubstringOp t1 t2 t3 String[1]"

inductive collection_unop_type where
  "is_collection_of t _ \<Longrightarrow>
   collection_unop_type collection_unop.SizeOp t Integer[1]"
| "is_collection_of t _ \<Longrightarrow>
   collection_unop_type IsEmptyOp t Boolean[1]"
| "is_collection_of t _ \<Longrightarrow>
   collection_unop_type NotEmptyOp t Boolean[1]"
| "\<lbrakk>is_collection_of t t1; UnlimitedNatural[1] \<le> t1; t1 \<le> Real[?]\<rbrakk> \<Longrightarrow>
   collection_unop_type MaxOp t t1"
| "\<lbrakk>is_collection_of t t1; UnlimitedNatural[1] \<le> t1; t1 \<le> Real[?]\<rbrakk> \<Longrightarrow>
   collection_unop_type MinOp t t1"
| "\<lbrakk>is_collection_of t t1; UnlimitedNatural[1] \<le> t1; t1 \<le> Real[?]\<rbrakk> \<Longrightarrow>
   collection_unop_type SumOp t t1"
| "\<lbrakk>is_collection_of t t1\<rbrakk> \<Longrightarrow>
   collection_unop_type AsSetOp t (Set t1)"
| "\<lbrakk>is_collection_of t t1\<rbrakk> \<Longrightarrow>
   collection_unop_type AsOrderedSetOp t (OrderedSet t1)"
| "\<lbrakk>is_collection_of t t1\<rbrakk> \<Longrightarrow>
   collection_unop_type AsBagOp t (Bag t1)"
| "\<lbrakk>is_collection_of t t1\<rbrakk> \<Longrightarrow>
   collection_unop_type AsSequenceOp t (Sequence t1)"
| "\<lbrakk>is_collection_of t t1; t1 \<le> OclAny[?]\<rbrakk> \<Longrightarrow>
   collection_unop_type FlattenOp t t"
| "\<lbrakk>is_collection_of t t1;
    collection_unop_type FlattenOp t1 t2;
    is_collection_of t2 t3\<rbrakk> \<Longrightarrow>
   collection_unop_type FlattenOp t (Collection t3)"

code_pred [show_modes] collection_unop_type .

values "{x. collection_unop_type FlattenOp
    (Set Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type FlattenOp
    (Sequence (Set Integer[?] :: classes1 type)) (x :: classes1 type)}"
values "{x. collection_unop_type FlattenOp
    (Sequence (Set (Bag Integer[?] :: classes1 type))) (x :: classes1 type)}"
values "{x. collection_unop_type collection_unop.MaxOp
    (Collection Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type collection_unop.MaxOp
    (Set Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type collection_unop.SizeOp
    (Integer[1] :: classes1 type) (x :: classes1 type)}"
values "{x. collection_unop_type collection_unop.SizeOp
    (Set Boolean[1] :: classes1 type) (x :: classes1 type)}"

inductive collection_binop_type where
  "\<lbrakk>is_collection_of t1 _; is_collection_of t2 _\<rbrakk>\<Longrightarrow>
   collection_binop_type collection_binop.EqualOp t1 t2 Boolean[1]"
| "\<lbrakk>is_collection_of t1 _; is_collection_of t2 _\<rbrakk>\<Longrightarrow>
   collection_binop_type collection_binop.NotEqualOp t1 t2 Boolean[1]"
| "\<lbrakk>is_collection_of t1 t2\<rbrakk>\<Longrightarrow>
   collection_binop_type IncludesOp t1 t2 Boolean[1]"
| "\<lbrakk>is_collection_of t1 t2\<rbrakk>\<Longrightarrow>
   collection_binop_type ExcludesOp t1 t2 Boolean[1]"
| "\<lbrakk>is_collection_of t1 t2\<rbrakk>\<Longrightarrow>
   collection_binop_type CountOp t1 t2 Integer[1]"
| "\<lbrakk>is_collection_of t1 t3; is_collection_of t2 t3\<rbrakk>\<Longrightarrow>
   collection_binop_type IncludesAllOp t1 t2 Boolean[1]"
| "\<lbrakk>is_collection_of t1 t3; is_collection_of t2 t3\<rbrakk>\<Longrightarrow>
   collection_binop_type ExcludesAllOp t1 t2 Boolean[1]"
| "\<lbrakk>is_collection_of t1 t3; is_collection_of t2 t4\<rbrakk>\<Longrightarrow>
   collection_binop_type ProductOp t1 t2 (Tuple (fmap_of_list [(0, t3), (1, t4)]))"

code_pred [show_modes] collection_binop_type .

values "{x. collection_binop_type ProductOp
    (Set Boolean[1] :: classes1 type) (Sequence Integer[?] :: classes1 type) (x :: classes1 type)}"

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
  "any_binop_type op t1 t2 t \<Longrightarrow>
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
   ternop_type op t1 t2 t3 t"

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
    and collection_parts_type where
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

values "{x. (Map.empty :: classes1 type env, model1) \<turnstile>
  Let ''x'' Integer[1] (IntegerLiteral 5)
    (BinaryOperationCall PlusOp (Var ''x'') (IntegerLiteral 7)): x}"
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

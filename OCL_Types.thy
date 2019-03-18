(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Types\<close>
theory OCL_Types
  imports Errorable Tuple "HOL-Library.Phantom_Type"
begin


typedef 'a nullable ("_\<^sub>\<box>" [21] 21) = "UNIV :: 'a option set" ..

definition nullable :: "'a \<Rightarrow> 'a nullable" ("_\<^sub>\<box>" [1000] 1000) where
  "nullable x = Abs_nullable (Some x)"

class null =
  fixes null :: 'a ("\<box>")

instantiation nullable :: (type) null
begin
definition "\<box> \<equiv> Abs_nullable None"
instance ..
end

free_constructors case_nullable for
  nullable
| "\<box> :: 'a nullable"
  unfolding nullable_def null_nullable_def
  apply (metis Abs_nullable_cases not_None_eq)
  apply (metis Abs_nullable_inverse UNIV_I option.inject)
  by (simp add: Abs_nullable_inject)

copy_bnf 'a nullable



(*** Definition *************************************************************)

section \<open>Definition\<close>

text \<open>
  Types are parameterized over classes.\<close>

type_synonym 'a enum = "('a, String.literal) phantom"
type_synonym elit = String.literal

type_synonym telem = String.literal
(*
datatype 'a extended = Original 'a | Extended 'a

datatype 'a type =
  OclAny
| OclVoid
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'a ("\<langle>_\<rangle>\<^sub>\<T>" [0] 1000)
| Enum "'a enum"
| Collection "'a type extended extended"
| Set "'a type extended extended"
| OrderedSet "'a type extended extended"
| Bag "'a type extended extended"
| Sequence "'a type extended extended"
| Tuple "telem \<rightharpoonup>\<^sub>f 'a type extended extended"
(*
datatype ('a, 'c) type =
  OclAny
| OclVoid
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'c ("\<langle>_\<rangle>\<^sub>\<T>" [0] 1000)
| Enum "'c enum"
| Collection 'a
| Set 'a
| OrderedSet 'a
| Bag 'a
| Sequence 'a
| Tuple "telem \<rightharpoonup>\<^sub>f 'a"
*)
(*
datatype 'a nullable_type =
  Required 'a
| Optional 'a

datatype 'a errorable_type =
  ErrorFree 'a
| Errorable 'a
*)

instantiation extended :: (order) order
begin

fun less_extended where
  "Original x < Original y = (x < y)"
| "Original x < Extended y = (x \<le> y)"
| "Extended x < Original y = False"
| "Extended x < Extended y = (x < y)"

fun less_eq_extended where
  "Original x \<le> Original y = (x \<le> y)"
| "Original x \<le> Extended y = (x \<le> y)"
| "Extended x \<le> Original y = False"
| "Extended x \<le> Extended y = (x \<le> y)"

lemma extended_less_le_not_le:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  for x y :: "'a extended"
proof
  show "x < y \<Longrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (erule less_extended.elims; auto)
  have "x \<le> y \<Longrightarrow> \<not> y \<le> x \<Longrightarrow> x < y"
    by (erule less_eq_extended.elims; auto)
  thus "x \<le> y \<and> \<not> y \<le> x \<Longrightarrow> x < y"
    by simp
qed

lemma extended_order_refl:
  "x \<le> x"
  for x :: "'a extended"
  by (cases x; auto)

lemma extended_order_trans:
  "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  for x y z :: "'a extended"
  by (erule less_eq_extended.elims; auto)+

lemma extended_antisym:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  for x y :: "'a extended"
  by (erule less_eq_extended.elims; auto)+

instance
  apply standard
  apply (simp add: extended_less_le_not_le)
  apply (simp add: extended_order_refl)
  apply (drule extended_order_trans; auto)
  by (simp add: extended_antisym)

end
(*
type_synonym ('a, 'c) nullable_type = "('a, 'c) type extended"
type_synonym 'c errorable_type = "('c itself, 'c) nullable_type extended"

term "Extended Integer :: ('a, 'c) nullable_type"
term "Extended (Extended Integer) :: 'c errorable_type"
term "Extended (Extended (Extended Integer)) :: 'c errorable_type"
*)

type_synonym 'c errorable_type = "('c itself, 'c) type extended extended"

(*
definition RequiredErrorFree :: "('c errorable_type, 'c) type \<Rightarrow> 'c errorable_type" where
  "RequiredErrorFree \<equiv> Original \<circ> Original"
definition RequiredErrorFree :: "('a, 'c) type \<Rightarrow> ('a, 'c) type extended extended" where
  "RequiredErrorFree \<equiv> Original \<circ> Original"
*)

definition "RequiredErrorFree \<equiv> Original \<circ> Original"
definition "RequiredErrorable \<equiv> Extended \<circ> Original"
definition "OptionalErrorFree \<equiv> Original \<circ> Extended"
definition "OptionalErrorable \<equiv> Extended \<circ> Extended"

term "RequiredErrorFree Integer :: 'a errorable_type"
term "RequiredErrorable Integer"

(*
inductive subtype :: "('a::order, 'c::order) type \<Rightarrow> ('a, 'c) type \<Rightarrow> bool" (infix "\<sqsubset>" 65) where

\<comment> \<open>Basic Types\<close>

  "OclVoid \<sqsubset> Boolean"
| "OclVoid \<sqsubset> UnlimitedNatural"
| "OclVoid \<sqsubset> String"
| "OclVoid \<sqsubset> \<langle>\<C>\<rangle>\<^sub>\<T>"
| "OclVoid \<sqsubset> Enum \<E>"

| "UnlimitedNatural \<sqsubset> Integer"
| "Integer \<sqsubset> Real"
| "\<C> < \<D> \<Longrightarrow> \<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset> \<langle>\<D>\<rangle>\<^sub>\<T>"

| "Boolean \<sqsubset> OclAny"
| "Real \<sqsubset> OclAny"
| "String \<sqsubset> OclAny"
| "\<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset> OclAny"
| "Enum \<E> \<sqsubset> OclAny"

\<comment> \<open>Collection Types\<close>

| "OclVoid \<sqsubset> Set OclVoid"
| "OclVoid \<sqsubset> OrderedSet OclVoid"
| "OclVoid \<sqsubset> Bag OclVoid"
| "OclVoid \<sqsubset> Sequence OclVoid"

| "\<tau> < \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"

| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"

| "Collection OclAny \<sqsubset> OclAny"

\<comment> \<open>Tuple Types\<close>

| "OclVoid \<sqsubset> Tuple \<pi>"
| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> < \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> OclAny"
*)


class type_hierarchy = order +
  fixes subtype :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

notation
  subtype ("'(\<sqsubset>')") and
  subtype ("(_/ \<sqsubset> _)" [51, 51] 50)

inductive extended_subtype (infix "\<sqsubset>\<^sub>E" 51) where
  "x \<sqsubset> y \<Longrightarrow> Original x \<sqsubset>\<^sub>E Original y"
| "x \<sqsubset> y \<Longrightarrow> Extended x \<sqsubset>\<^sub>E Extended y"
| "Original x \<sqsubset>\<^sub>E Extended x"

code_pred [show_modes] extended_subtype .

instantiation extended :: (type_hierarchy) type_hierarchy
begin

abbreviation "(\<sqsubset>) \<equiv> (\<sqsubset>\<^sub>E)"

instance ..

end

inductive type_subtype :: "'a :: type_hierarchy type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>T" 51) where

\<comment> \<open>Basic Types\<close>

  "OclVoid \<sqsubset>\<^sub>T Boolean"
| "OclVoid \<sqsubset>\<^sub>T UnlimitedNatural"
| "OclVoid \<sqsubset>\<^sub>T String"
| "OclVoid \<sqsubset>\<^sub>T \<langle>\<C>\<rangle>\<^sub>\<T>"
| "OclVoid \<sqsubset>\<^sub>T Enum \<E>"

| "UnlimitedNatural \<sqsubset>\<^sub>T Integer"
| "Integer \<sqsubset>\<^sub>T Real"
| "\<C> < \<D> \<Longrightarrow> \<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset>\<^sub>T \<langle>\<D>\<rangle>\<^sub>\<T>"

| "Boolean \<sqsubset>\<^sub>T OclAny"
| "Real \<sqsubset>\<^sub>T OclAny"
| "String \<sqsubset>\<^sub>T OclAny"
| "\<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset>\<^sub>T OclAny"
| "Enum \<E> \<sqsubset>\<^sub>T OclAny"

\<comment> \<open>Collection Types\<close>

| "OclVoid \<sqsubset>\<^sub>T Set (Original (Original OclVoid))"
| "OclVoid \<sqsubset>\<^sub>T OrderedSet (Original (Original OclVoid))"
| "OclVoid \<sqsubset>\<^sub>T Bag (Original (Original OclVoid))"
| "OclVoid \<sqsubset>\<^sub>T Sequence (Original (Original OclVoid))"

| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset>\<^sub>T Collection \<sigma>"
(*| "\<tau> < \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"

| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"

| "Collection (Extended (Extended OclAny)) \<sqsubset> OclAny"

\<comment> \<open>Tuple Types\<close>

| "OclVoid \<sqsubset> Tuple \<pi>"
| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> < \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> OclAny"

code_pred [show_modes] subtype_type2 .
*)

instantiation type :: (type_hierarchy) type_hierarchy
begin


end

instantiation type :: (order, order) order
begin

definition "(<) \<equiv> "

end
*)

datatype (plugins del: size) 'a type =
  OclAny
| OclVoid
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'a ("\<langle>_\<rangle>\<^sub>\<T>" [0] 1000)
| Enum "'a enum"
| Collection "'a type\<^sub>N\<^sub>E"
| Set "'a type\<^sub>N\<^sub>E"
| OrderedSet "'a type\<^sub>N\<^sub>E"
| Bag "'a type\<^sub>N\<^sub>E"
| Sequence "'a type\<^sub>N\<^sub>E"
| Tuple "telem \<rightharpoonup>\<^sub>f 'a type\<^sub>N\<^sub>E"
and 'a type\<^sub>N =
  Required "'a type"
| Optional "'a type"
and 'a type\<^sub>N\<^sub>E =
  ErrorFree "'a type\<^sub>N"
| Errorable "'a type\<^sub>N"


abbreviation Required_ErrorFree ("_[1]" [1000] 1000) where
  "Required_ErrorFree \<equiv> ErrorFree \<circ> Required"

abbreviation Optional_ErrorFree ("_[?]" [1000] 1000) where
  "Optional_ErrorFree \<equiv> ErrorFree \<circ> Optional"

abbreviation Required_Errorable ("_[1!]" [1000] 1000) where
  "Required_Errorable \<equiv> Errorable \<circ> Required"

abbreviation Optional_Errorable ("_[?!]" [1000] 1000) where
  "Optional_Errorable \<equiv> Errorable \<circ> Optional"


text \<open>
  We define the @{text OclInvalid} type separately, because we
  do not need types like @{text "Set(OclInvalid)"} in the theory.
  The @{text "OclVoid[1]"} type is not equal to @{text OclInvalid}.
  For example, @{text "Set(OclVoid[1])"} could theoretically be
  a valid type of the following expression:\<close>

text \<open>
\<^verbatim>\<open>Set{null}->excluding(null)\<close>\<close>

definition "OclInvalid :: 'a type\<^sub>\<bottom> \<equiv> \<bottom>"

instantiation type :: (type) size
begin

primrec size_type :: "'a type \<Rightarrow> nat" where
  "size_type OclSuper = 0"
| "size_type (Required \<tau>) = 0"
| "size_type (Optional \<tau>) = 0"
| "size_type (Collection \<tau>) = Suc (size_type \<tau>)"
| "size_type (Set \<tau>) = Suc (size_type \<tau>)"
| "size_type (OrderedSet \<tau>) = Suc (size_type \<tau>)"
| "size_type (Bag \<tau>) = Suc (size_type \<tau>)"
| "size_type (Sequence \<tau>) = Suc (size_type \<tau>)"
| "size_type (Tuple \<pi>) = Suc (ffold tcf 0 (fset_of_fmap (fmmap size_type \<pi>)))"

instance ..

end

inductive subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<sqsubset>" 65)
  and nullable_subtype :: "'a type\<^sub>N \<Rightarrow> 'a type\<^sub>N \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>N" 65)
  and errorable_subtype :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>N\<^sub>E" 65) where

\<comment> \<open>Basic Types\<close>

  "OclVoid \<sqsubset> Boolean"
| "OclVoid \<sqsubset> UnlimitedNatural"
| "OclVoid \<sqsubset> String"
| "OclVoid \<sqsubset> \<langle>\<C>\<rangle>\<^sub>\<T>"
| "OclVoid \<sqsubset> Enum \<E>"

| "UnlimitedNatural \<sqsubset> Integer"
| "Integer \<sqsubset> Real"
| "\<C> < \<D> \<Longrightarrow> \<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset> \<langle>\<D>\<rangle>\<^sub>\<T>"

| "Boolean \<sqsubset> OclAny"
| "Real \<sqsubset> OclAny"
| "String \<sqsubset> OclAny"
| "\<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset> OclAny"
| "Enum \<E> \<sqsubset> OclAny"

\<comment> \<open>Collection Types\<close>

| "OclVoid \<sqsubset> Set OclVoid[1]"
| "OclVoid \<sqsubset> OrderedSet OclVoid[1]"
| "OclVoid \<sqsubset> Bag OclVoid[1]"
| "OclVoid \<sqsubset> Sequence OclVoid[1]"

| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"

| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"

| "Collection OclAny[?!] \<sqsubset> OclAny"

\<comment> \<open>Tuple Types\<close>

| "OclVoid \<sqsubset> Tuple \<pi>"
| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> OclAny"

\<comment> \<open>Nullable Types\<close>

| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Required \<tau> \<sqsubset>\<^sub>N Required \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Optional \<tau> \<sqsubset>\<^sub>N Optional \<sigma>"
| "Required \<tau> \<sqsubset>\<^sub>N Optional \<tau>"

\<comment> \<open>Errorable Types\<close>

| "\<tau> \<sqsubset>\<^sub>N \<sigma> \<Longrightarrow> ErrorFree \<tau> \<sqsubset>\<^sub>N\<^sub>E ErrorFree \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N \<sigma> \<Longrightarrow> Errorable \<tau> \<sqsubset>\<^sub>N\<^sub>E Errorable \<sigma>"
| "ErrorFree \<tau> \<sqsubset>\<^sub>N\<^sub>E Errorable \<tau>"


code_pred [show_modes] subtype .



declare subtype_nullable_subtype_errorable_subtype.intros [intro!]


inductive_cases subtype_x_OclAny [elim!]: "\<tau> \<sqsubset> OclAny"
inductive_cases subtype_x_OclVoid [elim!]: "\<tau> \<sqsubset> OclVoid"
inductive_cases subtype_x_Boolean [elim!]: "\<tau> \<sqsubset> Boolean"
inductive_cases subtype_x_Real [elim!]: "\<tau> \<sqsubset> Real"
inductive_cases subtype_x_Integer [elim!]: "\<tau> \<sqsubset> Integer"
inductive_cases subtype_x_UnlimitedNatural [elim!]: "\<tau> \<sqsubset> UnlimitedNatural"
inductive_cases subtype_x_String [elim!]: "\<tau> \<sqsubset> String"
inductive_cases subtype_x_ObjectType [elim!]: "\<tau> \<sqsubset> ObjectType \<C>"
inductive_cases subtype_x_Enum [elim!]: "\<tau> \<sqsubset> Enum \<E>"
inductive_cases subtype_x_Collection [elim!]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases subtype_x_Set [elim!]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases subtype_x_OrderedSet [elim!]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases subtype_x_Bag [elim!]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases subtype_x_Sequence [elim!]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases subtype_x_Tuple [elim!]: "\<tau> \<sqsubset> Tuple \<pi>"

inductive_cases subtype_x_Required [elim!]: "\<tau> \<sqsubset>\<^sub>N Required \<sigma>"
inductive_cases subtype_x_Optional [elim!]: "\<tau> \<sqsubset>\<^sub>N Optional \<sigma>"
inductive_cases subtype_x_ErrorFree [elim!]: "\<tau> \<sqsubset>\<^sub>N\<^sub>E ErrorFree \<sigma>"
inductive_cases subtype_x_Errorable [elim!]: "\<tau> \<sqsubset>\<^sub>N\<^sub>E Errorable \<sigma>"

inductive_cases subtype_OclAny_x [elim!]: "OclAny \<sqsubset> \<sigma>"
inductive_cases subtype_Collection_x [elim!]: "Collection \<tau> \<sqsubset> \<sigma>"

lemma
  subtype_asym:
    "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> \<sigma> \<sqsubset> \<tau> \<Longrightarrow> False" and
  nullable_subtype_asym:
    "\<tau>' \<sqsubset>\<^sub>N \<sigma>' \<Longrightarrow> \<sigma>' \<sqsubset>\<^sub>N \<tau>' \<Longrightarrow> False" and
  errorable_subtype_asym:
    "\<tau>'' \<sqsubset>\<^sub>N\<^sub>E \<sigma>'' \<Longrightarrow> \<sigma>'' \<sqsubset>\<^sub>N\<^sub>E \<tau>'' \<Longrightarrow> False"
  for \<tau> \<sigma> :: "'a :: order type"
  and \<tau>' \<sigma>' :: "'a type\<^sub>N"
  and \<tau>'' \<sigma>'' :: "'a type\<^sub>N\<^sub>E"
  apply (induct rule: subtype_nullable_subtype_errorable_subtype.inducts, auto)
  using subtuple_antisym by fastforce

(*** Constructors Bijectivity on Transitive Closures ************************)

section \<open>Constructors Bijectivity on Transitive Closures\<close>

lemma ErrorFree_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N\<^sub>E) ErrorFree"
  by (auto simp add: inj_def)

lemma not_subtype_Errorable_ErrorFree:
  "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ (Errorable \<tau>) \<sigma> \<Longrightarrow> \<sigma> = ErrorFree \<rho> \<Longrightarrow> P"
  by (induct arbitrary: \<rho> rule: tranclp_induct; auto)

lemma Errorable_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N\<^sub>E) Errorable"
  apply (auto simp add: inj_def)
  using not_subtype_Errorable_ErrorFree by blast

lemma Required_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N) Required"
  by (auto simp add: inj_def)

lemma not_subtype_Optional_Required:
  "(\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ (Optional \<tau>) \<sigma> \<Longrightarrow> \<sigma> = Required \<rho> \<Longrightarrow> P"
  by (induct arbitrary: \<rho> rule: tranclp_induct; auto)

lemma Optional_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N) Optional"
  apply (auto simp add: inj_def)
  using not_subtype_Optional_Required by blast

lemma subtype_tranclp_Collection_x:
  "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct, auto)
  by (metis subtype_Collection_x subtype_OclAny_x tranclp.trancl_into_trancl)

lemma Collection_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Collection"
  apply (auto simp add: inj_def)
  using subtype_tranclp_Collection_x by auto

lemma Set_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Set"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma OrderedSet_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) OrderedSet"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Bag_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Bag"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Sequence_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Sequence"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Tuple_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Tuple"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

(*** Partial Order of Types *************************************************)

section \<open>Partial Order of Types\<close>

instantiation type :: (order) ord
begin
definition "(<) \<equiv> (\<sqsubset>)\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> (\<sqsubset>)\<^sup>*\<^sup>*"
instance ..
end

instantiation type\<^sub>N :: (order) ord
begin
definition "(<) \<equiv> (\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> (\<sqsubset>\<^sub>N)\<^sup>*\<^sup>*"
instance ..
end

instantiation type\<^sub>N\<^sub>E :: (order) ord
begin
definition "(<) \<equiv> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>*"
instance ..
end


instantiation type :: (order) order
begin

(*** Strict Introduction Rules **********************************************)

subsection \<open>Strict Introduction Rules\<close>

(* TODO: OclVoid < x *)

lemma type_less_OclVoid_x_intro [intro]:
  "\<tau> \<noteq> OclVoid \<Longrightarrow> OclVoid < \<tau>"
  apply (induct \<tau>, auto)
proof -
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid OclAny"
    by (rule_tac ?b="Boolean" in tranclp.trancl_into_trancl; auto)
  moreover have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid Integer"
    by (rule_tac ?b="UnlimitedNatural" in tranclp.trancl_into_trancl; auto)
  moreover hence "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid Real"
    by (rule_tac ?b="Integer" in tranclp.trancl_into_trancl; auto)
  moreover have "\<And>\<sigma>. (\<sqsubset>)\<^sup>+\<^sup>+ OclVoid (Collection \<sigma>)"
    apply (rule_tac ?b="Set OclVoid[1]" in tranclp_into_tranclp2)
    using subtype_nullable_subtype_errorable_subtype.intros apply auto[1]
    apply (rule_tac ?b="Collection OclVoid[1]" in tranclp_into_tranclp2)
    using subtype_nullable_subtype_errorable_subtype.intros apply auto[1]
    sorry
  ultimately show "\<tau> \<noteq> OclVoid \<Longrightarrow> OclVoid < \<tau>"
    unfolding less_type_def
    apply (induct \<tau>; auto)
qed


lemma type_less_x_Boolean_intro [intro]:
  "\<tau> = OclVoid \<Longrightarrow> \<tau> < Boolean"
  unfolding less_type_def
  by auto

lemma type_less_x_Real_intro [intro]:
  "\<tau> = Integer \<Longrightarrow> \<tau> < Real"
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> < Real"
  unfolding less_type_def
  by (rule rtranclp_into_tranclp2, auto)+

lemma type_less_x_Integer_intro [intro]:
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> < Integer"
  unfolding less_type_def
  by auto


(*
  OclAny
| OclVoid
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'a ("\<langle>_\<rangle>\<^sub>\<T>" [0] 1000)
| Enum "'a enum"
| Collection "'a type\<^sub>N\<^sub>E"
| Set "'a type\<^sub>N\<^sub>E"
| OrderedSet "'a type\<^sub>N\<^sub>E"
| Bag "'a type\<^sub>N\<^sub>E"
| Sequence "'a type\<^sub>N\<^sub>E"
| Tuple "telem \<rightharpoonup>\<^sub>f 'a type\<^sub>N\<^sub>E"

*)


lemma type_less_x_ErrorFree_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < ErrorFree \<sigma>"
  unfolding less_type\<^sub>N\<^sub>E_def less_type\<^sub>N_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Errorable_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Errorable \<sigma>"
  "\<tau> = Errorable \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Errorable \<sigma>"
  unfolding less_type\<^sub>N\<^sub>E_def less_type\<^sub>N_def less_eq_type\<^sub>N_def
  apply simp_all
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_tranclp; auto)

lemma type_less_x_Required_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Required \<sigma>"
  unfolding less_type\<^sub>N_def less_type_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Optional_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Optional \<sigma>"
  "\<tau> = Optional \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Optional \<sigma>"
  unfolding less_type\<^sub>N_def less_type_def less_eq_type_def
  apply simp_all
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_tranclp; auto)

lemma type_less_x_Collection_intro [intro]:
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def less_eq_type\<^sub>N\<^sub>E_def
  apply simp_all
  apply (rule_tac ?f="Collection" in preserve_tranclp; auto)
  apply (rule preserve_rtranclp''; auto)
  apply (rule preserve_rtranclp''; auto)
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_rtranclp''; auto)

lemma type_less_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Set \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < OrderedSet \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Bag \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Sequence \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma fun_or_eq_refl [intro]:
  "reflp (\<lambda>x y. f x y \<or> x = y)"
  by (simp add: reflpI)

lemma type_less_x_Tuple_intro [intro]:
  assumes "\<tau> = Tuple \<pi>"
      and "strict_subtuple (\<le>) \<pi> \<xi>"
    shows "\<tau> < Tuple \<xi>"
proof -
  have "subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>)\<^sup>*\<^sup>* \<pi> \<xi>"
    by (metis assms(2) less_eq_type\<^sub>N\<^sub>E_def rtranclp_eq_rtranclp)
  hence "(subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by simp (rule subtuple_to_trancl; auto)
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>))\<^sup>*\<^sup>* \<pi> \<xi>"
    by (simp add: tranclp_into_rtranclp)
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by (meson assms(2) rtranclpD)
  thus ?thesis
    unfolding less_type_def
    using assms(1) apply simp
    by (rule preserve_tranclp; auto)
qed
(*
lemma type_less_x_OclAny_intro [intro]:
  "\<tau> \<noteq> OclAny \<Longrightarrow> \<tau> < OclAny"
  unfolding less_type_def
proof (cases \<tau>)
  case OclAny
  then show ?thesis sorry
next
  case OclVoid
  then show ?thesis sorry
next
  case Boolean
  then show ?thesis sorry
next
  case Real
  then show ?thesis sorry
next
  case Integer
  then show ?thesis sorry
next
  case UnlimitedNatural
  then show ?thesis sorry
next
  case String
  then show ?thesis sorry
next
  case (ObjectType x8)
  then show ?thesis sorry
next
  case (Enum x9)
  then show ?thesis sorry
next
  case (Collection x10)
  then show ?thesis sorry
next
  case (Set x11)
  then show ?thesis sorry
next
  case (OrderedSet x12)
  then show ?thesis sorry
next
  case (Bag x13)
  then show ?thesis sorry
next
  case (Sequence x14)
  then show ?thesis sorry
next
  case (Tuple x15)
  then show ?thesis sorry
qed
*)
(*
proof (induct \<tau>)
  case OclAny thus ?case by auto
next
  case OclVoid
  then show ?case sorry
next
  case Boolean show ?case by auto
next
  case Real show ?case by auto
next
  case Integer
  then show ?case sorry
next
  case UnlimitedNatural
  then show ?case sorry
next
  case String show ?case by auto
next
  case (ObjectType x) show ?case by auto
next
  case (Enum x) show ?case by auto
next
  case (Collection x)
  then show ?case sorry
next
  case (Set x)
  then show ?case sorry
next
  case (OrderedSet x)
  then show ?case sorry
next
  case (Bag x)
  then show ?case sorry
next
  case (Sequence x)
  then show ?case sorry
next
  case (Tuple x)
  then show ?case sorry
next
  case (Required \<tau>)
  then show ?thesis sorry
next
  case (Optional \<tau>)
  then show ?thesis sorry
next
  case (ErrorFree x)
  then show ?thesis sorry
next
  case (Errorable x)
  then show ?thesis sorry
qed
*)
(*
  
  case OclAny thus ?case by auto
next
  case (Required \<tau>)
  have "subtype\<^sup>*\<^sup>* \<tau>[1] OclAny[1]"
    apply (rule_tac ?f="Required" in preserve_rtranclp[of basic_subtype], auto)
    by (metis less_eq_basic_type_def type_less_eq_x_OclAny_intro)
  also have "subtype\<^sup>+\<^sup>+ OclAny[1] OclAny[?]" by auto
  also have "subtype\<^sup>+\<^sup>+ OclAny[?] OclSuper" by auto
  finally show ?case by auto
next
  case (Optional \<tau>)
  have "subtype\<^sup>*\<^sup>* \<tau>[?] OclAny[?]"
    apply (rule_tac ?f="Optional" in preserve_rtranclp[of basic_subtype], auto)
    by (metis less_eq_basic_type_def type_less_eq_x_OclAny_intro)
  also have "subtype\<^sup>+\<^sup>+ OclAny[?] OclSuper" by auto
  finally show ?case by auto
next
  case (Collection \<tau>)
  have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Collection.hyps by force
  also have "subtype\<^sup>+\<^sup>+ (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Set \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Set \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Set.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (OrderedSet \<tau>)
  have "subtype\<^sup>+\<^sup>+ (OrderedSet \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using OrderedSet.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Bag \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Bag \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Bag.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Sequence \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Sequence \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    apply (rule_tac ?f="Collection" in preserve_rtranclp[of subtype], auto)
    using Sequence.hyps by force
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Tuple x) thus ?case by auto
qed
*)
(*** Strict Elimination Rules ***********************************************)

subsection \<open>Strict Elimination Rules\<close>

lemma type_less_x_Required [elim!]:
  assumes "\<tau> < Required \<sigma>"
      and "\<And>\<rho>. \<tau> = Required \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Required \<rho>"
    unfolding less_type\<^sub>N_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Required \<tau> < Required \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
(*
lemma type_less_x_Optional [elim!]:
  assumes "\<tau> < \<sigma>[?]"
      and "\<tau> = OclVoid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where
    "\<tau> = OclVoid \<or> \<tau> = \<rho>[1] \<or> \<tau> = \<rho>[?]"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[1] < \<sigma>[?] \<Longrightarrow> \<tau> \<le> \<sigma>"
    unfolding less_type_def less_eq_basic_type_def
    apply (drule tranclpD, auto)
    apply (erule subtype.cases, auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[?] < \<sigma>[?] \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_basic_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
*)
lemma type_less_x_Optional [elim!]:
  "\<tau> < Optional \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Optional \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type\<^sub>N_def less_type_def less_eq_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  apply (erule nullable_subtype.cases;
      auto simp: converse_rtranclp_into_rtranclp tranclp_into_tranclp2)
  by (meson Nitpick.rtranclp_unfold)

lemma type_less_x_Collection [elim!]:
  "\<tau> < Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def less_eq_type\<^sub>N\<^sub>E_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  by (erule subtype.cases;
      auto simp add: converse_rtranclp_into_rtranclp less_eq_type_def
                     tranclp_into_tranclp2 tranclp_into_rtranclp)

lemma type_less_x_Set [elim!]:
  assumes "\<tau> < Set \<sigma>"
      and "\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Set \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Set \<tau> < Set \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OrderedSet [elim!]:
  assumes "\<tau> < OrderedSet \<sigma>"
      and "\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OrderedSet \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. OrderedSet \<tau> < OrderedSet \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Bag [elim!]:
  assumes "\<tau> < Bag \<sigma>"
      and "\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Bag \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Bag \<tau> < Bag \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Sequence [elim!]:
  assumes "\<tau> < Sequence \<sigma>"
      and "\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Sequence \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Sequence \<tau> < Sequence \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

text \<open>
  We will be able to remove the acyclicity assumption only after
  we prove that the subtype relation is acyclic.\<close>

lemma type_less_x_Tuple':
  assumes "\<tau> < Tuple \<xi>"
      and "acyclicP_on (fmran' \<xi>) (\<sqsubset>\<^sub>N\<^sub>E)"
      and "\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<pi> where "\<tau> = Tuple \<pi> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover from assms(2) have
    "\<And>\<pi>. Tuple \<pi> < Tuple \<xi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi>"
    unfolding less_type_def less_eq_type\<^sub>N\<^sub>E_def
    apply (rule_tac ?f="Tuple" in strict_subtuple_rtranclp_intro)
(*    by (rule_tac ?f="Tuple" in strict_subtuple_rtranclp_intro; auto)*)
    sorry
    thm strict_subtuple_rtranclp_intro
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OclSuper [elim!]:
  "\<tau> < OclAny \<Longrightarrow> (\<tau> \<noteq> OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (drule tranclpD, auto)

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma
  subtype_irrefl: "\<tau> < \<tau> \<Longrightarrow> False" (*and
  subtype_irrefl': "\<tau>' < \<tau>' \<Longrightarrow> False" and
  subtype_irrefl'': "\<tau>'' < \<tau>'' \<Longrightarrow> False"*)
  for \<tau> :: "'a type"
(*  and \<tau>' :: "'a type\<^sub>N"
  and \<tau>'' :: "'a type\<^sub>N\<^sub>E"*)
  unfolding less_type_def tranclp_unfold

  apply auto
    apply (induct \<tau> and \<tau>' and \<tau>'', auto)

  unfolding less_type_def tranclp_unfold
  by auto


lemma subtype_irrefl:
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: "'a type"
  apply (induct \<tau>, auto)
  apply (metis less_type_def subtype_x_OclVoid tranclp.simps)
  apply (metis (no_types, lifting) less_type_def subtype_x_Boolean subtype_x_OclVoid tranclp.simps)
  apply (erule type_less_x_Tuple', auto)
  unfolding less_type_def tranclp_unfold
  by auto

lemma subtype_acyclic:
  "acyclicP subtype"
  apply (rule acyclicI)
  apply (simp add: trancl_def)
  by (metis (mono_tags) OCL_Types.less_type_def OCL_Types.subtype_irrefl)

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof
  show "\<tau> < \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
    apply (auto simp add: less_type_def less_eq_type_def)
    by (metis (mono_tags) subtype_irrefl less_type_def tranclp_rtranclp_tranclp)
  show "\<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> < \<sigma>"
    apply (auto simp add: less_type_def less_eq_type_def)
    by (metis rtranclpD)
qed

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type"
  unfolding less_eq_type_def by simp

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  unfolding less_eq_type_def by simp

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  unfolding less_eq_type_def less_type_def
  by (metis (mono_tags, lifting) less_eq_type_def
      less_le_not_le_type less_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  by (simp add: antisym_type)

end

(*** Non-Strict Introduction Rules ******************************************)

subsection \<open>Non-Strict Introduction Rules\<close>

lemma type_less_eq_x_Required_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Required \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Optional_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Collection_intro [intro]:
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Tuple_intro [intro]:
  "\<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> \<tau> \<le> Tuple \<xi>"
  using dual_order.strict_iff_order by blast

lemma type_less_eq_x_OclSuper_intro [intro]:
  "\<tau> \<le> OclSuper"
  unfolding dual_order.order_iff_strict by auto

(*** Non-Strict Elimination Rules *******************************************)

subsection \<open>Non-Strict Elimination Rules\<close>

lemma type_less_eq_x_Required [elim!]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Optional [elim!]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq, auto)

lemma type_less_eq_x_Collection [elim!]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Set [elim!]:
   "\<tau> \<le> Set \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_OrderedSet [elim!]:
   "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Bag [elim!]:
   "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Sequence [elim!]:
   "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_x_Tuple [elim!]:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (erule type_less_x_Tuple')
  by (meson acyclic_def subtype_acyclic)

lemma type_less_eq_x_Tuple [elim!]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule le_imp_less_or_eq, auto)
  by (simp add: fmap.rel_refl fmrel_to_subtuple)

(*** Simplification Rules ***************************************************)

subsection \<open>Simplification Rules\<close>

lemma type_less_left_simps [simp]:
  "OclSuper < \<sigma> = False"
  "\<rho>[1] < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = OclSuper \<or>
      \<sigma> = \<upsilon>[1] \<and> \<rho> < \<upsilon> \<or>
      \<sigma> = \<upsilon>[?] \<and> \<rho> \<le> \<upsilon>)"
  "\<rho>[?] < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = OclSuper \<or>
      \<sigma> = \<upsilon>[?] \<and> \<rho> < \<upsilon>)"
  "Collection \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> < \<phi>)"
  "Set \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Set \<phi> \<and> \<tau> < \<phi>)"
  "OrderedSet \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = OrderedSet \<phi> \<and> \<tau> < \<phi>)"
  "Bag \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Bag \<phi> \<and> \<tau> < \<phi>)"
  "Sequence \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Sequence \<phi> \<and> \<tau> < \<phi>)"
  "Tuple \<pi> < \<sigma> = (\<exists>\<xi>.
      \<sigma> = OclSuper \<or>
      \<sigma> = Tuple \<xi> \<and> strict_subtuple (\<le>) \<pi> \<xi>)"
  by (induct \<sigma>; auto)+

lemma type_less_right_simps [simp]:
  "\<tau> < OclSuper = (\<tau> \<noteq> OclSuper)"
  "\<tau> < \<upsilon>[1] = (\<exists>\<rho>. \<tau> = \<rho>[1] \<and> \<rho> < \<upsilon>)"
  "\<tau> < \<upsilon>[?] = (\<exists>\<rho>. \<tau> = \<rho>[1] \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = \<rho>[?] \<and> \<rho> < \<upsilon>)"
  "\<tau> < Collection \<sigma> = (\<exists>\<phi>.
      \<tau> = Collection \<phi> \<and> \<phi> < \<sigma> \<or>
      \<tau> = Set \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = OrderedSet \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Bag \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Sequence \<phi> \<and> \<phi> \<le> \<sigma>)"
  "\<tau> < Set \<sigma> = (\<exists>\<phi>. \<tau> = Set \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < OrderedSet \<sigma> = (\<exists>\<phi>. \<tau> = OrderedSet \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < Bag \<sigma> = (\<exists>\<phi>. \<tau> = Bag \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < Sequence \<sigma> = (\<exists>\<phi>. \<tau> = Sequence \<phi> \<and> \<phi> < \<sigma>)"
  "\<tau> < Tuple \<xi> = (\<exists>\<pi>. \<tau> = Tuple \<pi> \<and> strict_subtuple (\<le>) \<pi> \<xi>)"
  by auto

(*** Upper Semilattice of Types *********************************************)

section \<open>Upper Semilattice of Types\<close>

instantiation type :: (semilattice_sup) semilattice_sup
begin

fun sup_type where
  "OclSuper \<squnion> \<sigma> = OclSuper"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[1]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> OclSuper)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> OclSuper)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Tuple \<pi> \<squnion> \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> Tuple (fmmerge_fun (\<squnion>) \<pi> \<xi>)
     | _ \<Rightarrow> OclSuper)"

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case OclSuper show ?case by simp
  case (Required \<tau>) show ?case by (induct \<sigma>; auto)
  case (Optional \<tau>) show ?case by (induct \<sigma>; auto)
  case (Collection \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Set \<tau>) thus ?case by (induct \<sigma>; auto)
  case (OrderedSet \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Bag \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Sequence \<tau>) thus ?case by (induct \<sigma>; auto)
next
  case (Tuple \<pi>) thus ?case by (cases \<sigma>, auto)
qed

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case OclSuper show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case (Required \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Optional \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Collection \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Set \<tau>) thus ?case by (cases \<sigma>; simp)
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Bag \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Tuple \<pi>) thus ?case
    apply (cases \<sigma>; simp add: less_eq_type_def)
    using fmmerge_commut by blast
qed

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
proof (induct \<rho> arbitrary: \<tau> \<sigma>)
  case OclSuper show ?case using eq_refl by auto
next
  case (Required x) show ?case
    apply (insert Required)
    by (erule type_less_eq_x_Required; erule type_less_eq_x_Required; auto)
next
  case (Optional x) show ?case
    apply (insert Optional)
    by (erule type_less_eq_x_Optional; erule type_less_eq_x_Optional; auto)
next
  case (Collection \<rho>) show ?case
    apply (insert Collection)
    by (erule type_less_eq_x_Collection; erule type_less_eq_x_Collection; auto)
next
  case (Set \<rho>) show ?case
    apply (insert Set)
    by (erule type_less_eq_x_Set; erule type_less_eq_x_Set; auto)
next
  case (OrderedSet \<rho>) show ?case
    apply (insert OrderedSet)
    by (erule type_less_eq_x_OrderedSet; erule type_less_eq_x_OrderedSet; auto)
next
  case (Bag \<rho>) show ?case
    apply (insert Bag)
    by (erule type_less_eq_x_Bag; erule type_less_eq_x_Bag; auto)
next
  case (Sequence \<rho>) thus ?case
    apply (insert Sequence)
    by (erule type_less_eq_x_Sequence; erule type_less_eq_x_Sequence; auto)
next
  case (Tuple \<pi>) show ?case
    apply (insert Tuple)
    apply (erule type_less_eq_x_Tuple; erule type_less_eq_x_Tuple; auto)
    by (rule_tac ?\<pi>="(fmmerge (\<squnion>) \<pi>' \<pi>'')" in type_less_eq_x_Tuple_intro;
        simp add: fmrel_on_fset_fmmerge1)
qed

instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end

(*** Helper Relations *******************************************************)

section \<open>Helper Relations\<close>

abbreviation between ("_/ = _\<midarrow>_"  [51, 51, 51] 50) where
  "x = y\<midarrow>z \<equiv> y \<le> x \<and> x \<le> z"

inductive element_type where
  "element_type (Collection \<tau>) \<tau>"
| "element_type (Set \<tau>) \<tau>"
| "element_type (OrderedSet \<tau>) \<tau>"
| "element_type (Bag \<tau>) \<tau>"
| "element_type (Sequence \<tau>) \<tau>"

lemma element_type_alt_simps:
  "element_type \<tau> \<sigma> = 
     (Collection \<sigma> = \<tau> \<or>
      Set \<sigma> = \<tau> \<or>
      OrderedSet \<sigma> = \<tau> \<or>
      Bag \<sigma> = \<tau> \<or>
      Sequence \<sigma> = \<tau>)"
  by (auto simp add: element_type.simps)

inductive update_element_type where
  "update_element_type (Collection _) \<tau> (Collection \<tau>)"
| "update_element_type (Set _) \<tau> (Set \<tau>)"
| "update_element_type (OrderedSet _) \<tau> (OrderedSet \<tau>)"
| "update_element_type (Bag _) \<tau> (Bag \<tau>)"
| "update_element_type (Sequence _) \<tau> (Sequence \<tau>)"

inductive to_unique_collection where
  "to_unique_collection (Collection \<tau>) (Set \<tau>)"
| "to_unique_collection (Set \<tau>) (Set \<tau>)"
| "to_unique_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection (Bag \<tau>) (Set \<tau>)"
| "to_unique_collection (Sequence \<tau>) (OrderedSet \<tau>)"

inductive to_nonunique_collection where
  "to_nonunique_collection (Collection \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Set \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (OrderedSet \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection (Bag \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Sequence \<tau>) (Sequence \<tau>)"

inductive to_ordered_collection where
  "to_ordered_collection (Collection \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Set \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (Bag \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Sequence \<tau>) (Sequence \<tau>)"

fun to_single_type where
  "to_single_type OclSuper = OclSuper"
| "to_single_type \<tau>[1] = \<tau>[1]"
| "to_single_type \<tau>[?] = \<tau>[?]"
| "to_single_type (Collection \<tau>) = to_single_type \<tau>"
| "to_single_type (Set \<tau>) = to_single_type \<tau>"
| "to_single_type (OrderedSet \<tau>) = to_single_type \<tau>"
| "to_single_type (Bag \<tau>) = to_single_type \<tau>"
| "to_single_type (Sequence \<tau>) = to_single_type \<tau>"
| "to_single_type (Tuple \<pi>) = Tuple \<pi>"

fun to_required_type where
  "to_required_type \<tau>[1] = \<tau>[1]"
| "to_required_type \<tau>[?] = \<tau>[1]"
| "to_required_type \<tau> = \<tau>"

fun to_optional_type_nested where
  "to_optional_type_nested OclSuper = OclSuper"
| "to_optional_type_nested \<tau>[1] = \<tau>[?]"
| "to_optional_type_nested \<tau>[?] = \<tau>[?]"
| "to_optional_type_nested (Collection \<tau>) = Collection (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Set \<tau>) = Set (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (OrderedSet \<tau>) = OrderedSet (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Bag \<tau>) = Bag (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Sequence \<tau>) = Sequence (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Tuple \<pi>) = Tuple (fmmap to_optional_type_nested \<pi>)"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma element_type_det:
  "element_type \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   element_type \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: element_type.induct; simp add: element_type.simps)

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: update_element_type.induct; simp add: update_element_type.simps)

lemma to_unique_collection_det:
  "to_unique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_unique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_unique_collection.induct; simp add: to_unique_collection.simps)

lemma to_nonunique_collection_det:
  "to_nonunique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_nonunique_collection.induct; simp add: to_nonunique_collection.simps)

lemma to_ordered_collection_det:
  "to_ordered_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_ordered_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_ordered_collection.induct; simp add: to_ordered_collection.simps)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred subtype .

function subtype_fun :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" where
  "subtype_fun OclSuper _ = False"
| "subtype_fun (Required \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | \<rho>[1] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Optional \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Collection \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Set \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Set \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (OrderedSet \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OrderedSet \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Bag \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Bag \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Sequence \<tau>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Sequence \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Tuple \<pi>) \<sigma> = (case \<sigma>
    of OclSuper \<Rightarrow> True
     | Tuple \<xi> \<Rightarrow> strict_subtuple_fun (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>
     | _ \<Rightarrow> False)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(xs, ys). size ys)";
      auto simp add: elem_le_ffold' fmran'I)

lemma less_type_code [code]:
  "(<) = subtype_fun"
proof (intro ext iffI)
  fix \<tau> \<sigma> :: "'a type"
  show "\<tau> < \<sigma> \<Longrightarrow> subtype_fun \<tau> \<sigma>"
  proof (induct \<tau> arbitrary: \<sigma>)
    case OclSuper thus ?case by (cases \<sigma>; auto)
  next
    case (Required \<tau>) thus ?case
      by (cases \<sigma>; auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Optional \<tau>) thus ?case
      by (cases \<sigma>; auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Collection \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Set \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Bag \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Sequence \<tau>) thus ?case by (cases \<sigma>; auto)
  next
    case (Tuple \<pi>)
    have
      "\<And>\<xi>. subtuple (\<le>) \<pi> \<xi> \<longrightarrow>
       subtuple (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>"
      by (rule subtuple_mono; auto simp add: Tuple.hyps)
    with Tuple.prems show ?case by (cases \<sigma>; auto)
  qed
  show "subtype_fun \<tau> \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
  proof (induct \<sigma> arbitrary: \<tau>)
    case OclSuper thus ?case by (cases \<sigma>; auto)
  next
    case (Required \<sigma>) show ?case
      by (insert Required) (erule subtype_fun.elims;
          auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Optional \<sigma>) show ?case
      by (insert Optional) (erule subtype_fun.elims;
          auto simp: less_basic_type_code less_eq_basic_type_code)
  next
    case (Collection \<sigma>) show ?case
      apply (insert Collection)
      apply (erule subtype_fun.elims; auto)
      using order.strict_implies_order by auto
  next
    case (Set \<sigma>) show ?case
      by (insert Set) (erule subtype_fun.elims; auto)
  next
    case (OrderedSet \<sigma>) show ?case
      by (insert OrderedSet) (erule subtype_fun.elims; auto)
  next
    case (Bag \<sigma>) show ?case
      by (insert Bag) (erule subtype_fun.elims; auto)
  next
    case (Sequence \<sigma>) show ?case
      by (insert Sequence) (erule subtype_fun.elims; auto)
  next
    case (Tuple \<xi>)
    have subtuple_imp_simp:
      "\<And>\<pi>. subtuple (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<longrightarrow>
       subtuple (\<le>) \<pi> \<xi>"
      by (rule subtuple_mono; auto simp add: Tuple.hyps less_imp_le)
    show ?case
      apply (insert Tuple)
      by (erule subtype_fun.elims; auto simp add: subtuple_imp_simp)
  qed
qed

lemma less_eq_type_code [code]:
  "(\<le>) = (\<lambda>x y. subtype_fun x y \<or> x = y)"
  unfolding dual_order.order_iff_strict less_type_code
  by auto

code_pred element_type .
code_pred update_element_type .
code_pred to_unique_collection .
code_pred to_nonunique_collection .
code_pred to_ordered_collection .

end

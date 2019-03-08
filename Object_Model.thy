(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Object Model\label{sec:object-model}\<close>
theory Object_Model
  imports "HOL-Library.Extended_Nat" Finite_Map_Ext
begin

text \<open>
  The section defines a very simplified object model.
  It should define more constraints.\<close>

(*** Preliminaries **********************************************************)

subsection \<open>Preliminaries\<close>

type_synonym attr = String.literal
type_synonym assoc = String.literal
type_synonym role = String.literal
type_synonym oper = String.literal
type_synonym param = String.literal
type_synonym elit = String.literal

datatype param_dir = In | Out | InOut

type_synonym 'c assoc_end = "'c \<times> nat \<times> enat \<times> bool \<times> bool"
type_synonym 't param_spec = "param \<times> 't \<times> param_dir"
type_synonym ('t, 'e) oper_spec =
  "oper \<times> 't \<times> 't param_spec list \<times> 't \<times> bool \<times> 'e option"

definition "assoc_end_class :: 'c assoc_end \<Rightarrow> 'c \<equiv> fst"
definition "assoc_end_min :: 'c assoc_end \<Rightarrow> nat \<equiv> fst \<circ> snd"
definition "assoc_end_max :: 'c assoc_end \<Rightarrow> enat \<equiv> fst \<circ> snd \<circ> snd"
definition "assoc_end_ordered :: 'c assoc_end \<Rightarrow> bool \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_unique :: 'c assoc_end \<Rightarrow> bool \<equiv> snd \<circ> snd \<circ> snd \<circ> snd"

definition "oper_name :: ('t, 'e) oper_spec \<Rightarrow> oper \<equiv> fst"
definition "oper_context :: ('t, 'e) oper_spec \<Rightarrow> 't \<equiv> fst \<circ> snd"
definition "oper_params :: ('t, 'e) oper_spec \<Rightarrow> 't param_spec list \<equiv> fst \<circ> snd \<circ> snd"
definition "oper_result :: ('t, 'e) oper_spec \<Rightarrow> 't \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "oper_static :: ('t, 'e) oper_spec \<Rightarrow> bool \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
definition "oper_body :: ('t, 'e) oper_spec \<Rightarrow> 'e option \<equiv> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

definition "param_name ::'t param_spec \<Rightarrow> param \<equiv> fst"
definition "param_type ::'t param_spec \<Rightarrow> 't \<equiv> fst \<circ> snd"
definition "param_dir ::'t param_spec \<Rightarrow> param_dir \<equiv> snd \<circ> snd"

definition "oper_in_params op \<equiv>
  filter (\<lambda>p. param_dir p = In \<or> param_dir p = InOut) (oper_params op)"

definition "oper_out_params op \<equiv>
  filter (\<lambda>p. param_dir p = Out \<or> param_dir p = InOut) (oper_params op)"

text \<open>
  The following predicates allows one to access class attributes.\<close>

inductive owned_attribute' where
  "\<C> |\<in>| fmdom attributes \<Longrightarrow>
   fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
   fmlookup attrs\<^sub>\<C> attr = Some \<tau> \<Longrightarrow>
   owned_attribute' attributes \<C> attr \<tau>"

inductive attribute_not_closest where
  "owned_attribute' attributes \<D>' attr \<tau>' \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow>
   \<D>' < \<D> \<Longrightarrow>
   attribute_not_closest attributes \<C> attr \<D> \<tau>"

inductive closest_attribute where
  "owned_attribute' attributes \<D> attr \<tau> \<Longrightarrow>
   \<C> \<le> \<D> \<Longrightarrow>
   \<not> attribute_not_closest attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   closest_attribute attributes \<C> attr \<D> \<tau>"

inductive closest_attribute_not_unique where
  "closest_attribute attributes \<C> attr \<D>' \<tau>' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<or> \<tau> \<noteq> \<tau>' \<Longrightarrow>
   closest_attribute_not_unique attributes \<C> attr \<D> \<tau>"

inductive unique_closest_attribute where
  "closest_attribute attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   \<not> closest_attribute_not_unique attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   unique_closest_attribute attributes \<C> attr \<D> \<tau>"
(*
lemma closest_attribute_alt_simp:
  "closest_attribute attributes \<C> attr \<D> \<tau> =
   (owned_attribute' attributes \<D> attr \<tau> \<and>
    \<C> \<le> \<D> \<and>
    (\<forall>\<D>' \<tau>'. owned_attribute' attributes \<D>' attr \<tau>' \<longrightarrow> \<C> \<le> \<D>' \<longrightarrow> \<not> \<D>' < \<D>))"
  by (auto simp add: attribute_not_closest.simps closest_attribute.simps)

lemma unique_closest_attribute_alt_simp:
  "unique_closest_attribute attributes \<C> attr \<D> \<tau> =
   (closest_attribute attributes \<C> attr \<D> \<tau> \<and>
    (\<forall>\<D>' \<tau>'. closest_attribute attributes \<C> attr \<D>' \<tau>' \<longrightarrow> \<D> = \<D>' \<and> \<tau> = \<tau>'))"
  by (simp add: closest_attribute_not_unique.simps unique_closest_attribute.simps)
*)
text \<open>
  The following predicates allows one to access association ends.\<close>

inductive role_refer_class where
  "role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = \<C> \<Longrightarrow>
   role_refer_class ends \<C> role"

inductive class_roles where
  "\<C> |\<in>| classes \<Longrightarrow>
   assoc |\<in>| fmdom associations \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   role_refer_class ends \<C> from \<Longrightarrow>
   role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   class_roles classes associations \<C> from role end"

inductive owned_association_end' where
  "class_roles classes associations \<C> from role end \<Longrightarrow>
   owned_association_end' classes associations \<C> None role end"
| "class_roles classes associations \<C> from role end \<Longrightarrow>
   owned_association_end' classes associations \<C> (Some from) role end"

inductive association_end_not_closest where
  "owned_association_end' classes associations \<D>' from role end' \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow>
   \<D>' < \<D> \<Longrightarrow>
   association_end_not_closest classes associations \<C> from role \<D> end"

inductive closest_association_end where
  "owned_association_end' classes associations \<D> from role end \<Longrightarrow>
   \<C> \<le> \<D> \<Longrightarrow>
   \<not> association_end_not_closest classes associations \<C> from role \<D> end \<Longrightarrow>
   closest_association_end classes associations \<C> from role \<D> end"

inductive closest_association_end_not_unique where
  "closest_association_end classes associations \<C> from role \<D>' end' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<or> end \<noteq> end' \<Longrightarrow>
   closest_association_end_not_unique classes associations \<C> from role \<D> end"

inductive unique_closest_association_end where
  "closest_association_end classes associations \<C> from role \<D> end \<Longrightarrow>
   \<not> closest_association_end_not_unique classes associations \<C> from role \<D> end \<Longrightarrow>
   unique_closest_association_end classes associations \<C> from role \<D> end"

text \<open>
  The following predicates allows one to access association classes.\<close>

inductive referred_by_association_class''' where
  "fmlookup association_classes \<A> = Some assoc \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   role_refer_class ends \<C> from \<Longrightarrow>
   referred_by_association_class''' association_classes associations \<C> from \<A>"

inductive referred_by_association_class'' where
  "referred_by_association_class''' association_classes associations \<C> from \<A> \<Longrightarrow>
   referred_by_association_class'' association_classes associations \<C> None \<A>"
| "referred_by_association_class''' association_classes associations \<C> from \<A> \<Longrightarrow>
   referred_by_association_class'' association_classes associations \<C> (Some from) \<A>"

inductive association_class_not_closest where
  "referred_by_association_class'' association_classes associations \<D>' from \<A> \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow>
   \<D>' < \<D> \<Longrightarrow>
   association_class_not_closest association_classes associations \<C> from \<A> \<D>"

inductive closest_association_class where
  "referred_by_association_class'' association_classes associations \<D> from \<A> \<Longrightarrow>
   \<C> \<le> \<D> \<Longrightarrow>
   \<not> association_class_not_closest association_classes associations \<C> from \<A> \<D> \<Longrightarrow>
   closest_association_class association_classes associations \<C> from \<A> \<D>"

inductive closest_association_class_not_unique where
  "closest_association_class association_classes associations \<C> from \<A> \<D>' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<Longrightarrow>
   closest_association_class_not_unique association_classes associations \<C> from \<A> \<D>"

inductive unique_closest_association_class where
  "closest_association_class association_classes associations \<C> from \<A> \<D> \<Longrightarrow>
   \<not> closest_association_class_not_unique association_classes associations \<C> from \<A> \<D> \<Longrightarrow>
   unique_closest_association_class association_classes associations \<C> from \<A> \<D>"

text \<open>
  The following predicates allows one to access ends of association classes.\<close>

inductive association_class_end' where
  "fmlookup association_classes \<A> = Some assoc \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   association_class_end' association_classes associations \<A> role end"

inductive association_class_end_not_unique where
  "association_class_end' association_classes associations \<A> role end' \<Longrightarrow>
   end \<noteq> end' \<Longrightarrow>
   association_class_end_not_unique association_classes associations \<A> role end"

inductive unique_association_class_end where
  "association_class_end' association_classes associations \<A> role end \<Longrightarrow>
   \<not> association_class_end_not_unique association_classes associations \<A> role end \<Longrightarrow>
   unique_association_class_end association_classes associations \<A> role end"

text \<open>
  The following predicates allows one to access class operations.\<close>

inductive any_operation' where
  "op |\<in>| fset_of_list operations \<Longrightarrow>
   oper_name op = name \<Longrightarrow>
   \<tau> \<le> oper_context op \<Longrightarrow>
   list_all2 (\<lambda>\<sigma> param. \<sigma> \<le> param_type param) \<pi> (oper_in_params op) \<Longrightarrow>
   any_operation' operations \<tau> name \<pi> op"

inductive operation' where
  "any_operation' operations \<tau> name \<pi> op \<Longrightarrow>
   \<not> oper_static op \<Longrightarrow>
   operation' operations \<tau> name \<pi> op"

inductive operation_not_unique where
  "operation' operations \<tau> name \<pi> oper' \<Longrightarrow>
   oper \<noteq> oper' \<Longrightarrow>
   operation_not_unique operations \<tau> name \<pi> oper"

inductive unique_operation where
  "operation' operations \<tau> name \<pi> oper \<Longrightarrow>
   \<not> operation_not_unique operations \<tau> name \<pi> oper \<Longrightarrow>
   unique_operation operations \<tau> name \<pi> oper"

inductive static_operation' where
  "any_operation' operations \<tau> name \<pi> op \<Longrightarrow>
   oper_static op \<Longrightarrow>
   static_operation' operations \<tau> name \<pi> op"

inductive static_operation_not_unique where
  "static_operation' operations \<tau> name \<pi> oper' \<Longrightarrow>
   oper \<noteq> oper' \<Longrightarrow>
   static_operation_not_unique operations \<tau> name \<pi> oper"

inductive unique_static_operation where
  "static_operation' operations \<tau> name \<pi> oper \<Longrightarrow>
   \<not> static_operation_not_unique operations \<tau> name \<pi> oper \<Longrightarrow>
   unique_static_operation operations \<tau> name \<pi> oper"

text \<open>
  The following predicate allows one to check an enumeration literal for existence.\<close>

inductive has_literal' where
  "fmlookup literals e = Some lits \<Longrightarrow>
   lit |\<in>| lits \<Longrightarrow>
   has_literal' literals e lit"

(*** Elimination Rules ******************************************************)

subsection \<open>Elimination Rules\<close>
(*
inductive_cases owned_attribute'E [elim!]: "owned_attribute' attributes \<C> attr \<tau>"
inductive_cases attribute_not_closestE [elim!]: "attribute_not_closest attributes \<C> attr \<D> \<tau>"
inductive_cases closest_attributeE [elim!]: "closest_attribute attributes \<C> attr \<D> \<tau>"
inductive_cases closest_attribute_not_uniqueE [elim!]: "closest_attribute_not_unique attributes \<C> attr \<D> \<tau>"
inductive_cases unique_closest_attributeE [elim!]: "unique_closest_attribute attributes \<C> attr \<D> \<tau>"

inductive_cases role_refer_classE [elim!]: "role_refer_class ends \<C> role"
inductive_cases class_rolesE [elim!]: "class_roles classes associations \<C> from role end"
inductive_cases owned_association_end'E [elim!]: "owned_association_end' classes associations \<C> (Some from) role end"
inductive_cases association_end_not_closestE [elim!]: "association_end_not_closest classes associations \<C> from role \<D> end"
inductive_cases closest_association_endE [elim!]: "closest_association_end classes associations \<C> from role \<D> end"
inductive_cases closest_association_end_not_uniqueE [elim!]: "closest_association_end_not_unique classes associations \<C> from role \<D> end"
inductive_cases unique_closest_association_endE [elim!]: "unique_closest_association_end classes associations \<C> from role \<D> end"

inductive_cases referred_by_association_class'''E [elim!]: "referred_by_association_class''' association_classes associations \<C> from \<A>"
inductive_cases referred_by_association_class''E [elim!]: "referred_by_association_class'' association_classes associations \<C> (Some from) \<A>"
inductive_cases association_class_not_closestE [elim!]: "association_class_not_closest association_classes associations \<C> from \<A> \<D>"
inductive_cases closest_association_classE [elim!]: "closest_association_class association_classes associations \<C> from \<A> \<D>"
inductive_cases closest_association_class_not_uniqueE [elim!]: "closest_association_class_not_unique association_classes associations \<C> from \<A> \<D>"
inductive_cases unique_closest_association_classE [elim!]: "unique_closest_association_class association_classes associations \<C> from \<A> \<D>"

inductive_cases association_class_end'E [elim!]: "association_class_end' association_classes associations \<A> role end"
inductive_cases association_class_end_not_uniqueE [elim!]: "association_class_end_not_unique association_classes associations \<A> role end"
inductive_cases unique_association_class_endE [elim!]: "unique_association_class_end association_classes associations \<A> role end"

inductive_cases any_operation'E [elim!]: "any_operation' operations \<tau> name \<pi> op"
inductive_cases operation'E [elim!]: "operation' operations \<tau> name \<pi> op"
inductive_cases operation_not_uniqueE [elim!]: "operation_not_unique operations \<tau> name \<pi> oper"
inductive_cases unique_operationE [elim!]: "unique_operation operations \<tau> name \<pi> oper"
inductive_cases static_operation'E [elim!]: "static_operation' operations \<tau> name \<pi> op"
inductive_cases static_operation_not_uniqueE [elim!]: "static_operation_not_unique operations \<tau> name \<pi> oper"
inductive_cases unique_static_operationE [elim!]: "unique_static_operation operations \<tau> name \<pi> oper"

inductive_cases has_literal'E [elim!]: "has_literal' literals e lit"
*)
(*** Definition *************************************************************)

subsection \<open>Definition\<close>

locale object_model =
  fixes classes :: "'a :: semilattice_sup fset"
    and attributes :: "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 't :: order"
    and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
    and association_classes :: "'a \<rightharpoonup>\<^sub>f assoc"
    and operations :: "('t, 'e) oper_spec list"
    and literals :: "'n \<rightharpoonup>\<^sub>f elit fset"
  assumes assoc_end_min_less_eq_max:
    "assoc |\<in>| fmdom associations \<Longrightarrow>
     fmlookup associations assoc = Some ends \<Longrightarrow>
     role |\<in>| fmdom ends  \<Longrightarrow>
     fmlookup ends role = Some end \<Longrightarrow>
     assoc_end_min end \<le> assoc_end_max end"
  assumes class_roles_unique:
    "class_roles classes associations \<C> from role end\<^sub>1 \<Longrightarrow>
     class_roles classes associations \<C> from role end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
begin

abbreviation "owned_attribute \<equiv>
  owned_attribute' attributes"

abbreviation "attribute \<equiv>
  unique_closest_attribute attributes"

abbreviation "owned_association_end \<equiv>
  owned_association_end' classes associations"

abbreviation "association_end \<equiv>
  unique_closest_association_end classes associations"

abbreviation "referred_by_association_class \<equiv>
  unique_closest_association_class association_classes associations"

abbreviation "association_class_end \<equiv>
  unique_association_class_end association_classes associations"

abbreviation "operation \<equiv>
  unique_operation operations"

abbreviation "static_operation \<equiv>
  unique_static_operation operations"

abbreviation "has_literal \<equiv>
  has_literal' literals"

end

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma (in object_model) attribute_det:
  "attribute \<C> attr \<D> \<tau> \<Longrightarrow>
   attribute \<C> attr \<E> \<sigma> \<Longrightarrow> \<D> = \<E> \<and> \<tau> = \<sigma>"
  by (meson closest_attribute_not_unique.intros unique_closest_attribute.cases)

lemma (in object_model) attribute_self_or_inherited:
  "attribute \<C> attr \<D> \<tau> \<Longrightarrow> \<C> \<le> \<D>"
  by (meson closest_attribute.cases unique_closest_attribute.cases)

lemma (in object_model) attribute_closest:
  "attribute \<C> attr \<D> \<tau> \<Longrightarrow>
   owned_attribute \<D>' attr \<tau> \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow> \<not> \<D>' < \<D>"
  by (meson attribute_not_closest.intros closest_attribute.cases
      unique_closest_attribute.cases)


lemma (in object_model) association_end_det:
  "association_end \<C> from role \<D>\<^sub>1 end\<^sub>1 \<Longrightarrow>
   association_end \<C> from role \<D>\<^sub>2 end\<^sub>2 \<Longrightarrow> \<D>\<^sub>1 = \<D>\<^sub>2 \<and> end\<^sub>1 = end\<^sub>2"
  by (meson closest_association_end_not_unique.intros
      unique_closest_association_end.cases)

lemma (in object_model) association_end_self_or_inherited:
  "association_end \<C> from role \<D> end \<Longrightarrow> \<C> \<le> \<D>"
  by (meson closest_association_end.cases unique_closest_association_end.cases)

lemma (in object_model) association_end_closest:
  "association_end \<C> from role \<D> end \<Longrightarrow>
   owned_association_end \<D>' from role end \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow> \<not> \<D>' < \<D>"
  by (meson association_end_not_closest.intros closest_association_end.cases
      unique_closest_association_end.cases)


lemma (in object_model) association_class_end_det:
  "association_class_end \<A> role end\<^sub>1 \<Longrightarrow>
   association_class_end \<A> role end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
  by (meson association_class_end_not_unique.intros unique_association_class_end.cases)


lemma (in object_model) operation_det:
  "operation \<tau> name \<pi> oper\<^sub>1 \<Longrightarrow>
   operation \<tau> name \<pi> oper\<^sub>2 \<Longrightarrow> oper\<^sub>1 = oper\<^sub>2"
  by (meson operation_not_unique.intros unique_operation.cases)

lemma (in object_model) static_operation_det:
  "static_operation \<tau> name \<pi> oper\<^sub>1 \<Longrightarrow>
   static_operation \<tau> name \<pi> oper\<^sub>2 \<Longrightarrow> oper\<^sub>1 = oper\<^sub>2"
  by (meson static_operation_not_unique.intros unique_static_operation.cases)

(*** Code Setup *************************************************************)

subsection \<open>Code Setup\<close>

lemma fmember_code_predI [code_pred_intro]:
  "x |\<in>| xs" if "Predicate_Compile.contains (fset xs) x"
  using that by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

code_pred fmember
  by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

code_pred [show_modes] unique_closest_attribute .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] class_roles .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] owned_association_end' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] closest_association_end .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool ) [show_modes] closest_association_end_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] unique_closest_association_end .

code_pred [show_modes] unique_closest_association_class .

code_pred [show_modes] association_class_end' .

code_pred [show_modes] association_class_end_not_unique .

code_pred  [show_modes] unique_association_class_end .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] any_operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) [show_modes] operation_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] unique_operation .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] static_operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) [show_modes] static_operation_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] unique_static_operation .

code_pred [show_modes] has_literal' .

end

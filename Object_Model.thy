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

definition "assoc_end_class \<equiv> fst"
definition "assoc_end_min \<equiv> fst \<circ> snd"
definition "assoc_end_max \<equiv> fst \<circ> snd \<circ> snd"
definition "assoc_end_ordered \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_unique \<equiv> snd \<circ> snd \<circ> snd \<circ> snd"

definition "oper_name \<equiv> fst"
definition "oper_context \<equiv> fst \<circ> snd"
definition "oper_params \<equiv> fst \<circ> snd \<circ> snd"
definition "oper_result \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "oper_static \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
definition "oper_body \<equiv> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

definition "param_name \<equiv> fst"
definition "param_type \<equiv> fst \<circ> snd"
definition "param_dir \<equiv> snd \<circ> snd"

definition "oper_in_params op \<equiv>
  filter (\<lambda>p. param_dir p = In \<or> param_dir p = InOut) (oper_params op)"

definition "oper_out_params op \<equiv>
  filter (\<lambda>p. param_dir p = Out \<or> param_dir p = InOut) (oper_params op)"

text \<open>
  The following predicates allows one to access class attributes.\<close>

inductive owned_attribute' where
 "fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
  fmlookup attrs\<^sub>\<C> attr = Some \<tau> \<Longrightarrow>
  owned_attribute' attributes \<C> attr \<tau>"

inductive class_has_attribute' where
 "owned_attribute' attributes \<C> attr \<tau> \<Longrightarrow>
  class_has_attribute' attributes \<C> attr"

inductive attribute' where
 "Least (\<lambda>\<D>. \<C> \<le> \<D> \<and> class_has_attribute' attributes \<D> attr) = \<D> \<Longrightarrow>
  owned_attribute' attributes \<D> attr \<tau> \<Longrightarrow>
  attribute' attributes \<C> attr \<D> \<tau>"

text \<open>
  The following predicates allows one to access association ends.\<close>

inductive role_refer_class where
  "role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = \<C> \<Longrightarrow>
   role_refer_class ends \<C> role"

inductive class_roles where
  "assoc |\<in>| fmdom associations \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   role_refer_class ends \<C> from \<Longrightarrow>
   role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   class_roles associations \<C> from role end"

inductive owned_association_end' where
  "class_roles associations \<C> from role end \<Longrightarrow>
   owned_association_end' associations \<C> None role end"
| "class_roles associations \<C> from role end \<Longrightarrow>
   owned_association_end' associations \<C> (Some from) role end"

inductive class_is_association_source' where
  "owned_association_end' associations \<C> from role end \<Longrightarrow>
   class_is_association_source' associations \<C> from role"

inductive association_end' where
  "Least (\<lambda>\<D>. \<C> \<le> \<D> \<and> class_is_association_source' associations \<D> from role) = \<D> \<Longrightarrow>
   owned_association_end' associations \<D> from role end \<Longrightarrow>
   association_end' associations \<C> from role \<D> end"

inductive association_end_not_unique where
  "association_end' associations \<C> from role \<D>' end' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<or> end \<noteq> end' \<Longrightarrow>
   association_end_not_unique associations \<C> from role \<D> end"

inductive unique_association_end where
  "association_end' associations \<C> from role \<D> end \<Longrightarrow>
   \<not> association_end_not_unique associations \<C> from role \<D> end \<Longrightarrow>
   unique_association_end associations \<C> from role \<D> end"

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

inductive referred_by_association_class' where
  "Least (\<lambda>\<D>. \<C> \<le> \<D> \<and> referred_by_association_class''
      association_classes associations \<D> from \<A>) = \<D> \<Longrightarrow>
   referred_by_association_class' association_classes associations \<C> from \<A>"

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

(*** Definition *************************************************************)

subsection \<open>Definition\<close>

locale object_model =
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 't :: order"
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
    "class_roles associations \<C> from role end\<^sub>1 \<Longrightarrow>
     class_roles associations \<C> from role end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
begin

abbreviation "attribute \<equiv> attribute' attributes"
abbreviation "association_end \<equiv> unique_association_end associations"
abbreviation "referred_by_association_class \<equiv>
  referred_by_association_class' association_classes associations"
abbreviation "association_class_end \<equiv>
  unique_association_class_end association_classes associations"
abbreviation "operation \<equiv> unique_operation operations"
abbreviation "static_operation \<equiv> unique_static_operation operations"
abbreviation "has_literal \<equiv> has_literal' literals"

end

(*** Determinism ************************************************************)

subsection \<open>Determinism\<close>

lemma owned_attribute'_det:
  "owned_attribute' attributes \<C> attr \<tau> \<Longrightarrow>
   owned_attribute' attributes \<C> attr \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  by (elim owned_attribute'.cases; auto)

lemma (in object_model) attribute_det:
  "attribute \<C> attr \<D> \<tau> \<Longrightarrow>
   attribute \<C> attr \<E> \<sigma> \<Longrightarrow> \<D> = \<E> \<and> \<tau> = \<sigma>"
  by (elim attribute'.cases; auto simp add: owned_attribute'_det)

lemma (in object_model) association_end_det:
  "association_end \<C> from role \<D>\<^sub>1 end\<^sub>1 \<Longrightarrow>
   association_end \<C> from role \<D>\<^sub>2 end\<^sub>2 \<Longrightarrow> \<D>\<^sub>1 = \<D>\<^sub>2 \<and> end\<^sub>1 = end\<^sub>2"
  by (meson association_end_not_unique.intros unique_association_end.cases)

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

code_pred [show_modes] attribute' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] class_roles .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] owned_association_end' .

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
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] association_end' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) [show_modes] association_end_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] unique_association_end .

code_pred [show_modes] referred_by_association_class' .

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

(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Object Model\label{sec:object-model}\<close>
theory Object_Model
  imports "HOL-Library.Extended_Nat" Finite_Map_Ext
    OCL_Types (*"HOL-Library.Transitive_Closure_Table"*)
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
(*type_synonym enum = String.literal*)
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

inductive the_association_end' where
  "The (\<lambda>(\<D>, end). association_end' associations \<C> from role \<D> end) = (\<D>, end) \<Longrightarrow>
   the_association_end' associations \<C> from role \<D> end"


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

inductive association_class_end' where
  "fmlookup association_classes \<A> = Some assoc \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   association_class_end' association_classes associations \<A> role end"

inductive the_association_class_end' where
  "The (\<lambda>end. association_class_end' association_classes associations \<A> role end) = end \<Longrightarrow>
   the_association_class_end' association_classes associations \<A> role end"


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

inductive static_operation' where
  "any_operation' operations \<tau> name \<pi> op \<Longrightarrow>
   oper_static op \<Longrightarrow>
   static_operation' operations \<tau> name \<pi> op"

inductive the_operation' where
  "The (\<lambda>oper. operation' operations \<tau> op \<pi> oper) = oper \<Longrightarrow>
   the_operation' operations \<tau> op \<pi> oper"

inductive the_static_operation' where
  "The (\<lambda>oper. static_operation' operations \<tau> op \<pi> oper) = oper \<Longrightarrow>
   the_static_operation' operations \<tau> op \<pi> oper"


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
abbreviation "association_end \<equiv> the_association_end' associations"
abbreviation "referred_by_association_class \<equiv>
  referred_by_association_class' association_classes associations"
abbreviation "association_class_end \<equiv>
  the_association_class_end' association_classes associations"
abbreviation "operation \<equiv> the_operation' operations"
abbreviation "static_operation \<equiv> the_static_operation' operations"
abbreviation "has_literal \<equiv> has_literal' literals"

lemma owned_attribute'_det:
  "owned_attribute' attributes \<C> attr \<tau> \<Longrightarrow>
   owned_attribute' attributes \<C> attr \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  by (elim owned_attribute'.cases; auto)

lemma attribute_det:
  "attribute' attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   attribute' attributes \<C> attr \<E> \<sigma> \<Longrightarrow> \<D> = \<E> \<and> \<tau> = \<sigma>"
  by (elim attribute'.cases; auto simp add: owned_attribute'_det)

end

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

lemma the_association_end'_code_predI [code_pred_intro]:
  "Predicate.the (association_end'_i_i_i_i_o_o associations \<C> from role) = (\<D>, end) \<Longrightarrow>
   the_association_end' associations \<C> from role \<D> end"
  by (simp add: Predicate.the_def the_association_end'.simps
       association_end'_i_i_i_i_o_o_def)

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) [show_modes] the_association_end'
  by (metis Predicate.the_def association_end'_i_i_i_i_o_o_def pred.sel the_association_end'.cases)

code_pred [show_modes] referred_by_association_class' .

code_pred [show_modes] association_class_end' .

lemma the_association_class_end'_code_predI [code_pred_intro]:
  "Predicate.the (association_class_end'_i_i_i_i_o association_classes associations \<A> role) = end \<Longrightarrow>
   the_association_class_end' association_classes associations \<A> role end"
  by (simp add: Predicate.the_def the_association_class_end'.simps
       association_class_end'_i_i_i_i_o_def)

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] the_association_class_end'
  by (metis the_association_class_end'.cases the_association_class_end'_code_predI)

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] any_operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] operation' .

lemma the_operation'_code_predI [code_pred_intro]:
  "Predicate.the (operation'_i_i_i_i_o operations \<tau> op \<pi>) = oper \<Longrightarrow>
   the_operation' operations \<tau> op \<pi> oper"
  by (simp add: Predicate.the_def the_operation'.simps
       operation'_i_i_i_i_o_def)

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] the_operation'
  by (metis the_operation'.cases the_operation'_code_predI)

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] static_operation' .

lemma the_static_operation'_code_predI [code_pred_intro]:
  "Predicate.the (static_operation'_i_i_i_i_o operations \<tau> op \<pi>) = oper \<Longrightarrow>
   the_static_operation' operations \<tau> op \<pi> oper"
  by (simp add: Predicate.the_def the_static_operation'.simps
       static_operation'_i_i_i_i_o_def)

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] the_static_operation'
  by (metis the_static_operation'.cases the_static_operation'_code_predI)

code_pred [show_modes] has_literal' .

(*
(*** Classes ****************************************************************)

section \<open>Classes\<close>

datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

inductive subclass1 where
  "c \<noteq> Object \<Longrightarrow>
   subclass1 c Object"
| "subclass1 Employee Person"
| "subclass1 Customer Person"

code_pred subclass1 .

instantiation classes1 :: semilattice_sup
begin

definition "(<) \<equiv> subclass1"
definition "(\<le>) \<equiv> subclass1\<^sup>=\<^sup>="

notation sup (infixl "\<squnion>" 65)

fun sup_classes1 where
  "Object \<squnion> _ = Object"
| "Person \<squnion> c = (if c = Person \<or> c = Employee \<or> c = Customer
    then Person else Object)"
| "Employee \<squnion> c = (if c = Employee then Employee else
    if c = Person \<or> c = Customer then Person else Object)"
| "Customer \<squnion> c = (if c = Customer then Customer else
    if c = Person \<or> c = Employee then Person else Object)"
| "Project \<squnion> c = (if c = Project then Project else Object)"
| "Task \<squnion> c = (if c = Task then Task else Object)"
| "Sprint \<squnion> c = (if c = Sprint then Sprint else Object)"

lemma less_le_not_le_classes1:
  "c < d \<longleftrightarrow> c \<le> d \<and> \<not> d \<le> c"
  for c d :: classes1
  unfolding less_classes1_def less_eq_classes1_def
  using subclass1.simps by auto

lemma order_refl_classes1:
  "c \<le> c"
  for c :: classes1
  unfolding less_eq_classes1_def by simp

lemma order_trans_classes1:
  "c \<le> d \<Longrightarrow> d \<le> e \<Longrightarrow> c \<le> e"
  for c d e :: classes1
  unfolding less_eq_classes1_def
  using subclass1.simps by auto

lemma antisym_classes1:
  "c \<le> d \<Longrightarrow> d \<le> c \<Longrightarrow> c = d"
  for c d :: classes1
  unfolding less_eq_classes1_def
  using subclass1.simps by auto

lemma sup_ge1_classes1:
  "c \<le> c \<squnion> d"
  for c d :: classes1
  by (induct c; auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

lemma sup_ge2_classes1:
  "d \<le> c \<squnion> d"
  for c d :: classes1
  by (induct c; auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

lemma sup_least_classes1:
  "c \<le> e \<Longrightarrow> d \<le> e \<Longrightarrow> c \<squnion> d \<le> e"
  for c d e :: classes1
  by (induct c; induct d;
      auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_classes1)
  apply (simp add: order_refl_classes1)
  apply (rule order_trans_classes1; auto)
  apply (simp add: antisym_classes1)
  apply (simp add: sup_ge1_classes1)
  apply (simp add: sup_ge2_classes1)
  apply (simp add: sup_least_classes1)
  done

end

instantiation classes1 :: enum
begin

definition [simp]: "enum_classes1 \<equiv>
  [Object, Person, Employee, Customer, Project, Task, Sprint]"

definition [simp]: "enum_all_classes1 P \<equiv>
  P Object \<and> P Person \<and> P Employee \<and> P Customer \<and> P Project \<and> P Task \<and> P Sprint"

definition [simp]: "enum_ex_classes1 P \<equiv>
  P Object \<or> P Person \<or> P Employee \<or> P Customer \<or> P Project \<or> P Task \<or> P Sprint" 

instance
  apply intro_classes
  apply auto
  by (metis classes1.exhaust)+

end

abbreviation "assocs \<equiv> [
  STR ''ProjectManager'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0::nat, \<infinity>::enat, False, True),
    STR ''manager'' \<mapsto>\<^sub>f (Employee, 1, 1, False, False)],
  STR ''ProjectMember'' \<mapsto>\<^sub>f [
    STR ''member_of'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, False),
    STR ''members'' \<mapsto>\<^sub>f (Employee, 1, 20, True, True)],
  STR ''ManagerEmployee'' \<mapsto>\<^sub>f [
    STR ''line_manager'' \<mapsto>\<^sub>f (Employee, 0::nat, 1, False, False),
    STR ''project_manager'' \<mapsto>\<^sub>f (Employee, 0::nat, \<infinity>, False, False),
    STR ''employees'' \<mapsto>\<^sub>f (Employee, 3, 7, False, False)],
  STR ''ProjectCustomer'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, True),
    STR ''customer'' \<mapsto>\<^sub>f (Customer, 1, 1, False, False)],
  STR ''ProjectTask'' \<mapsto>\<^sub>f [
    STR ''project'' \<mapsto>\<^sub>f (Project, 1, 1, False, False),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, \<infinity>, True, True)],
  STR ''SprintTaskAssignee'' \<mapsto>\<^sub>f [
    STR ''sprint'' \<mapsto>\<^sub>f (Sprint, 0, 10, False, True),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, 5, False, True),
    STR ''assignee'' \<mapsto>\<^sub>f (Employee, 0, 1, False, False)]]"
(*
definition "operations_classes1 \<equiv> [
  (STR ''membersCount'', Person, [], 1::nat, False, None :: nat option),
  (STR ''membersByName'', Project, [(STR ''mn'', 1::nat, In)], 1, False, None),
  (STR ''allProjects'', Project, [], 1, True, None)
  ]"
*)
declare [[coercion "ObjectType :: classes1 \<Rightarrow> classes1 basic_type"]]

definition "operations_classes1 \<equiv> [
  (STR ''membersCount'', Project[1], [], Integer[1], False, None),
  (STR ''membersByName'', Project[1], [(STR ''mn'', String[1], In)], Set Employee[1], False, None),
  (STR ''allProjects'', Project[1], [], Set Project[1], True, None)
  ] :: (classes1 type, nat) oper_spec list"


value "any_operation' operations_classes1 Employee[1] STR ''membersCount'' [] (STR ''membersCount'', Project[1], [], Integer[1], False, None)"
values "{op. any_operation' operations_classes1 Employee[1] STR ''membersCount'' [] op}"
*)

end

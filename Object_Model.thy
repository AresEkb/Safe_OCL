(*  Title:       Safe OCL
    Author:      Denis Nikiforov, February 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Object Model\label{sec:object-model}\<close>
theory Object_Model
  imports "HOL-Library.Extended_Nat" Finite_Map_Ext
begin

text \<open>
  This theory defines a very simplified object model. It does not
  support attribute and operation redefinition.
  It does not define any constraints either.\<close>

type_synonym attr = String.literal
type_synonym assoc = String.literal
type_synonym role = String.literal
type_synonym oper = String.literal
type_synonym param = String.literal
type_synonym enum = String.literal
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

definition "role_refer_class ends \<C> role \<equiv>
  assoc_end_class (the (fmlookup ends role)) = \<C>"

definition "assoc_refer_class ends \<C> \<equiv>
  fBex (fmdom ends) (role_refer_class ends \<C>)"

definition "assoc_refer_role ends role \<equiv> fmlookup ends role \<noteq> None"

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

(* We define all functions with (<) or (\<le>) as abbreviations.
   In other case we will get errors related to code generator *)
abbreviation "has_matching_signature \<tau> op \<pi> x \<equiv>
  op = oper_name x \<and> \<tau> \<le> oper_context x \<and>
  list_all2 (\<lambda>x y. x \<le> y) \<pi> (map param_type (oper_in_params x))"













(*
datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

inductive subclass1 where
  "c \<noteq> Object \<Longrightarrow>
   subclass1 c Object"
| "subclass1 Employee Person"
| "subclass1 Customer Person"

code_pred subclass1 .

notation sup (infixl "\<squnion>" 65)

instantiation classes1 :: semilattice_sup
begin

definition "(<) \<equiv> subclass1"
definition "(\<le>) \<equiv> subclass1\<^sup>=\<^sup>="

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

value "LEAST x. Employee \<le> x"
value "LEAST x. x \<in> {Person, Project}"
value "GREATEST x. x \<in> {Person, Project}"
value "GREATEST x. x \<in> {Person, Employee}"
value "Sup {Person, Employee}"
value "GREATEST x. Employee < x"
term Inf
term Sup
value "Inf {A,B}"
*)

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

lemma fmember_code_predI [code_pred_intro]:
  "x |\<in>| xs" if "Predicate_Compile.contains (fset xs) x"
  using that by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

code_pred fmember
  by (simp add: Predicate_Compile.contains_def fmember.rep_eq)
(*
inductive owned_association_end'' where
 "role \<noteq> from \<Longrightarrow>
  assoc |\<in>| fmdom associations \<Longrightarrow>
  fmlookup associations assoc = Some ends \<Longrightarrow>
  fmlookup ends role = Some end \<Longrightarrow>
  fmlookup ends from = Some from_end \<Longrightarrow>
  assoc_end_class from_end = \<C> \<Longrightarrow>
  owned_association_end'' associations \<C> role from end"
*)
inductive owned_association_end' where
  "assoc |\<in>| fmdom associations \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   fmlookup ends from = Some from_end \<Longrightarrow>
   \<C> = assoc_end_class from_end \<Longrightarrow>
   from |\<in>| fmdom ends \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   owned_association_end' associations \<C> role None end"
| "assoc |\<in>| fmdom associations \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   fmlookup ends from = Some from_end \<Longrightarrow>
   \<C> = assoc_end_class from_end \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   owned_association_end' associations \<C> role (Some from) end"

code_pred [show_modes] owned_association_end' .


(*
lemma owned_association_end'_det:
  "owned_association_end' assocs \<C> role from end\<^sub>1 \<Longrightarrow>
   owned_association_end' assocs \<C> role from end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
  nitpick
  apply (elim owned_association_end'.cases; auto)
*)

inductive class_is_association_source' where
  "owned_association_end' associations \<C> role from end \<Longrightarrow>
   class_is_association_source' associations \<C> role from"

code_pred [show_modes] class_is_association_source' .

inductive association_end' where
 "Least (\<lambda>\<D>. \<C> \<le> \<D> \<and> class_is_association_source' associations \<D> role from) = \<D> \<Longrightarrow>
  owned_association_end' associations \<D> role from end \<Longrightarrow>
  association_end' associations \<C> role from end"

code_pred [show_modes] association_end' .

(*
definition "role_refer_class ends \<C> role \<equiv>
  assoc_end_class (the (fmlookup ends role)) = \<C>"

definition "assoc_refer_class ends \<C> \<equiv>
  fBex (fmdom ends) (role_refer_class ends \<C>)"

definition "assoc_refer_role ends role \<equiv> fmlookup ends role \<noteq> None"

abbreviation "find_associations \<C> role from \<equiv>
  fmfilter (\<lambda>assoc.
    case fmlookup associations assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      (case from
        of None \<Rightarrow> assoc_refer_class (fmdrop role ends) \<C>
         | Some from_role \<Rightarrow> role_refer_class ends \<C> from_role) \<and>
      assoc_refer_role ends role) associations"

abbreviation "find_owned_association_end \<C> role from \<equiv>
  let found = fmran (find_associations \<C> role from) in
  if fcard found = 1 then fmlookup (fthe_elem found) role else None"

abbreviation "find_association_end \<C> role from \<equiv>
  let found = Option.these {find_owned_association_end \<D> role from | \<D>. \<C> \<le> \<D>} in
  if card found = 1 then Some (the_elem found) else None"
*)



code_pred attribute' .

locale object_model = 
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 't :: order"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and association_classes :: "'a \<rightharpoonup>\<^sub>f assoc"
  and operations :: "('t, 'e) oper_spec list"
  and literals :: "'n \<rightharpoonup>\<^sub>f elit fset"
  assumes owned_association_end_det:
  "owned_association_end' associations \<C> role from end\<^sub>1 \<Longrightarrow>
   owned_association_end' associations \<C> role from end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
begin

abbreviation "attribute \<equiv> attribute' attributes"
abbreviation "association_end \<equiv> association_end' associations"

(*
abbreviation "find_owned_attribute \<C> attr \<equiv>
  map_option (Pair \<C>) (Option.bind (fmlookup attributes \<C>) (\<lambda>attrs\<^sub>\<C>. fmlookup attrs\<^sub>\<C> attr))"

abbreviation "find_attribute \<C> attr \<equiv>
  let found = {(\<D>, \<tau>). \<C> \<le> \<D> \<and> attribute \<C> attr (\<D>, \<tau>)} in
  if card found = 1 then Some (the_elem found) else None"
(*
abbreviation "find_attribute \<C> attr \<equiv>
  let found = Option.these {find_owned_attribute \<D> attr | \<D>. \<C> \<le> \<D>} in
  if card found = 1 then Some (the_elem found) else None"
*)
lemma owned_attribute_code [code_abbrev, simp]:
  "find_owned_attribute \<C> attr = Some (\<C>, \<tau>) \<longleftrightarrow>
   owned_attribute \<C> attr (\<C>, \<tau>)"
proof
  show
    "find_owned_attribute \<C> attr = Some (\<C>, \<tau>) \<Longrightarrow>
     owned_attribute \<C> attr (\<C>, \<tau>)"
    unfolding Option.map_conv_bind_option Option.bind_eq_Some_conv
    by (auto simp add: owned_attribute.intros)
  show
    "owned_attribute \<C> attr (\<C>, \<tau>) \<Longrightarrow>
     find_owned_attribute \<C> attr = Some (\<C>, \<tau>)"
    by (erule owned_attribute.cases; simp)
qed

lemma attribute_code' [code_abbrev, simp]:
  "Option.these {find_owned_attribute \<D> attr | \<D>. \<C> \<le> \<D>} =
   {(\<D>, \<tau>). \<C> \<le> \<D> \<and> attribute \<C> attr (\<D>, \<tau>)}"
proof
  have "\<And>\<C> \<D> \<D>' \<tau>.
     Some (\<D>', \<tau>) = find_owned_attribute \<D> attr \<Longrightarrow> \<C> \<le> \<D> \<Longrightarrow> \<C> \<le> \<D>'"
    by (metis fst_conv map_option_eq_Some)
  thus
    "Option.these {find_owned_attribute \<D> attr |\<D>. \<C> \<le> \<D>} \<subseteq>
     {(\<D>, \<tau>). \<C> \<le> \<D> \<and> attribute \<C> attr (\<D>, \<tau>)}"
    apply (auto simp add: in_these_eq)
    apply (rule attribute.intros, simp)
    by (metis (mono_tags, lifting) fst_conv
        map_option_eq_Some owned_attribute_code)
  show
    "{(\<D>, \<tau>). \<C> \<le> \<D> \<and> attribute \<C> attr (\<D>, \<tau>)} \<subseteq>
     Option.these {find_owned_attribute \<D> attr |\<D>. \<C> \<le> \<D>}"
    apply (auto simp add: in_these_eq)
    by (metis attribute.cases owned_attribute_code)
qed

lemma attribute_code'':
  "{(\<D>, \<tau>). \<C> \<le> \<D> \<and> attribute \<C> attr (\<D>, \<tau>)} =
   Option.these {find_owned_attribute \<D> attr | \<D>. \<C> \<le> \<D>}"
  by simp

lemma attribute_code [code_abbrev, simp]:
  "(find_attribute \<C> attr = Some (\<D>, \<tau>)) =
   attribute \<C> attr (\<D>, \<tau>)"
proof
  show
    "find_attribute \<C> attr = Some (\<D>, \<tau>) \<Longrightarrow>
     attribute \<C> attr (\<D>, \<tau>)"
    apply (auto simp add: Let_def split: if_splits)
    unfolding attribute_code''
    apply (auto simp add: Let_def Option.these_def split: if_splits)
    apply (rule attribute.intros)
    by (auto simp add: owned_attribute.intros)
  show
    "attribute \<C> attr (\<D>, \<tau>) \<Longrightarrow>
     find_attribute \<C> attr = Some (\<D>, \<tau>)"
    apply (erule attribute.cases)
    apply (auto simp add: Let_def split: if_split)
qed
*)
abbreviation "find_associations \<C> role from \<equiv>
  fmfilter (\<lambda>assoc.
    case fmlookup associations assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      (case from
        of None \<Rightarrow> assoc_refer_class (fmdrop role ends) \<C>
         | Some from_role \<Rightarrow> role_refer_class ends \<C> from_role) \<and>
      assoc_refer_role ends role) associations"

abbreviation "find_owned_association_end \<C> role from \<equiv>
  let found = fmran (find_associations \<C> role from) in
  if fcard found = 1 then fmlookup (fthe_elem found) role else None"

abbreviation "find_association_end \<C> role from \<equiv>
  let found = Option.these {find_owned_association_end \<D> role from | \<D>. \<C> \<le> \<D>} in
  if card found = 1 then Some (the_elem found) else None"

abbreviation "referred_by_association_class \<C> \<A> from \<equiv>
  case fmlookup association_classes \<A> of None \<Rightarrow> False | Some assoc \<Rightarrow>
    (case fmlookup associations assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      (\<exists>\<D>. \<C> \<le> \<D> \<and>
        (case from
          of None \<Rightarrow> assoc_refer_class ends \<D>
           | Some from_role \<Rightarrow> role_refer_class ends \<D> from_role)))"

abbreviation "find_association_class_end \<A> role \<equiv>
  case fmlookup association_classes \<A> of None \<Rightarrow> None | Some assoc \<Rightarrow>
    (case fmlookup associations assoc of None \<Rightarrow> None | Some ends \<Rightarrow>
      fmlookup ends role)"

abbreviation "find_operation \<tau> op \<pi> \<equiv>
  find (\<lambda>x. has_matching_signature \<tau> op \<pi> x \<and> \<not> oper_static x) operations"

abbreviation "find_static_operation \<tau> op \<pi> \<equiv>
  find (\<lambda>x. has_matching_signature \<tau> op \<pi> x \<and> oper_static x) operations"

abbreviation "has_literal e lit \<equiv>
  (case fmlookup literals e
    of Some lits \<Rightarrow> lit |\<in>| lits
     | None \<Rightarrow> False)"

end

end

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

locale object_model = 
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 't :: order"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and association_classes :: "'a \<rightharpoonup>\<^sub>f assoc"
  and operations :: "('t, 'e) oper_spec list"
  and literals :: "'n \<rightharpoonup>\<^sub>f elit fset"
begin

inductive owned_attribute where
 "fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
  fmlookup attrs\<^sub>\<C> attr = Some \<tau> \<Longrightarrow>
  owned_attribute \<C> attr (\<C>, \<tau>)"

inductive attribute where
 "\<C> \<le> \<D> \<Longrightarrow>
  owned_attribute \<D> attr (\<D>, \<tau>) \<Longrightarrow>
  attribute \<C> attr (\<D>, \<tau>)"

abbreviation "find_owned_attribute \<C> attr \<equiv>
  map_option (Pair \<C>) (Option.bind (fmlookup attributes \<C>) (\<lambda>attrs\<^sub>\<C>. fmlookup attrs\<^sub>\<C> attr))"

abbreviation "find_attribute \<C> attr \<equiv>
  let found = Option.these {find_owned_attribute \<D> attr | \<D>. \<C> \<le> \<D>} in
  if card found = 1 then Some (the_elem found) else None"

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

lemma attribute_code [code_abbrev, simp]:
  "(find_attribute \<C> attr = Some (\<D>, \<tau>)) =
   attribute \<C> attr (\<D>, \<tau>)"
proof
  show
    "find_attribute \<C> attr = Some (\<D>, \<tau>) \<Longrightarrow>
     attribute \<C> attr (\<D>, \<tau>)"
    unfolding Let_def
    by (auto simp add: owned_attribute.intros)
  show
    "attribute \<C> attr (\<D>, \<tau>) \<Longrightarrow>
     find_attribute \<C> attr = Some (\<D>, \<tau>)"
    apply (erule attribute.cases)
    apply (auto simp add: Let_def split: if_split)
    unfolding Let_def
qed

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

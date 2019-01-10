(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Object Model\<close>
theory Object_Model
  imports OCL_Types "HOL-Library.Extended_Nat" "HOL-Library.Finite_Map"
begin

type_synonym 'a attrs = "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
type_synonym 'a assoc_end = "'a \<times> nat \<times> enat"
type_synonym 'a assocs = "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"

datatype parameter_mode = In | Out | InOut

definition assoc_end_class :: "'a assoc_end \<Rightarrow> 'a" where
  "assoc_end_class \<equiv> fst"

definition assoc_end_min :: "'a assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd"

definition assoc_end_max :: "'a assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd"

definition assoc_end_type :: "'a assoc_end \<Rightarrow> 'a type" where
  "assoc_end_type end \<equiv>
    let cls = assoc_end_class end in
    if assoc_end_max end \<le> 1 then
      if assoc_end_min end = 0
        then (ObjectType cls)[?]
        else (ObjectType cls)[1]
    else Set (ObjectType cls)[1]"

definition assoc_end_min_le_max :: "'a assoc_end \<Rightarrow> bool" where
  "assoc_end_min_le_max end \<equiv> assoc_end_min end \<le> assoc_end_max end"

definition assoc_refer_role :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_role ends role \<equiv> fmlookup ends role \<noteq> None"

text \<open>
  The OCL specification allows attribute redefinition with the same type.
  But we prohibit it.\<close>

locale object_model = semilattice_sup +
  fixes attributes :: "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'b"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  assumes attributes_distinct:
    "less \<C> \<D> \<Longrightarrow>
     fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
     fmlookup attributes \<D> = Some attrs\<^sub>\<D> \<Longrightarrow>
     fmlookup attrs\<^sub>\<C> attr \<noteq> None \<Longrightarrow>
     fmlookup attrs\<^sub>\<D> attr = None"
begin

abbreviation "find_owned_attribute \<C> attr \<equiv>
  map_option (\<lambda>\<tau>. (\<C>, \<tau>)) (Option.bind (fmlookup attributes \<C>) (\<lambda>attrs\<^sub>\<C>. fmlookup attrs\<^sub>\<C> attr))"

abbreviation "find_attribute \<C> attr \<equiv>
  let found = Option.these {find_owned_attribute \<D> attr | \<D>. less_eq \<C> \<D>} in
  if card found = 1 then Some (the_elem found) else None"

abbreviation "assoc_refer_class ends \<C> \<equiv>
  fBex (fmdom ends) (\<lambda>role. assoc_end_class (the (fmlookup ends role)) = \<C>)"

abbreviation "find_associations \<C> role \<equiv>
  fmfilter (\<lambda>assoc.
    case fmlookup associations assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      assoc_refer_class (fmdrop role ends) \<C> \<and> assoc_refer_role ends role) associations"

abbreviation "find_owned_association_end \<C> role \<equiv>
  let found = fmran (find_associations \<C> role) in
  if fcard found = 1 then fmlookup (fthe_elem found) role else None"

abbreviation "find_association_end \<C> role \<equiv>
  let found = Option.these {find_owned_association_end \<D> role | \<D>. less_eq \<C> \<D>} in
  if card found = 1 then Some (the_elem found) else None"

end

(*
  Maybe the following inductive definitions will be used in future.

inductive find_attribute where
  "\<C> \<le> \<D> \<Longrightarrow>
   fmlookup attrs \<D> = Some attrs\<^sub>\<D> \<Longrightarrow>
   fmlookup attrs\<^sub>\<D> attr = Some \<tau> \<Longrightarrow>
   find_attribute attrs \<C> attr \<D> \<tau>"

inductive find_association where
  "cls \<le> cls2 \<Longrightarrow>
   assoc_name |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc_name = Some assoc \<Longrightarrow>
   fmlookup assoc role = Some end \<Longrightarrow>
   from_role |\<in>| fmdom assoc \<Longrightarrow>
   from_role \<noteq> role \<Longrightarrow>
   fmlookup assoc from_role = Some from_end \<Longrightarrow>
   assoc_end_class from_end = cls2 \<Longrightarrow>
   find_association assocs cls role cls2 end"
*)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>
(*
definition "attrs_ok_fun attrs \<equiv> \<nexists>\<C> \<D>.
  \<C> < \<D> \<and>
  (case (fmlookup attrs \<C>, fmlookup attrs \<D>)
    of (Some attrs\<^sub>\<C>, Some attrs\<^sub>\<D>) \<Rightarrow>
      fBex (fmdom attrs\<^sub>\<C>) (\<lambda>attr.
        fmlookup attrs\<^sub>\<C> attr \<noteq> None \<and>
        fmlookup attrs\<^sub>\<D> attr \<noteq> None)
    | _ \<Rightarrow> False)"

lemma attrs_ok_code [code_abbrev, simp]:
  "attrs_ok_fun attrs = attrs_ok attrs"
proof
  show "attrs_ok_fun attrs \<Longrightarrow> attrs_ok attrs"
    unfolding attrs_ok_fun_def attrs_ok_def option.case_eq_if
    apply auto
    by (smt fBexI fmdomI fmdom_notD fmdom_notI option.sel)
  show "attrs_ok attrs \<Longrightarrow> attrs_ok_fun attrs"
    unfolding attrs_ok_fun_def attrs_ok_def option.case_eq_if
    by auto
qed
*)
(*
code_pred [show_modes] find_attribute .

lemma fmember_code_predI [code_pred_intro]:
  "Predicate_Compile.contains (fset xs) x \<Longrightarrow> x |\<in>| xs"
  by (meson Predicate_Compile.containsE notin_fset)

code_pred [show_modes] fmember
  by (simp add: Predicate_Compile.containsI fmember.rep_eq)

code_pred [show_modes] find_association .
*)

end

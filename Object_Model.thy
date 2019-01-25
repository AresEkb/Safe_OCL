(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Object Model\<close>
theory Object_Model
  imports "HOL-Library.Extended_Nat" "HOL-Library.Finite_Map"
begin

type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)

type_synonym attr = String.literal
type_synonym assoc = String.literal
type_synonym role = String.literal
type_synonym oper = String.literal
type_synonym param = String.literal

datatype param_dir = In | Out | InOut

type_synonym 'c assoc_end = "'c \<times> nat \<times> enat \<times> bool \<times> bool"
type_synonym 't param_spec = "param \<times> 't \<times> param_dir"
type_synonym ('t, 'e) oper_spec = "oper \<times> 't param_spec list \<times> 't \<times> 'e option"

definition "assoc_end_class \<equiv> fst"
definition "assoc_end_min \<equiv> fst \<circ> snd"
definition "assoc_end_max \<equiv> fst \<circ> snd \<circ> snd"
definition "assoc_end_ordered \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_unique \<equiv> snd \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_min_le_max end \<equiv> assoc_end_min end \<le> assoc_end_max end"

definition "oper_name \<equiv> fst"
definition "oper_params \<equiv> fst \<circ> snd"
definition "oper_result \<equiv> fst \<circ> snd \<circ> snd"
definition "oper_body \<equiv> snd \<circ> snd \<circ> snd"

definition "param_name \<equiv> fst"
definition "param_type \<equiv> fst \<circ> snd"
definition "param_dir \<equiv> snd \<circ> snd"

definition "assoc_refer_class ends \<C> \<equiv>
  fBex (fmdom ends) (\<lambda>role. assoc_end_class (the (fmlookup ends role)) = \<C>)"

definition "assoc_refer_role ends role \<equiv> fmlookup ends role \<noteq> None"

definition "oper_in_params op \<equiv>
  filter (\<lambda>p. param_dir p = In \<or> param_dir p = InOut) (oper_params op)"

definition "oper_out_params op \<equiv>
  filter (\<lambda>p. param_dir p = Out \<or> param_dir p = InOut) (oper_params op)"

text \<open>
  The OCL specification allows attribute redefinition with the same type.
  But we prohibit it.\<close>

locale object_model = 
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 't :: order"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and operations :: "('t, 'e) oper_spec list"
  assumes attributes_distinct:
    "\<C> < \<D> \<Longrightarrow>
     fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
     fmlookup attributes \<D> = Some attrs\<^sub>\<D> \<Longrightarrow>
     fmlookup attrs\<^sub>\<C> attr \<noteq> None \<Longrightarrow>
     fmlookup attrs\<^sub>\<D> attr = None"
begin

(*
abbreviation "oper_out_params op \<equiv>
  filter (\<lambda>p. param_dir p = Out \<or> param_dir p = InOut) (oper_params op) @
  [(STR ''result'', oper_result op, Out)]"

abbreviation "oper_type op \<equiv>
  let params = oper_out_params op in
  if length params = 0
    then oper_result op
    else Tuple (fmap_of_list (map (\<lambda>p. (param_name p, param_type p)) params))"
*)
abbreviation "find_operation op param_types \<equiv>
  find (\<lambda>x. oper_name x = op \<and>
    list_all2 (\<lambda>x y. x \<le> y) param_types (map param_type (oper_in_params x))) operations"

abbreviation "find_owned_attribute \<C> attr \<equiv>
  map_option (Pair \<C>) (Option.bind (fmlookup attributes \<C>) (\<lambda>attrs\<^sub>\<C>. fmlookup attrs\<^sub>\<C> attr))"

abbreviation "find_attribute \<C> attr \<equiv>
  let found = Option.these {find_owned_attribute \<D> attr | \<D>. less_eq \<C> \<D>} in
  if card found = 1 then Some (the_elem found) else None"

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

end

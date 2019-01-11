(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Object Model\<close>
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

type_synonym 'a assoc_end = "'a \<times> nat \<times> enat \<times> bool \<times> bool"
type_synonym 'b param_spec = "param \<times> 'b \<times> param_dir"
type_synonym ('b, 'c) oper_spec = "oper \<times> 'b param_spec list \<times> 'b \<times> 'c option"

definition "assoc_end_class \<equiv> fst"
definition "assoc_end_min \<equiv> fst \<circ> snd"
definition "assoc_end_max \<equiv> fst \<circ> snd \<circ> snd"
definition "assoc_end_ordered \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_unique \<equiv> snd \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_min_le_max end \<equiv> assoc_end_min end \<le> assoc_end_max end"

definition "assoc_refer_class ends \<C> \<equiv>
  fBex (fmdom ends) (\<lambda>role. assoc_end_class (the (fmlookup ends role)) = \<C>)"

definition "assoc_refer_role ends role \<equiv> fmlookup ends role \<noteq> None"

text \<open>
  The OCL specification allows attribute redefinition with the same type.
  But we prohibit it.\<close>

locale object_model = semilattice_sup +
  fixes attributes :: "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'b"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and operations :: "('b, 'c) oper_spec list"
  assumes attributes_distinct:
    "less \<C> \<D> \<Longrightarrow>
     fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
     fmlookup attributes \<D> = Some attrs\<^sub>\<D> \<Longrightarrow>
     fmlookup attrs\<^sub>\<C> attr \<noteq> None \<Longrightarrow>
     fmlookup attrs\<^sub>\<D> attr = None"
begin

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

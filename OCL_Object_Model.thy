(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Object Model\<close>
theory OCL_Object_Model
  imports OCL_Syntax "HOL-Library.Transitive_Closure_Table"
begin

section \<open>Definition\<close>

definition
  "assoc_end_type end \<equiv>
    let cls = assoc_end_class end in
    if assoc_end_max end \<le> 1 then
      if assoc_end_min end = 0
        then (ObjectType cls)[?]
        else (ObjectType cls)[1]
    else
      (case (assoc_end_unique end, assoc_end_ordered end)
        of (False, False) \<Rightarrow> Bag (ObjectType cls)[1]
         | (False, True)  \<Rightarrow> Sequence (ObjectType cls)[1]
         | (True,  False) \<Rightarrow> Set (ObjectType cls)[1]
         | (True,  True)  \<Rightarrow> OrderedSet (ObjectType cls)[1])"

definition "oper_type op \<equiv>
  let params = oper_out_params op in
  if length params = 0
    then oper_result op
    else Tuple (fmap_of_list (map (\<lambda>p. (param_name p, param_type p))
      (params @ [(STR ''result'', oper_result op, Out)])))"

class ocl_object_model =
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and operations :: "('a type, 'a expr) oper_spec list"
  and literals :: "'a enum \<rightharpoonup>\<^sub>f elit fset"
(*  and literals :: "'a basic_type \<rightharpoonup>\<^sub>f elit fset"*)
  assumes attributes_distinct:
    "\<C> < \<D> \<Longrightarrow>
     fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
     fmlookup attributes \<D> = Some attrs\<^sub>\<D> \<Longrightarrow>
     fmlookup attrs\<^sub>\<C> attr \<noteq> None \<Longrightarrow>
     fmlookup attrs\<^sub>\<D> attr = None"
begin

interpretation base: object_model
  apply standard
  by (simp add: local.attributes_distinct)

abbreviation "find_attribute \<equiv> base.find_attribute"
abbreviation "find_association_end \<equiv> base.find_association_end"
abbreviation "find_operation \<equiv> base.find_operation"
abbreviation "has_literal \<equiv> base.has_literal"

end

end

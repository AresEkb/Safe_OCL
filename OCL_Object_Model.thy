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
    let \<C> = assoc_end_class end in
    if assoc_end_max end \<le> 1 then
      if assoc_end_min end = 0
        then \<langle>\<C>\<rangle>\<^sub>\<T>[?]
        else \<langle>\<C>\<rangle>\<^sub>\<T>[1]
    else
      (case (assoc_end_unique end, assoc_end_ordered end)
        of (False, False) \<Rightarrow> Bag \<langle>\<C>\<rangle>\<^sub>\<T>[1]
         | (False, True)  \<Rightarrow> Sequence \<langle>\<C>\<rangle>\<^sub>\<T>[1]
         | (True,  False) \<Rightarrow> Set \<langle>\<C>\<rangle>\<^sub>\<T>[1]
         | (True,  True)  \<Rightarrow> OrderedSet \<langle>\<C>\<rangle>\<^sub>\<T>[1])"

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
begin

interpretation base: object_model .

abbreviation "find_attribute \<equiv> base.find_attribute"
abbreviation "find_association_end \<equiv> base.find_association_end"
abbreviation "find_operation \<equiv> base.find_operation"
abbreviation "find_static_operation \<equiv> base.find_static_operation"
abbreviation "has_literal \<equiv> base.has_literal"

end

lemma find_implies_in_set:
  "find P xs = Some x \<Longrightarrow> x \<in> set xs"
  by (metis find_Some_iff nth_mem)
(*
lemma oper_type_wd:
  "oper_result op \<noteq> OclInvalid \<Longrightarrow> oper_type op \<noteq> OclInvalid"
  unfolding oper_type_def
  apply auto
  by (smt type.distinct(17))

class ocl_object_model = ocl_object_model' +
  assumes operations_wd: "\<And>op. op \<in> set operations \<Longrightarrow> oper_result op \<noteq> OclInvalid"
begin

lemma find_static_operation_wd:
  "find_static_operation \<tau> op \<pi> = Some oper \<Longrightarrow>
   oper_type oper \<noteq> OclInvalid"
  by (simp add: operations_wd oper_type_wd find_implies_in_set)

end
*)
end

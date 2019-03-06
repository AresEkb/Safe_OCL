(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Object Model\<close>
theory OCL_Object_Model
  imports OCL_Syntax
begin

text \<open>
  I see no reason why objects should refer nulls using multi-valued
  associations. Therefore, multi-valued associations have collection
  types with non-nullable element types.\<close>

definition
  "assoc_end_type end \<equiv>
    let \<C> = assoc_end_class end in
    if assoc_end_max end \<le> 1 then
      if assoc_end_min end = 0 then \<langle>\<C>\<rangle>\<^sub>\<T>[?] else \<langle>\<C>\<rangle>\<^sub>\<T>[1]
    else
      (case (assoc_end_unique end, assoc_end_ordered end)
        of (True,  False) \<Rightarrow> Set \<langle>\<C>\<rangle>\<^sub>\<T>[1]
         | (True,  True)  \<Rightarrow> OrderedSet \<langle>\<C>\<rangle>\<^sub>\<T>[1]
         | (False, False) \<Rightarrow> Bag \<langle>\<C>\<rangle>\<^sub>\<T>[1]
         | (False, True)  \<Rightarrow> Sequence \<langle>\<C>\<rangle>\<^sub>\<T>[1])"

definition "class_assoc_type \<A> \<equiv> Set \<langle>\<A>\<rangle>\<^sub>\<T>[1]"

definition "class_assoc_end_type end \<equiv> \<langle>assoc_end_class end\<rangle>\<^sub>\<T>[1]"

definition "oper_type op \<equiv>
  let params = oper_out_params op in
  if length params = 0
    then oper_result op
    else Tuple (fmap_of_list (map (\<lambda>p. (param_name p, param_type p))
      (params @ [(STR ''result'', oper_result op, Out)])))"

class ocl_object_model =
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and association_classes :: "'a \<rightharpoonup>\<^sub>f assoc"
  and operations :: "('a type, 'a expr) oper_spec list"
  and literals :: "'a enum \<rightharpoonup>\<^sub>f elit fset"
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

interpretation base: object_model
  by standard (simp_all add: local.assoc_end_min_less_eq_max local.class_roles_unique)

abbreviation "attribute \<equiv> base.attribute"
abbreviation "association_end \<equiv> base.association_end"
abbreviation "referred_by_association_class \<equiv> base.referred_by_association_class"
abbreviation "association_class_end \<equiv> base.association_class_end"
abbreviation "operation \<equiv> base.operation"
abbreviation "static_operation \<equiv> base.static_operation"
abbreviation "has_literal \<equiv> base.has_literal"

lemmas attribute_det = base.attribute_det
lemmas association_end_det = base.association_end_det
lemmas association_class_end_det = base.association_class_end_det
lemmas operation_det = base.operation_det
lemmas static_operation_det = base.static_operation_det

end

end

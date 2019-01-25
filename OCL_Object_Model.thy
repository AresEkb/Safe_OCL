(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>OCL Object Model\<close>
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

(*
datatype 'a ty = A | B

instantiation ty :: (order) order
begin
definition "x < y \<equiv> x = A \<and> y = B"
definition "x \<le> y \<equiv> (x :: 'a ty) = y \<or> x < y"
instance
  apply intro_classes
  using less_eq_ty_def less_ty_def by auto
end

locale loc =
  fixes f :: "'a :: semilattice_sup \<Rightarrow> 't :: order"
begin
definition "g \<equiv> inv f"
end

class cls = semilattice_sup +
  fixes f :: "'a \<Rightarrow> 'a ty"
begin
interpretation base: loc .
abbreviation "g \<equiv> base.g"
end
*)


class ocl_object_model =
  fixes attributes :: "'a :: semilattice_sup \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  and operations :: "('a type, 'a expr) oper_spec list"
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
(*
abbreviation "oper_in_params op \<equiv>
  filter (\<lambda>p. param_dir p = In \<or> param_dir p = InOut) (oper_params op)"

abbreviation "find_operation op param_types \<equiv>
  find (\<lambda>x. oper_name x = op \<and>
    list_all2 (<) param_types (map param_type (oper_in_params x))) operations"
*)
end

(*** Test Cases *************************************************************)

section \<open>Test Cases\<close>

instantiation classes1 :: ocl_object_model
begin
(*
definition "attributes_classes1 \<equiv> Abs_fmap [
  Person \<mapsto> Abs_fmap [
    STR ''name1'' \<mapsto> String[1] :: classes1 type],
  Employee \<mapsto> Abs_fmap [
    STR ''name'' \<mapsto> Integer[1],
    STR ''position'' \<mapsto> String[1]],
  Customer \<mapsto> Abs_fmap [
    STR ''vip'' \<mapsto> Boolean[1]],
  Project \<mapsto> Abs_fmap [
    STR ''name'' \<mapsto> String[1],
    STR ''cost'' \<mapsto> Real[?]],
  Task \<mapsto> Abs_fmap [
    STR ''description'' \<mapsto> String[1]]]"
*)
definition "attributes_classes1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name1'', String[1] :: classes1 type)]),
  (Employee, fmap_of_list [
    (STR ''name'', Integer[1] :: classes1 type),
    (STR ''position'', String[1])]),
  (Customer, fmap_of_list [
    (STR ''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''cost'', Real[?])]),
  (Task, fmap_of_list [
    (STR ''description'', String[1])])]"

definition "associations_classes1 \<equiv> fmap_of_list [
  (STR ''ProjectPerson'', fmap_of_list [
    (STR ''projects1'', (Project, 0::nat, 5, False, False)),
    (STR ''person'', (Person, 0, 1, False, False))]),
  (STR ''ProjectManager'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, \<infinity>::enat, False, False)),
    (STR ''manager'', (Employee, 1, 1, False, False))]),
  (STR ''ProjectMember'', fmap_of_list [
    (STR ''member_of'', (Project, 0, \<infinity>, False, False)),
    (STR ''members'', (Employee, 1, 20, False, False))]),
  (STR ''ManagerEmployee'', fmap_of_list [
    (STR ''line_manager'', (Employee, 0::nat, 1, False, False)),
    (STR ''project_manager'', (Employee, 0::nat, \<infinity>, False, False)),
    (STR ''employees'', (Employee, 3, 7, False, False))]),
  (STR ''ProjectCustomer'', fmap_of_list [
    (STR ''projects'', (Project, 0, \<infinity>, False, False)),
    (STR ''customer'', (Customer, 1, 1, False, False))]),
  (STR ''ProjectTask'', fmap_of_list [
    (STR ''project'', (Project, 1, 1, False, False)),
    (STR ''tasks'', (Task, 0, \<infinity>, False, False))]),
  (STR ''SprintTaskAssignee'', fmap_of_list [
    (STR ''sprint'', (Sprint, 0, 10, False, False)),
    (STR ''tasks'', (Task, 0, 5, False, False)),
    (STR ''assignee'', (Employee, 0, 1, False, False))])]"

definition "operations_classes1 \<equiv> [
  (\<comment> \<open>Name\<close>
   STR ''membersCount'',
   \<comment> \<open>Parameters\<close>
   [(STR ''self'', (ObjectType Project)[?], In)],
   \<comment> \<open>Return Type\<close>
   Integer[1],
   \<comment> \<open>Body: self.members->size()\<close>
   Some (UnaryOperationCall
      (AssociationEndCall (Var STR ''self'') DotCall STR ''members'')
      ArrowCall CollectionSizeOp)),
  (\<comment> \<open>Name\<close>
   STR ''membersByName'',
   \<comment> \<open>Parameters\<close>
   [(STR ''self'', (ObjectType Project)[?], In),
    (STR ''member_name'', String[1], In)],
   \<comment> \<open>Return Type\<close>
   Set \<langle>Employee\<rangle>\<^sub>\<T>[1],
   \<comment> \<open>Body: self.members->select(member | member.name = member_name)\<close>
   Some (IteratorCall
      (AssociationEndCall (Var STR ''self'') DotCall STR ''members'')
      ArrowCall SelectIter [STR ''member'']
        (BinaryOperationCall
          (AttributeCall (Var STR ''member'') DotCall STR ''name'')
          DotCall EqualOp (Var STR ''member_name''))))
  ] :: (classes1 type, classes1 expr) oper_spec list"

lemma classes1_attrs_ok:
  "\<C> < \<D> \<Longrightarrow>
   fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
   fmlookup attributes \<D> = Some attrs\<^sub>\<D> \<Longrightarrow>
   fmlookup attrs\<^sub>\<C> attr \<noteq> None \<Longrightarrow>
   fmlookup attrs\<^sub>\<D> attr = None"
  for \<C> \<D> :: classes1
  unfolding less_classes1_def
  by (induct rule: subclass1.induct; auto simp add: attributes_classes1_def)

instance
  apply intro_classes
  by (simp add: classes1_attrs_ok)

end

subsection \<open>Positive Cases\<close>

(* TODO: Check *)
value "find_attribute Employee STR ''name''"
value "find_attribute Employee STR ''position''"
value "find_association_end Employee STR ''projects''"
value "find_association_end Person STR ''projects''"
value "find_operation STR ''membersCount'' [(ObjectType Project)[1]]"
value "find_operation STR ''membersByName'' [(ObjectType Project)[1], String[1]]"

subsection \<open>Negative Cases\<close>

(*value "find_association_end Project STR ''manager1''"*)

end

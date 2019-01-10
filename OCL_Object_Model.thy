theory OCL_Object_Model
  imports Object_Model OCL_Types
begin

class ocl_object_model = semilattice_sup +
  fixes attributes :: "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
  and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
  assumes attributes_distinct:
    "less \<C> \<D> \<Longrightarrow>
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

end

(*** Test Cases *************************************************************)

section \<open>Test Cases\<close>

instantiation classes1 :: ocl_object_model
begin

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
    (STR ''projects'', (Project, 0::nat, 5)),
    (STR ''person'', (Person, 0, 1))]),
  (STR ''ProjectManager'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, \<infinity>::enat)),
    (STR ''manager'', (Employee, 1, 1))]),
  (STR ''ProjectMember'', fmap_of_list [
    (STR ''member_of'', (Project, 0, \<infinity>)),
    (STR ''members'', (Employee, 1, 20))]),
  (STR ''ManagerEmployee'', fmap_of_list [
    (STR ''line_manager'', (Employee, 0::nat, 1)),
    (STR ''project_manager'', (Employee, 0::nat, \<infinity>)),
    (STR ''employees'', (Employee, 3, 7))]),
  (STR ''ProjectCustomer'', fmap_of_list [
    (STR ''projects'', (Project, 0, \<infinity>)),
    (STR ''customer'', (Customer, 1, 1))]),
  (STR ''ProjectTask'', fmap_of_list [
    (STR ''project'', (Project, 1, 1)),
    (STR ''tasks'', (Task, 0, \<infinity>))]),
  (STR ''SprintTaskAssignee'', fmap_of_list [
    (STR ''sprint'', (Sprint, 0, 10)),
    (STR ''tasks'', (Task, 0, 5)),
    (STR ''assignee'', (Employee, 0, 1))])]"

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

subsection \<open>Negative Cases\<close>

value "find_association_end Project STR ''manager1''"

end

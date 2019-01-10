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
type_synonym 'a model = "'a attrs \<times> 'a assocs"

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

(* from нужен для N-арных ассоциаций, в которых у исходного класса больше одной роли
   С другой стороны, не очень понятно зачем. Для определения типа не нужен,
   нужен для вычисления значения  *)

definition "attrs_ok attrs \<equiv> \<nexists>\<C> \<D> attrs\<^sub>\<C> attrs\<^sub>\<D> attr.
  \<C> < \<D> \<and>
  fmlookup attrs \<C> = Some attrs\<^sub>\<C> \<and>
  fmlookup attrs \<D> = Some attrs\<^sub>\<D> \<and>
  fmlookup attrs\<^sub>\<C> attr \<noteq> None \<and>
  fmlookup attrs\<^sub>\<D> attr \<noteq> None"

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

class object_model = semilattice_sup +
  fixes attribute :: "'a \<Rightarrow> attr \<Rightarrow> 'a \<Rightarrow> 'a type \<Rightarrow> bool"

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

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

code_pred [show_modes] find_attribute .

lemma fmember_code_predI [code_pred_intro]:
  "Predicate_Compile.contains (fset xs) x \<Longrightarrow> x |\<in>| xs"
  by (meson Predicate_Compile.containsE notin_fset)

code_pred [show_modes] fmember
  by (simp add: Predicate_Compile.containsI fmember.rep_eq)

code_pred [show_modes] find_association .

(*** Test Cases *************************************************************)

section \<open>Test Cases\<close>

definition "attrs1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type)]),
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

value "attrs_ok attrs1"

lemma find_attribute_det:
  "attrs_ok attrs \<Longrightarrow>
   find_attribute attrs \<C> attr \<D> \<tau> \<Longrightarrow>
   find_attribute attrs \<C> attr \<E> \<sigma> \<Longrightarrow>
   \<D> = \<E> \<and> \<tau> = \<sigma>"
  sorry

definition assocs1 :: "classes1 assocs" where
  "assocs1 \<equiv> fmap_of_list [
  (STR ''ProjectPerson'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, 5)),
    (STR ''person'', (Person, 0, 1))]),
  (STR ''ProjectManager'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, \<infinity>)),
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

instantiation classes1 :: object_model
begin

definition "attribute_classes1 = find_attribute attrs1"

instance ..

end

print_theorems

definition "model_ok m \<equiv> attrs_ok (fst m)"

typedef (overloaded) 'a good_model = "{m :: ('a :: ord) model. model_ok m}"
proof -
  have "model_ok (fmempty, fmempty)"
    unfolding model_ok_def attrs_ok_def
    by auto
  thus ?thesis
    by auto
qed


term attribute_classes1
term "classes1.attribute"

definition "model1 \<equiv> (attrs1, assocs1)"

subsection \<open>Positive Cases\<close>

values "{(c, t). attribute Employee (STR ''name'') c t}"
values "{(c, t). find_attribute attrs1 Employee (STR ''name'') c t}"
values "{(c, t). find_attribute attrs1 Employee (STR ''position'') c t}"
values "{(c, e). find_association assocs1 Employee STR ''projects'' c e}"
values "{(c, e). find_association assocs1 Customer STR ''projects'' c e}"

subsection \<open>Negative Cases\<close>

values "{(c, e). find_association assocs1 Project STR ''manager1'' c e}"

end

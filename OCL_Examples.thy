(*  Title:       Safe OCL
    Author:      Denis Nikiforov, February 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Examples\<close>
theory OCL_Examples
  imports OCL_Normalization
begin

(*** Classes ****************************************************************)

section \<open>Classes\<close>

datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

inductive subclass1 where
  "c \<noteq> Object \<Longrightarrow>
   subclass1 c Object"
| "subclass1 Employee Person"
| "subclass1 Customer Person"

code_pred subclass1 .

instantiation classes1 :: semilattice_sup
begin

definition "(<) \<equiv> subclass1"
definition "(\<le>) \<equiv> subclass1\<^sup>=\<^sup>="

fun sup_classes1 where
  "Object \<squnion> _ = Object"
| "Person \<squnion> c = (if c = Person \<or> c = Employee \<or> c = Customer
    then Person else Object)"
| "Employee \<squnion> c = (if c = Employee then Employee else
    if c = Person \<or> c = Customer then Person else Object)"
| "Customer \<squnion> c = (if c = Customer then Customer else
    if c = Person \<or> c = Employee then Person else Object)"
| "Project \<squnion> c = (if c = Project then Project else Object)"
| "Task \<squnion> c = (if c = Task then Task else Object)"
| "Sprint \<squnion> c = (if c = Sprint then Sprint else Object)"

lemma less_le_not_le_classes1:
  "c < d \<longleftrightarrow> c \<le> d \<and> \<not> d \<le> c"
  for c d :: classes1
  unfolding less_classes1_def less_eq_classes1_def
  using subclass1.simps by auto

lemma order_refl_classes1:
  "c \<le> c"
  for c :: classes1
  unfolding less_eq_classes1_def by simp

lemma order_trans_classes1:
  "c \<le> d \<Longrightarrow> d \<le> e \<Longrightarrow> c \<le> e"
  for c d e :: classes1
  unfolding less_eq_classes1_def
  using subclass1.simps by auto

lemma antisym_classes1:
  "c \<le> d \<Longrightarrow> d \<le> c \<Longrightarrow> c = d"
  for c d :: classes1
  unfolding less_eq_classes1_def
  using subclass1.simps by auto

lemma sup_ge1_classes1:
  "c \<le> c \<squnion> d"
  for c d :: classes1
  by (induct c; auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

lemma sup_ge2_classes1:
  "d \<le> c \<squnion> d"
  for c d :: classes1
  by (induct c; auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

lemma sup_least_classes1:
  "c \<le> e \<Longrightarrow> d \<le> e \<Longrightarrow> c \<squnion> d \<le> e"
  for c d e :: classes1
  by (induct c; induct d;
      auto simp add: less_eq_classes1_def less_classes1_def subclass1.simps)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_classes1)
  apply (simp add: order_refl_classes1)
  apply (rule order_trans_classes1; auto)
  apply (simp add: antisym_classes1)
  apply (simp add: sup_ge1_classes1)
  apply (simp add: sup_ge2_classes1)
  apply (simp add: sup_least_classes1)
  done

end

instantiation classes1 :: enum
begin

definition [simp]: "enum_classes1 \<equiv>
  [Object, Person, Employee, Customer, Project, Task, Sprint]"

definition [simp]: "enum_all_classes1 P \<equiv>
  P Object \<and> P Person \<and> P Employee \<and> P Customer \<and> P Project \<and> P Task \<and> P Sprint"

definition [simp]: "enum_ex_classes1 P \<equiv>
  P Object \<or> P Person \<or> P Employee \<or> P Customer \<or> P Project \<or> P Task \<or> P Sprint" 

instance
  apply intro_classes
  apply auto
  by (metis classes1.exhaust)+

end

declare [[coercion "ObjectType :: classes1 \<Rightarrow> classes1 basic_type"]]

(*** Basic Types ************************************************************)

section \<open>Basic Types\<close>

subsection \<open>Positive Cases\<close>

value "UnlimitedNatural < (Real :: classes1 basic_type)"
value "\<langle>Employee\<rangle>\<^sub>\<T> < \<langle>Person\<rangle>\<^sub>\<T>"
value "\<langle>Person\<rangle>\<^sub>\<T> \<le> OclAny"

subsection \<open>Negative Cases\<close>

value "String \<le> (Boolean :: classes1 basic_type)"

(*** Types ******************************************************************)

datatype ty = A | B | C | D | E

instantiation ty :: order
begin

fun less_ty where
  "A < x = (x = B \<or> x = C \<or> x = D \<or> x = E)"
| "B < x = (x = C \<or> x = D \<or> x = E)"
| "C < x = False"
| "D < x = (x = E)"
| "E < x = False"

definition "(x :: ty) \<le> y \<equiv> x < y \<or> x = y"

lemma ty_less_le_not_le:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  for x y :: ty
  by (cases x; cases y; simp add: less_eq_ty_def)

lemma ty_order_refl [iff]:
  "x \<le> x"
  for x :: ty
  by (simp add: less_eq_ty_def)

lemma ty_order_trans:
  "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  for x y z :: ty
  by (cases x; cases y; cases z; simp add: less_eq_ty_def)

lemma ty_antisym:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  for x y :: ty
  by (cases x; cases y; simp add: less_eq_ty_def)

instance
  apply intro_classes
  apply (simp add: ty_less_le_not_le)
  apply simp
  using ty_order_trans apply blast
  by (simp add: ty_antisym)

end

instantiation ty :: enum
begin

definition "enum_ty \<equiv> [A, B, C, D, E]"
definition "enum_all_ty P \<equiv> P A \<and> P B \<and> P C \<and> P D \<and> P E"
definition "enum_ex_ty P \<equiv> P A \<or> P B \<or> P C \<or> P D \<or> P E"

instance
  apply intro_classes
  unfolding enum_ty_def enum_all_ty_def enum_ex_ty_def
  apply (rule UNIV_eq_I; simp; rule ty.exhaust; auto)
  apply simp
  apply (metis UNIV_I ty.exhaust)
  apply (metis UNIV_I ty.exhaust)
  done

end

inductive test where
  "Least (\<lambda>z. x < z \<and> z \<noteq> E) = z \<Longrightarrow>
   z \<le> y \<Longrightarrow>
   test x y z"

code_pred [show_modes] test .

values "{x. test A E x}"
(*
values "{x. test B E x}"
values "{x. test C E x}"
values "{x. test D E x}"
values "{x. test E E x}"
*)

lemma test_A_E_B:
  "test A E B"
  apply (rule test.intros)
  unfolding Least_def apply auto
  using less_eq_ty_def apply fastforce
  by (simp add: less_eq_ty_def)

thm Least_equality









section \<open>Types\<close>

subsection \<open>Positive Cases\<close>

value "Integer[?] < (OclSuper :: classes1 type)"
value "Collection Real[?] < (OclSuper :: classes1 type)"
value "Set (Collection Boolean[1]) < (OclSuper :: classes1 type)"
value "Set (Bag Boolean[1]) < Set (Collection Boolean[?] :: classes1 type)"
value "Tuple (fmap_of_list [(STR ''1'', Boolean[1]), (STR ''2'', Integer[1])]) <
       Tuple (fmap_of_list [(STR ''1'', Boolean[?] :: classes1 type)])"

value "Integer[1] \<squnion> Real[?] :: classes1 type" \<comment> \<open>@{text "Real[?]"}\<close>
value "Set Integer[1] \<squnion> Set (Real[1] :: classes1 type)" \<comment> \<open>@{text "Set(Real[1])"}\<close>
value "Set Integer[1] \<squnion> Bag (Boolean[?] :: classes1 type)" \<comment> \<open>@{text "Collection(OclAny[?])"}\<close>
value "Set Integer[1] \<squnion> Real[1] :: classes1 type" \<comment> \<open>@{text "OclSuper"}\<close>

subsection \<open>Negative Cases\<close>

value "OrderedSet Boolean[1] < Set (Boolean[1] :: classes1 type)"

(*** Object Model ***********************************************************)

section \<open>Object Model\<close>

instantiation classes1 :: ocl_object_model
begin

definition "attributes_classes1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type)]),
  (Employee, fmap_of_list [
    (STR ''position'', String[1])]),
  (Customer, fmap_of_list [
    (STR ''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''cost'', Real[?])]),
  (Task, fmap_of_list [
    (STR ''description'', String[1])])]"
(*
abbreviation "assocs \<equiv> fmap_of_list [
  (STR ''ProjectManager'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, \<infinity>::enat, False, True)),
    (STR ''manager'', (Employee, 1, 1, False, False))]),
  (STR ''ProjectMember'', fmap_of_list [
    (STR ''member_of'', (Project, 0, \<infinity>, False, False)),
    (STR ''members'', (Employee, 1, 20, True, True))]),
  (STR ''ManagerEmployee'', fmap_of_list [
    (STR ''line_manager'', (Employee, 0::nat, 1, False, False)),
    (STR ''project_manager'', (Employee, 0::nat, \<infinity>, False, False)),
    (STR ''employees'', (Employee, 3, 7, False, False))]),
  (STR ''ProjectCustomer'', fmap_of_list [
    (STR ''projects'', (Project, 0, \<infinity>, False, True)),
    (STR ''customer'', (Customer, 1, 1, False, False))]),
  (STR ''ProjectTask'', fmap_of_list [
    (STR ''project'', (Project, 1, 1, False, False)),
    (STR ''tasks'', (Task, 0, \<infinity>, True, True))]),
  (STR ''SprintTaskAssignee'', fmap_of_list [
    (STR ''sprint'', (Sprint, 0, 10, False, True)),
    (STR ''tasks'', (Task, 0, 5, False, True)),
    (STR ''assignee'', (Employee, 0, 1, False, False))])]"
*)
abbreviation "assocs \<equiv> [
  STR ''ProjectManager'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0::nat, \<infinity>::enat, False, True),
    STR ''manager'' \<mapsto>\<^sub>f (Employee, 1, 1, False, False)],
  STR ''ProjectMember'' \<mapsto>\<^sub>f [
    STR ''member_of'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, False),
    STR ''members'' \<mapsto>\<^sub>f (Employee, 1, 20, True, True)],
  STR ''ManagerEmployee'' \<mapsto>\<^sub>f [
    STR ''line_manager'' \<mapsto>\<^sub>f (Employee, 0::nat, 1, False, False),
    STR ''project_manager'' \<mapsto>\<^sub>f (Employee, 0::nat, \<infinity>, False, False),
    STR ''employees'' \<mapsto>\<^sub>f (Employee, 3, 7, False, False)],
  STR ''ProjectCustomer'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, True),
    STR ''customer'' \<mapsto>\<^sub>f (Customer, 1, 1, False, False)],
  STR ''ProjectTask'' \<mapsto>\<^sub>f [
    STR ''project'' \<mapsto>\<^sub>f (Project, 1, 1, False, False),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, \<infinity>, True, True)],
  STR ''SprintTaskAssignee'' \<mapsto>\<^sub>f [
    STR ''sprint'' \<mapsto>\<^sub>f (Sprint, 0, 10, False, True),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, 5, False, True),
    STR ''assignee'' \<mapsto>\<^sub>f (Employee, 0, 1, False, False)]]"

definition "associations_classes1 \<equiv> assocs"

definition "association_classes_classes1 \<equiv> fmempty :: classes1 \<rightharpoonup>\<^sub>f assoc"

text \<open>
\begin{verbatim}
context Project
def: membersCount() : Integer[1] = members->size()
def: membersByName(mn : String[1]) : Set(Employee[1]) =
       members->select(member | member.name = mn)
static def: allProjects() : Set(Project[1]) = Project[1].allInstances()
\end{verbatim}\<close>

definition "operations_classes1 \<equiv> [
  (STR ''membersCount'', Project[1], [], Integer[1], False,
   Some (OperationCall
    (AssociationEndCall (Var STR ''self'') DotCall STR ''members'' None)
    ArrowCall CollectionSizeOp [])),
  (STR ''membersByName'', Project[1], [(STR ''mn'', String[1], In)],
    Set Employee[1], False,
   Some (SelectIteratorCall
    (AssociationEndCall (Var STR ''self'') DotCall STR ''members'' None)
    ArrowCall [STR ''member''] None
    (OperationCall
      (AttributeCall (Var STR ''member'') DotCall STR ''name'')
      DotCall EqualOp [Var STR ''mn'']))),
  (STR ''allProjects'', Project[1], [], Set Project[1], True,
   Some (MetaOperationCall Project[1] AllInstancesOp))
  ] :: (classes1 type, classes1 expr) oper_spec list"

declare [[coercion "phantom :: String.literal \<Rightarrow> classes1 enum"]]

definition "literals_classes1 \<equiv> fmap_of_list [
  (STR ''E1'' :: classes1 enum, {|STR ''A'', STR ''B''|}),
  (STR ''E2'', {|STR ''C'', STR ''D'', STR ''E''|})]"
(*
lemma q:
  "owned_association_end' assocs \<C> role from end\<^sub>1 \<Longrightarrow>
   owned_association_end' assocs \<C> role from end\<^sub>2 \<Longrightarrow>
   end\<^sub>1 = end\<^sub>2"
  apply (erule owned_association_end'.cases; erule owned_association_end'.cases; simp)
  unfolding associations_classes1_def
  apply simp
*)
(*
lemma q11:
  "x |\<in>| fmdom (fmupd k y xm) \<longleftrightarrow> x = k \<or> x |\<in>| fmdom xm"
  by auto

lemma q12:
  "x |\<in>| fmdom fmempty \<Longrightarrow> False"
  by simp

lemma q13:
  "assoc\<^sub>1 |\<in>| fmdom (fmupd k y xm) \<Longrightarrow>
   fmlookup (fmupd k y xm) assoc\<^sub>1 = Some ends\<^sub>1 \<Longrightarrow>
   ends\<^sub>1 = y \<or> fmlookup xm assoc\<^sub>1 = Some ends\<^sub>1"
  by (metis fmupd_lookup option.inject)
(*
lemma q14:
  "fmlookup (m(a \<mapsto>\<^sub>f b)) a' = (if a = a' then Some b else fmlookup m a')"
*)

lemma q16 []:
  "(a, b, c, d, e) = x \<longleftrightarrow> x = (a, b, c, d, e)"
  by auto

lemma q17 []:
  "fmlookup xm x = Some y \<longleftrightarrow> Some y = fmlookup xm x"
  by auto

thm fmupd_lookup if_splits

lemma owned_association_end_det':
  "assoc\<^sub>1 |\<in>| fmdom assocs \<Longrightarrow>
   assoc\<^sub>2 |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc\<^sub>1 = Some ends\<^sub>1 \<Longrightarrow>
   fmlookup assocs assoc\<^sub>2 = Some ends\<^sub>2 \<Longrightarrow>
   fmlookup ends\<^sub>1 role = Some end\<^sub>1 \<Longrightarrow>
   fmlookup ends\<^sub>2 role = Some end\<^sub>2 \<Longrightarrow>
   fmlookup ends\<^sub>1 from\<^sub>1 = Some from_end\<^sub>1 \<Longrightarrow>
   fmlookup ends\<^sub>2 from\<^sub>2 = Some from_end\<^sub>2 \<Longrightarrow>
   assoc_end_class from_end\<^sub>1 = assoc_end_class from_end\<^sub>2 \<Longrightarrow>
   from\<^sub>1 |\<in>| fmdom ends\<^sub>1 \<Longrightarrow>
   from\<^sub>2 |\<in>| fmdom ends\<^sub>2 \<Longrightarrow>
   role \<noteq> from\<^sub>1 \<Longrightarrow>
   role \<noteq> from\<^sub>2 \<Longrightarrow>
   end\<^sub>1 = end\<^sub>2"
  apply (cases "role |\<notin>| fmdom ends\<^sub>1")
  apply (simp add: fmdomI)
  apply (simp split: if_splits)
  unfolding q15 assoc_end_class_def
  unfolding q17
  apply (simp del: fmupd_lookup)
  apply (elim disjE; simp)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  unfolding q16
                      apply simp
  apply simp
                      apply simp
*)
(*
  apply (simp)
  apply (elim disjE; clarsimp)
  apply (elim disjE; clarsimp)
  apply (elim disjE; clarsimp)
  apply (elim disjE; clarsimp)
  apply (simp; elim disjE)
*)
(*
  apply (simp add: split: if_splits)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]*)
(*                      apply auto[1]*)
(*
  unfolding q11 assoc_end_class_def
  apply (elim disjE)
  apply simp
  apply auto[1]
  using [[simp_trace]] apply auto[1]
*)

term fmdrop

inductive assoc_refer_class' where
  "role |\<in>| fmdom ends \<Longrightarrow> (* Это можно убрать или нужно для кодогенератора? *)
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = \<C> \<Longrightarrow>
   assoc_refer_class' ends \<C> role"

code_pred [show_modes] assoc_refer_class' .

inductive class_roles where
  "assoc |\<in>| fmdom associations1 \<Longrightarrow> (* Это можно убрать или нужно для кодогенератора? *)
   fmlookup associations1 assoc = Some ends \<Longrightarrow>
   assoc_refer_class' ends \<C> from \<Longrightarrow>
   role |\<in>| fmdom ends \<Longrightarrow> (* Это можно убрать или нужно для кодогенератора? *)
   fmlookup ends role = Some end \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   class_roles associations1 \<C> assoc from role"

code_pred [show_modes] class_roles .

thm class_roles_i_i_i_i_i_def

lemma q15:
  "fmupd k x xm = y \<longleftrightarrow> y = fmupd k x xm"
  by auto

thm class_roles_i_i_o_o_o_def

lemma class_roles_unique:
  "class_roles assocs Employee assoc\<^sub>1 from role \<Longrightarrow>
   class_roles assocs Employee assoc\<^sub>2 from role \<Longrightarrow> assoc\<^sub>1 = assoc\<^sub>2"
  apply (erule class_roles.cases; erule class_roles.cases;
     erule assoc_refer_class'.cases; erule assoc_refer_class'.cases)
  unfolding q15
  apply simp
(*
  apply (drule OCL_Examples.class_roles_i_i_o_o_oI)
  apply (drule OCL_Examples.class_roles_i_i_o_o_oI)
  unfolding class_roles_i_i_o_o_o_def
  apply auto
*)
(*
  apply (erule class_roles.cases; erule class_roles.cases;
     erule assoc_refer_class'.cases; erule assoc_refer_class'.cases)
  unfolding q15
  apply simp
  apply (elim disjE, simp split: if_splits)
  apply (simp_all split: if_splits)
*)


 
  
  
values "{(x, y, z). class_roles assocs Employee x y z}"
values "{(x, y, z). class_roles assocs Object x y z}"
values "{(x, y, z). class_roles assocs Project x y z}"
values "{(x, y, z, a). class_roles assocs x y z a}"

inductive class_roles where
  "assocs2 = fmfilter (\<lambda>assoc.
     fmlookup associations1 assoc = Some ends \<and>
     assoc_refer_class ends \<C>) associations1 \<Longrightarrow>
   assoc |\<in>| fmdom assocs2 \<Longrightarrow>
   fmlookup assocs2 assoc = Some ends \<Longrightarrow>
   class_roles associations1 \<C> ends"

code_pred [show_modes] class_roles .

lemma owned_association_end_det':
  "assoc\<^sub>1 |\<in>| fmdom assocs \<Longrightarrow>
   assoc\<^sub>2 |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc\<^sub>1 = Some ends\<^sub>1 \<Longrightarrow>
   fmlookup assocs assoc\<^sub>2 = Some ends\<^sub>2 \<Longrightarrow>
   fmlookup ends\<^sub>1 role = Some end\<^sub>1 \<Longrightarrow>
   fmlookup ends\<^sub>2 role = Some end\<^sub>2 \<Longrightarrow>
   fmlookup ends\<^sub>1 from\<^sub>1 = Some from_end\<^sub>1 \<Longrightarrow>
   fmlookup ends\<^sub>2 from\<^sub>2 = Some from_end\<^sub>2 \<Longrightarrow>
   assoc_end_class from_end\<^sub>1 = assoc_end_class from_end\<^sub>2 \<Longrightarrow>
   from\<^sub>1 |\<in>| fmdom ends\<^sub>1 \<Longrightarrow>
   from\<^sub>2 |\<in>| fmdom ends\<^sub>2 \<Longrightarrow>
   role \<noteq> from\<^sub>1 \<Longrightarrow>
   role \<noteq> from\<^sub>2 \<Longrightarrow>
   end\<^sub>1 = end\<^sub>2"
  apply (cases "role |\<notin>| fmdom ends\<^sub>1")
  apply (simp add: fmdomI)
  apply (simp)
  apply (elim disjE; simp add: assoc_end_class_def split: if_splits)
  by auto
(*
lemma owned_association_end_det':
  assumes "assoc\<^sub>1 |\<in>| fmdom assocs"
   and "assoc\<^sub>2 |\<in>| fmdom assocs"
   and "fmlookup assocs assoc\<^sub>1 = Some ends\<^sub>1"
   and "fmlookup assocs assoc\<^sub>2 = Some ends\<^sub>2"
   and "fmlookup ends\<^sub>1 role = Some end\<^sub>1"
   and "fmlookup ends\<^sub>2 role = Some end\<^sub>2"
   and "fmlookup ends\<^sub>1 from\<^sub>1 = Some from_end\<^sub>1"
   and "fmlookup ends\<^sub>2 from\<^sub>2 = Some from_end\<^sub>2"
   and "assoc_end_class from_end\<^sub>1 = assoc_end_class from_end\<^sub>2"
   and "role \<noteq> from\<^sub>1"
   and "role \<noteq> from\<^sub>2"
  shows "end\<^sub>1 = end\<^sub>2"
proof -
  have "role |\<in>| fmdom ends\<^sub>1"
    by (simp add: assms(5) fmdomI)
  have "role |\<in>| fmdom ends\<^sub>2"
    by (simp add: assms(6) fmdomI)
  have "from\<^sub>1 |\<in>| fmdom ends\<^sub>1"
    by (simp add: assms(7) fmdomI)
  have "from\<^sub>2 |\<in>| fmdom ends\<^sub>2"
    by (simp add: assms(8) fmdomI)
  show ?thesis
qed
*)

lemma owned_association_end_det'':
  assumes "assoc\<^sub>1 |\<in>| fmdom assocs"
   and "assoc\<^sub>2 |\<in>| fmdom assocs"
   and "fmlookup assocs assoc\<^sub>1 = Some ends\<^sub>1"
   and "fmlookup assocs assoc\<^sub>2 = Some ends\<^sub>2"
   and "fmlookup ends\<^sub>1 role = Some end\<^sub>1"
   and "fmlookup ends\<^sub>2 role = Some end\<^sub>2"
   and "fmlookup ends\<^sub>1 from = Some from_end\<^sub>1"
   and "fmlookup ends\<^sub>2 from = Some from_end\<^sub>2"
   and "assoc_end_class from_end\<^sub>1 = assoc_end_class from_end\<^sub>2"
   and "role \<noteq> from"
  shows "end\<^sub>1 = end\<^sub>2"
proof -
  have "from |\<in>| fmdom ends\<^sub>1"
    by (simp add: assms(7) fmdomI)
  have "from |\<in>| fmdom ends\<^sub>2"
    by (simp add: assms(8) fmdomI)
  show ?thesis
    using \<open>from |\<in>| fmdom ends\<^sub>1\<close> \<open>from |\<in>| fmdom ends\<^sub>2\<close>
      assms owned_association_end_det' by blast
qed

(*
proof -
  assume a1: "assoc\<^sub>1 |\<in>| fmdom assocs"
  assume a2: "assoc\<^sub>2 |\<in>| fmdom assocs"
  assume a3: "fmlookup assocs assoc\<^sub>1 = Some ends\<^sub>1"
  assume a4: "fmlookup assocs assoc\<^sub>2 = Some ends\<^sub>2"
  assume a5: "fmlookup ends\<^sub>1 role = Some end\<^sub>1"
  assume a6: "fmlookup ends\<^sub>2 role = Some end\<^sub>2"
  assume a7: "fmlookup ends\<^sub>1 from = Some from_end\<^sub>1"
  assume a8: "fmlookup ends\<^sub>2 from = Some from_end\<^sub>2"
  assume a9: "assoc_end_class from_end\<^sub>1 = assoc_end_class from_end\<^sub>2"
  assume a10: "role \<noteq> from"
  have "\<forall>x0 x10 x1 x2 x3 x4 x5 x6 x7 x8 x9. (x10 |\<in>| fmdom assocs \<and> x9 |\<in>| fmdom assocs \<and> fmlookup assocs x10 = Some x8 \<and> fmlookup assocs x9 = Some x7 \<and> fmlookup x8 x6 = Some x5 \<and> fmlookup x7 x6 = Some x4 \<and> fmlookup x8 x3 = Some x2 \<and> fmlookup x7 x1 = Some x0 \<and> assoc_end_class x2 = assoc_end_class x0 \<and> x3 |\<in>| fmdom x8 \<and> x1 |\<in>| fmdom x7 \<and> x6 \<noteq> x3 \<and> x6 \<noteq> x1 \<longrightarrow> x5 = x4) = ((x10 |\<notin>| fmdom assocs \<or> x9 |\<notin>| fmdom assocs \<or> fmlookup assocs x10 \<noteq> Some x8 \<or> fmlookup assocs x9 \<noteq> Some x7 \<or> fmlookup x8 x6 \<noteq> Some x5 \<or> fmlookup x7 x6 \<noteq> Some x4 \<or> fmlookup x8 x3 \<noteq> Some x2 \<or> fmlookup x7 x1 \<noteq> Some x0 \<or> assoc_end_class x2 \<noteq> assoc_end_class x0 \<or> x3 |\<notin>| fmdom x8 \<or> x1 |\<notin>| fmdom x7 \<or> x6 = x3 \<or> x6 = x1) \<or> x5 = x4)"
    by meson
  then have f11: "\<forall>l la f fa lb p pa lc pb ld pc. (l |\<notin>| fmdom assocs \<or> la |\<notin>| fmdom assocs \<or> fmlookup assocs l \<noteq> Some f \<or> fmlookup assocs la \<noteq> Some fa \<or> fmlookup f lb \<noteq> Some p \<or> fmlookup fa lb \<noteq> Some pa \<or> fmlookup f lc \<noteq> Some pb \<or> fmlookup fa ld \<noteq> Some pc \<or> assoc_end_class pb \<noteq> assoc_end_class pc \<or> lc |\<notin>| fmdom f \<or> ld |\<notin>| fmdom fa \<or> lb = lc \<or> lb = ld) \<or> p = pa"
    by (metis owned_association_end_det') (* > 1.0 s, timed out *)
  have f12: "from |\<in>| fmdom ends\<^sub>2"
    using a8 by (metis fmdomI)
  have "from |\<in>| fmdom ends\<^sub>1"
    using a7 by (meson fmdomI)
  then show ?thesis
    using f12 f11 a10 a9 a8 a7 a6 a5 a4 a3 a2 a1 by blast
qed

  using owned_association_end_det'
  by (smt fmdomI)
*)
(*
lemma owned_association_end_det'':
  "assoc\<^sub>1 |\<in>| fmdom assocs \<Longrightarrow>
   assoc\<^sub>2 |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc\<^sub>1 = Some ends\<^sub>1 \<Longrightarrow>
   fmlookup assocs assoc\<^sub>2 = Some ends\<^sub>2 \<Longrightarrow>
   fmlookup ends\<^sub>1 role = Some end\<^sub>1 \<Longrightarrow>
   fmlookup ends\<^sub>2 role = Some end\<^sub>2 \<Longrightarrow>
   fmlookup ends\<^sub>1 from = Some from_end\<^sub>1 \<Longrightarrow>
   fmlookup ends\<^sub>2 from = Some from_end\<^sub>2 \<Longrightarrow>
   assoc_end_class from_end\<^sub>1 = assoc_end_class from_end\<^sub>2 \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   end\<^sub>1 = end\<^sub>2"
  apply (cases "role |\<in>| fmdom ends\<^sub>1"; simp)
  apply (elim disjE; simp split: if_splits)
  apply (auto)
  by (auto split: if_splits)
*)
instance
  apply standard
  apply (erule owned_association_end'.cases; erule owned_association_end'.cases; simp)
  using associations_classes1_def owned_association_end_det' apply presburger
  using associations_classes1_def owned_association_end_det'' apply presburger
  done

end

subsection \<open>Positive Cases\<close>
(*
value "find_attribute Employee STR ''name''"
value "find_attribute Employee STR ''position''"
*)
values "{(\<D>, \<tau>). attribute Employee STR ''name'' \<D> \<tau>}"
values "{(\<D>, \<tau>). attribute Employee STR ''position'' \<D> \<tau>}"
values "{end. association_end Employee STR ''projects'' None end}"
value "find_operation Project[1] STR ''membersCount'' []"
value "find_operation Project[1] STR ''membersByName'' [String[1]]"
value "has_literal STR ''E1'' STR ''A''"

subsection \<open>Negative Cases\<close>

(* TODO: Implement as lemma *)
(* TODO: Add a separate section with few examples for a generated code *)
(*values "{end. association_end Person STR ''projects'' None end}"*)
value "has_literal STR ''E1'' STR ''C''"

lemma subclass1_Person_x [simp]:
  "Person \<le> \<tau> = (\<tau> = Person \<or> \<tau> = Object)"
  unfolding dual_order.order_iff_strict less_classes1_def
  by (auto simp: subclass1.simps subclass1.intros)

lemma subclass1_Employee_x [simp]:
  "Employee \<le> \<tau> = (\<tau> = Employee \<or> \<tau> = Person \<or> \<tau> = Object)"
  unfolding dual_order.order_iff_strict less_classes1_def
  by (auto simp: subclass1.simps subclass1.intros)

declare attribute'.simps [simp]
declare class_has_attribute'.simps [simp]
declare owned_attribute'.simps [simp]
declare attributes_classes1_def [simp]
declare Least_def [simp]

lemma
  "attribute Employee STR ''name'' Person String[1]"
  by auto

inductive_simps q51: "owned_association_end' associations \<C> role None end"
inductive_simps q52: "owned_association_end' associations \<C> role (Some from) end"

print_theorems

lemma q61 [simp]:
  "fmupd k x xm = ym \<longleftrightarrow> ym = fmupd k x xm"
  by auto
(*
lemma q21:
  "owned_association_end' assocs Employee STR ''projects'' from end =
   ((from = None \<or> from = Some STR ''manager'') \<and>
    end = (Project, 0::nat, \<infinity>::enat, False, True))"
proof
  show "owned_association_end' assocs Employee STR ''projects'' from end \<Longrightarrow>
    (from = None \<or> from = Some STR ''manager'') \<and>
     end = (Project, 0, \<infinity>, False, True)"
    apply (erule owned_association_end'.cases)
    apply (auto simp add: assoc_end_class_def split: if_splits)
    done
  show "(from = None \<or> from = Some STR ''manager'') \<and>
     end = (Project, 0, \<infinity>, False, True) \<Longrightarrow>
     owned_association_end' assocs Employee STR ''projects'' from end"
    apply (simp add: owned_association_end'.simps)
*)

lemma q21:
  "owned_association_end' assocs Employee STR ''projects'' from end \<Longrightarrow>
   ((from = None \<or> from = Some STR ''manager'') \<and>
    end = (Project, 0::nat, \<infinity>::enat, False, True))"
  apply (erule owned_association_end'.cases)
  apply (auto simp add: assoc_end_class_def split: if_splits)
  done

  thm owned_association_end'.cases
(*
  apply (simp add: owned_association_end'.simps)
  apply auto
*)
lemma
  "association_end Employee STR ''projects'' None (Project, 0, \<infinity>, False, True)"
  apply (rule association_end'.intros)
   apply auto
  apply (simp add: associations_classes1_def)
   apply auto
  apply (auto simp add: class_is_association_source'.simps)
  apply (rule owned_association_end'.intros)
(*
   apply (auto simp add: association_end'.simps class_is_association_source'.simps
      )
*)
(*
owned_association_end'.simps associations_classes1_def
  apply (rule association_end'.intros)
  apply auto
  apply (rule owned_association_end'.intros)
*)
   apply (auto simp add: association_end'.simps class_is_association_source'.simps
      owned_association_end'.simps)
  apply (intro exI conjI)

thm classes1.distinct(19) classes1.simps(14) classes1.simps(16) classes1.simps(18) the_equality

  thm HOL.imp_conv_disj HOL.conj_disj_distribL

lemma
  "\<nexists>end. association_end Person STR ''projects'' None end"
  apply auto
  apply (erule association_end'.cases)
  apply auto

(*** Typing *****************************************************************)

section \<open>Typing\<close>

subsection \<open>Positive Cases\<close>


(*declare normalize_normalize_call_normalize_expr_list.intros [intro!]*)
(*declare nf_typing.intros [intro!]*)


(*
inductive_simps q52 [simp]: "\<Gamma> \<turnstile> expr : \<tau>"
inductive_simps q57 [simp]: "\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : \<tau>"
inductive_simps q58 [simp]: "\<Gamma> \<turnstile>\<^sub>E NullLiteral : \<tau>"
inductive_simps q59 [simp]: "\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : \<tau>"
inductive_simps q60 [simp]: "\<Gamma> \<turnstile> Var v \<Rrightarrow> expr"
inductive_simps q61 [simp]: "\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
inductive_simps q62 [simp]: "\<Gamma> \<turnstile>\<^sub>E Let v ty init body : \<tau>"
inductive_simps q63 [simp]: "\<Gamma> \<turnstile> Let v ty init body \<Rrightarrow> expr"
*)

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>
(*
inductive_simps op_type_simp [simp]: "op_type op k \<tau> \<pi> \<sigma>"

inductive_simps unop_type_simp [simp]: "unop_type op k \<tau> \<sigma>"
inductive_simps binop_type_simp [simp]: "binop_type op k \<tau> \<sigma> \<rho>"
inductive_simps ternop_type_simp [simp]: "ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>"

inductive_simps any_unop_type_simp [simp]: "any_unop_type op \<tau> \<sigma>"
inductive_simps boolean_unop_type_simp [simp]: "boolean_unop_type op \<tau> \<sigma>"
inductive_simps numeric_unop_type_simp [simp]: "numeric_unop_type op \<tau> \<sigma>"
inductive_simps string_unop_type_simp [simp]: "string_unop_type op \<tau> \<sigma>"
inductive_simps collection_unop_type_simp [simp]: "collection_unop_type op \<tau> \<sigma>"

inductive_simps super_binop_type_simp [simp]: "super_binop_type op \<tau> \<sigma> \<rho>"
inductive_simps boolean_binop_type_simp [simp]: "boolean_binop_type op \<tau> \<sigma> \<rho>"
inductive_simps numeric_binop_type_simp [simp]: "numeric_binop_type op \<tau> \<sigma> \<rho>"
inductive_simps string_binop_type_simp [simp]: "string_binop_type op \<tau> \<sigma> \<rho>"
inductive_simps collection_binop_type_simp [simp]: "collection_binop_type op \<tau> \<sigma> \<rho>"

inductive_simps string_ternop_type_simp [simp]: "string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"
inductive_simps collection_ternop_type_simp [simp]: "collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"
*)

inductive_simps op_type_alt_simps:
"mataop_type \<tau> op \<sigma>"
"typeop_type k op \<tau> \<sigma> \<rho>"

"op_type op k \<tau> \<pi> \<sigma>"
"unop_type op k \<tau> \<sigma>"
"binop_type op k \<tau> \<sigma> \<rho>"
"ternop_type op k \<tau> \<sigma> \<rho> \<upsilon>"

"any_unop_type op \<tau> \<sigma>"
"boolean_unop_type op \<tau> \<sigma>"
"numeric_unop_type op \<tau> \<sigma>"
"string_unop_type op \<tau> \<sigma>"
"collection_unop_type op \<tau> \<sigma>"

"super_binop_type op \<tau> \<sigma> \<rho>"
"boolean_binop_type op \<tau> \<sigma> \<rho>"
"numeric_binop_type op \<tau> \<sigma> \<rho>"
"string_binop_type op \<tau> \<sigma> \<rho>"
"collection_binop_type op \<tau> \<sigma> \<rho>"

"string_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"
"collection_ternop_type op \<tau> \<sigma> \<rho> \<upsilon>"


(*
declare boolean_unop_type.intros [intro!]
declare numeric_unop_type.intros [intro!]
declare string_unop_type.intros [intro!]
declare collection_unop_type.intros [intro!]

declare op_type.intros [intro!]

declare unop_type.intros [intro!]
declare binop_type.intros [intro!]
declare ternop_type.intros [intro!]

declare any_unop_type.intros [intro!]
declare boolean_unop_type.intros [intro!]
declare numeric_unop_type.intros [intro!]
declare string_unop_type.intros [intro!]
declare collection_unop_type.intros [intro!]

declare super_binop_type.intros [intro!]
declare boolean_binop_type.intros [intro!]
declare numeric_binop_type.intros [intro!]
declare string_binop_type.intros [intro!]
declare collection_binop_type.intros [intro!]

declare string_ternop_type.intros [intro!]
declare collection_ternop_type.intros [intro!]
*)



print_theorems
(*
inductive_simps q64 [simp]: "\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
inductive_simps q65 [simp]: "\<Gamma> \<turnstile>\<^sub>L [] : \<tau>"
inductive_simps q66 [simp]: "\<Gamma> \<turnstile>\<^sub>L x # xs : \<tau>"
inductive_simps q70 [simp]: "\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
inductive_simps q71 [simp]: "\<Gamma> \<turnstile>\<^sub>E Let v ty init body : \<tau>"
inductive_simps q72 [simp]: "\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau>"
inductive_simps q73 [simp]: "\<Gamma> \<turnstile>\<^sub>C [x] : \<tau>"
inductive_simps q74 [simp]: "\<Gamma> \<turnstile>\<^sub>C x # y # xs : \<tau>"
inductive_simps q75 [simp]: "\<Gamma> \<turnstile>\<^sub>P CollectionItem a : \<tau>"
inductive_simps q76 [simp]: "\<Gamma> \<turnstile>\<^sub>P CollectionRange a b : \<tau>"
*)
(*
inductive_simps q54 [simp]: "\<Gamma> \<turnstile>\<^sub>C Operation op params \<Rrightarrow> expr"
inductive_simps q55 [simp]: "\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> expr"
inductive_simps q56 [simp]: "\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> expr"

inductive_simps q50 [simp]: "\<Gamma> \<turnstile> OperationCall src k op params \<Rrightarrow> \<tau>"
inductive_simps q53 [simp]: "\<Gamma> \<turnstile> Literal c \<Rrightarrow> expr"
inductive_simps q68 [simp]: "\<Gamma> \<turnstile> Let v ty init body \<Rrightarrow> expr"
inductive_simps q69 [simp]: "\<Gamma> \<turnstile> Var v \<Rrightarrow> expr"
*)
(*
inductive_simps q51 [simp]: "element_type \<tau> \<sigma>"
inductive_simps q67 [simp]: "\<Gamma> \<turnstile> expr : \<tau>"
*)
inductive_simps typing_alt_simps: 
"\<Gamma> \<turnstile>\<^sub>E NullLiteral : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E BooleanLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RealLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E UnlimitedNaturalLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IntegerLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E StringLiteral c : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E EnumLiteral enm lit : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectionLiteral k prts : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral [] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleLiteral (x # xs) : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E Let v \<tau> init body : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E Var v : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E If a b c : \<tau>"

"\<Gamma> \<turnstile>\<^sub>E MetaOperationCall \<tau> op : \<sigma>"
"\<Gamma> \<turnstile>\<^sub>E StaticOperationCall \<tau> op as : \<sigma>"

"\<Gamma> \<turnstile>\<^sub>E TypeOperationCall a k op \<sigma> : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AttributeCall src k prop : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationEndCall src k role from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassCall src k a from : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AssociationClassEndCall src k role : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OperationCall src k op params : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E TupleElementCall src k elem : \<tau>"

"\<Gamma> \<turnstile>\<^sub>I (src, its, body) : ys"
"\<Gamma> \<turnstile>\<^sub>E IterateCall src k its its_ty res res_t res_init body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E AnyIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ClosureIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E CollectNestedIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ExistsIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E ForAllIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E OneIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E IsUniqueIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SelectIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E RejectIteratorCall src k its its_ty body : \<tau>"
"\<Gamma> \<turnstile>\<^sub>E SortedByIteratorCall src k its its_ty body : \<tau>"

"\<Gamma> \<turnstile>\<^sub>C [x] : \<tau>"
"\<Gamma> \<turnstile>\<^sub>C x # y # xs : \<tau>"
"\<Gamma> \<turnstile>\<^sub>P CollectionItem a : \<tau>"
"\<Gamma> \<turnstile>\<^sub>P CollectionRange a b : \<tau>"
"\<Gamma> \<turnstile>\<^sub>L [] : \<pi>"
"\<Gamma> \<turnstile>\<^sub>L x # xs : \<pi>"

inductive_simps normalize_alt_simps:
"\<Gamma> \<turnstile> Literal a \<Rrightarrow> b"
"\<Gamma> \<turnstile> Let v t init body \<Rrightarrow> b"
"\<Gamma> \<turnstile> Var v \<Rrightarrow> b"
"\<Gamma> \<turnstile> If a b c \<Rrightarrow> d"

"\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> b"
"\<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src DotCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src SafeDotCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src ArrowCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src SafeArrowCall call \<Rrightarrow> b"

"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C call \<Rrightarrow> b"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its its_ty res res_t res_init body \<Rrightarrow> call"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its its_ty body \<Rrightarrow> call"

"\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> ys"
"\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> ys"

(*
declare op_type.intros [intro!]
declare binop_type.intros [intro!]
declare boolean_binop_type.intros [intro!]
*)
print_theorems

declare nf_typing.simps [simp]

declare op_type_alt_simps [simp]
declare typing_alt_simps [simp]
declare normalize_alt_simps [simp]

declare element_type.simps [simp]
declare update_element_type.simps [simp]
declare to_unique_collection.simps [simp]
declare to_nonunique_collection.simps [simp]
declare to_ordered_collection.simps [simp]


abbreviation "\<Gamma> \<equiv> fmempty :: classes1 type env"

text \<open>
\<^verbatim>\<open>E1::A : E1[1]\<close>\<close>
lemma
  "\<Gamma> \<turnstile> EnumLiteral STR ''E1'' STR ''A'' : (Enum STR ''E1'')[1]"
  by (auto simp add: literals_classes1_def)

text \<open>
\<^verbatim>\<open>true or false : Boolean[1]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    OperationCall (BooleanLiteral True) DotCall OrOp
      [BooleanLiteral False] : Boolean[1]"
  by auto

text \<open>
\<^verbatim>\<open>null and true : Boolean[?]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    OperationCall (NullLiteral) DotCall AndOp
      [BooleanLiteral True] : Boolean[?]"
  by auto

text \<open>
\<^verbatim>\<open>let x : Real[1] = 5 in x + 7 : Real[1]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    Let (STR ''x'') (Some Real[1]) (IntegerLiteral 5)
    (OperationCall (Var STR ''x'') DotCall PlusOp [IntegerLiteral 7]) : Real[1]"
  by auto

text \<open>
\<^verbatim>\<open>null.oclIsUndefined() : Boolean[1]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    OperationCall (NullLiteral) DotCall OclIsUndefinedOp [] : Boolean[1]"
  by auto

(*
declare element_type.intros [intro!]
declare to_nonunique_collection.intros [intro!]
declare update_element_type.intros [intro!]
*)

lemma q81 [simp]:
  "Sequence \<tau> \<le> OclAny[?] = False"
  by auto

lemma q82 [simp]:
  "Sequence \<tau> \<le> Tuple \<pi> = False"
  by auto

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}.oclIsUndefined() : Sequence(Boolean[1])\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    OperationCall (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem NullLiteral])
    DotCall OclIsUndefinedOp [] : Sequence Boolean[1]"
  by auto

text \<open>
\<^verbatim>\<open>Sequence{1..5}->product(Set{'a', 'b'})
  : Set(Tuple(first: Integer[1], second: String[1]))\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    OperationCall (CollectionLiteral SequenceKind
      [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5)])
      ArrowCall ProductOp
      [CollectionLiteral SetKind
        [CollectionItem (StringLiteral ''a''),
         CollectionItem (StringLiteral ''b'')]] :
    Set (Tuple (fmap_of_list [(STR ''first'', Integer[1]), (STR ''second'', String[1])]))"
  by auto


lemma q83 [simp]:
  "\<tau>[1] < \<tau>[?]"
  "\<tau>[1] \<le> \<tau>[?]"
  apply auto
  by (simp add: less_type_def subtype.intros(3) tranclp.r_into_trancl)
(*
declare update_element_type.intros [intro]
declare update_element_type.simps [simp]
*)
text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->iterate(x, acc : Real[1] = 0 | acc + x)
  : Real[1]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    IterateCall (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem NullLiteral]) SafeArrowCall
      [STR ''x''] None
      (STR ''acc'') (Some Real[1]) (IntegerLiteral 0)
    (OperationCall (Var STR ''acc'') DotCall PlusOp [Var STR ''x'']) : Real[1]"
  by auto

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->max() : Integer[1]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
    OperationCall (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem NullLiteral])
      SafeArrowCall CollectionMaxOp [] : Integer[1]"
  by auto

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x->any(it | it = 'test') : String[?]\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
  Let (STR ''x'') (Some (Sequence String[?])) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (AnyIteratorCall (Var STR ''x'') ArrowCall [STR ''it''] (Some String[?])
    (OperationCall (Var STR ''it'') DotCall EqualOp [StringLiteral ''test''])) : String[?]"
  by auto

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x?->closure(it | it) : OrderedSet(String[1])\<close>\<close>
lemma
  "\<Gamma> \<turnstile>
  Let STR ''x'' (Some (Sequence String[?])) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (ClosureIteratorCall (Var STR ''x'') SafeArrowCall [STR ''it''] None
    (Var STR ''it'')) : OrderedSet String[1]"
  by auto

lemma q [simp]:
  "(Employee \<le> \<tau>) = (\<tau> = Employee \<or> \<tau> = Person \<or> \<tau> = Object)"
  by (metis dual_order.order_iff_strict less_classes1_def subclass1.simps)

inductive_simps attribute'_alt_simps[simp]: "attribute' attrs \<C> attr \<D> \<tau>"
inductive_simps owned_attribute'_alt_simps[simp]: "owned_attribute' attrs \<C> attr \<tau>"
inductive_simps class_has_attribute'_alt_simps[simp]: "class_has_attribute' attrs \<C> attr"

print_theorems

(*declare classes1.simps [simp]*)
(*
lemma q11:
  "owned_attribute' attributes Person STR ''name'' \<tau> = (\<tau> = String[1])"
  by (auto simp add: attributes_classes1_def owned_attribute'_alt_simps)

inductive_simps q12[simp]: "owned_attribute' attributes Employee STR ''position'' String[1]"
inductive_simps q13[simp]: "owned_attribute' attributes Customer STR ''vip'' Boolean[1]"
inductive_simps q14[simp]: "owned_attribute' attributes Project STR ''name'' String[1]"
inductive_simps q15[simp]: "owned_attribute' attributes Project STR ''cost'' Real[?]"
inductive_simps q16[simp]: "owned_attribute' attributes Task STR ''description'' String[1]"
*)
(*
definition "attributes_classes1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type)]),
  (Employee, fmap_of_list [
    (STR ''position'', String[1])]),
  (Customer, fmap_of_list [
    (STR ''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''cost'', Real[?])]),
  (Task, fmap_of_list [
    (STR ''description'', String[1])])]"
*)

print_theorems

(*
  HOL.conj_disj_distribL: (?P \<and> (?Q \<or> ?R)) = (?P \<and> ?Q \<or> ?P \<and> ?R)
  HOL.conj_disj_distribR: ((?P \<or> ?Q) \<and> ?R) = (?P \<and> ?R \<or> ?Q \<and> ?R)
  Groebner_Basis.dnf(2): ((?Q \<or> ?R) \<and> ?P) = (?Q \<and> ?P \<or> ?R \<and> ?P)
  HOL.disj_conj_distribL: (?P \<or> ?Q \<and> ?R) = ((?P \<or> ?Q) \<and> (?P \<or> ?R))
  HOL.disj_conj_distribR: (?P \<and> ?Q \<or> ?R) = ((?P \<or> ?R) \<and> (?Q \<or> ?R))
*)

lemma q21:
  "y \<noteq> z \<Longrightarrow> (z \<noteq> x \<and> y = x) = (y = x)"
  by auto

lemma q22:
  "(z \<noteq> x \<and> y = x) = (z \<noteq> y \<and> y = x)"
  by auto

lemma q23:
  "P (z \<noteq> x \<and> y = x) = P (z \<noteq> y \<and> y = x)"
proof -
  have "(z = y \<or> y \<noteq> x) \<and> (z = x \<or> y \<noteq> x) \<or> P (z \<noteq> x \<and> y = x) = P (z \<noteq> y \<and> y = x)"
    by blast
  then show ?thesis
    by auto
qed

lemma q24:
  "(Task \<noteq> x \<and>
        Project \<noteq> x \<and>
        Customer \<noteq> x \<and> Employee \<noteq> x \<and> Person = x) = (Person = x)"
  by auto

lemma q25:
  "(Task \<noteq> x \<and>
        Project \<noteq> x \<and>
        Customer \<noteq> x \<and> Employee \<noteq> x \<and> Person = x \<and> x \<le> Person) = (Person = x)"
  by auto

lemma q26:
  "z = (THE x. z \<noteq> x) \<Longrightarrow> False"

lemma q26:
  "(THE x. z \<noteq> x \<and> P x) = (THE x. P x)"

text \<open>
\<^verbatim>\<open>context Employee:
name : String[1]\<close>\<close>
lemma
  "\<Gamma>(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AttributeCall (Var STR ''self'') DotCall STR ''name'' : String[1]"
  apply (auto simp add: attributes_classes1_def)
  unfolding Least_def HOL.imp_conv_disj HOL.conj_disj_distribL apply auto
  apply (metis (mono_tags, lifting) classes1.distinct(15) classes1.distinct(17) classes1.simps(14) classes1.simps(20) eq_iff theI)
  apply (metis (mono_tags, lifting) classes1.distinct(15) classes1.distinct(17) classes1.simps(14) classes1.simps(20) eq_iff theI)
  apply (metis (mono_tags, lifting) classes1.distinct(15) classes1.distinct(17) classes1.simps(14) classes1.simps(20) eq_iff theI)
  apply (metis (mono_tags, lifting) classes1.distinct(15) classes1.distinct(17) classes1.simps(14) classes1.simps(20) eq_iff theI)
  done

text \<open>
\<^verbatim>\<open>context Employee:
projects : Set(Project[1])\<close>\<close>
lemma
  "\<Gamma>(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AssociationEndCall (Var STR ''self'') DotCall STR ''projects'' None : Set Project[1]"
  apply auto

text \<open>
\<^verbatim>\<open>context Employee:
projects.members : Bag(Employee[1])\<close>\<close>
lemma
  "\<Gamma>(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
  AssociationEndCall (AssociationEndCall (Var STR ''self'')
      DotCall STR ''projects'' None)
    DotCall STR ''members'' None : Bag Employee[1]"
  apply simp

text \<open>
\<^verbatim>\<open>Project[?].allInstances() : Set(Project[?])\<close>\<close>
lemma
  "\<Gamma> \<turnstile> MetaOperationCall Project[?] AllInstancesOp : Set Project[?]"
  by auto

text \<open>
\<^verbatim>\<open>Project[1]::allProjects() : Set(Project[1])\<close>\<close>
lemma
  "\<Gamma> \<turnstile> StaticOperationCall Project[1] STR ''allProjects'' [] : Set Project[1]"
  apply auto

subsection \<open>Negative Cases\<close>

text \<open>
\<^verbatim>\<open>true = null\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma> \<turnstile> OperationCall (BooleanLiteral True) DotCall EqualOp [NullLiteral] : \<tau>"
  by auto

text \<open>
\<^verbatim>\<open>let x : Boolean[1] = 5 in x and true\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma> \<turnstile>
    Let STR ''x'' (Some Boolean[1]) (IntegerLiteral 5)
      (OperationCall (Var STR ''x'') DotCall AndOp [BooleanLiteral True]) : \<tau>"
  by auto

text \<open>
\<^verbatim>\<open>let x : Sequence String[?] = Sequence{'abc', 'zxc'} in
x->closure(it | 1)\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma> \<turnstile>
    Let STR ''x'' (Some (Sequence String[?])) (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (ClosureIteratorCall (Var STR ''x'') ArrowCall [STR ''it''] None
      (IntegerLiteral 1)) : \<tau>"
  by auto

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}->max()\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma> \<turnstile>
    OperationCall (CollectionLiteral SequenceKind
                [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
                 CollectionItem NullLiteral])
        ArrowCall CollectionMaxOp [] : \<tau>"
  apply auto

end

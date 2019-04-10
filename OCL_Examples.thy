(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
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
  by (simp add: sup_least_classes1)

end

code_pred subclass1 .

fun subclass1_fun where
  "subclass1_fun Object \<C> = False"
| "subclass1_fun Person \<C> = (\<C> = Object)"
| "subclass1_fun Employee \<C> = (\<C> = Object \<or> \<C> = Person)"
| "subclass1_fun Customer \<C> = (\<C> = Object \<or> \<C> = Person)"
| "subclass1_fun Project \<C> = (\<C> = Object)"
| "subclass1_fun Task \<C> = (\<C> = Object)"
| "subclass1_fun Sprint \<C> = (\<C> = Object)"

lemma less_classes1_code [code]:
  "(<) = subclass1_fun"
proof (intro ext iffI)
  fix \<C> \<D> :: "classes1"
  show "\<C> < \<D> \<Longrightarrow> subclass1_fun \<C> \<D>"
    unfolding less_classes1_def
    apply (erule subclass1.cases, auto)
    using subclass1_fun.elims(3) by blast
  show "subclass1_fun \<C> \<D> \<Longrightarrow> \<C> < \<D>"
    by (erule subclass1_fun.elims, auto simp add: less_classes1_def subclass1.intros)
qed

lemma less_eq_classes1_code [code]:
  "(\<le>) = (\<lambda>x y. subclass1_fun x y \<or> x = y)"
  unfolding dual_order.order_iff_strict less_classes1_code
  by auto

(*** Object Model ***********************************************************)

section \<open>Object Model\<close>

abbreviation "\<Gamma>\<^sub>0 \<equiv> fmempty :: classes1 type\<^sub>N\<^sub>E env"
declare [[coercion "ObjectType :: classes1 \<Rightarrow> classes1 type"]]
declare [[coercion "phantom :: String.literal \<Rightarrow> classes1 enum"]]

instantiation classes1 :: ocl_object_model
begin

definition "classes_classes1 \<equiv>
  {|Object, Person, Employee, Customer, Project, Task, Sprint|}"

definition "attributes_classes1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type\<^sub>N\<^sub>E)]),
  (Employee, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''position'', String[1])]),
  (Customer, fmap_of_list [
    (STR ''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''cost'', Real[?])]),
  (Task, fmap_of_list [
    (STR ''description'', String[1])])]"

abbreviation "assocs \<equiv> [
  STR ''ProjectManager'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0::nat, \<infinity>::enat, False, True),
    STR ''manager'' \<mapsto>\<^sub>f (Employee, 1, 1, False, False)],
  STR ''ProjectMember'' \<mapsto>\<^sub>f [
    STR ''member_of'' \<mapsto>\<^sub>f (Project, 0, \<infinity>, False, False),
    STR ''members'' \<mapsto>\<^sub>f (Employee, 1, 20, True, True)],
  STR ''ManagerEmployee'' \<mapsto>\<^sub>f [
    STR ''line_manager'' \<mapsto>\<^sub>f (Employee, 0, 1, False, False),
    STR ''project_manager'' \<mapsto>\<^sub>f (Employee, 0, \<infinity>, False, False),
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
static def: allProjects() : Set(Project[1]) =
              Project[1].allInstances()
\end{verbatim}\<close>

definition "operations_classes1 \<equiv> [
  (STR ''membersCount'', Project[1], [], Integer[1], False,
   Some (
    (AssociationEndCall (Var STR ''self'') DotCall None STR ''members'')\<^bold>-\<^bold>>size())),
  (STR ''membersByName'', Project[1], [(STR ''mn'', String[1], In)],
    (Set Employee[\<^bold>1])[1], False,
   Some (
    (AssociationEndCall (Var STR ''self'') DotCall None STR ''members'')\<^bold>-\<^bold>>select(
    STR ''member'' \<^bold>|
      (AttributeCall (Var STR ''member'') DotCall STR ''name'') \<^bold>=
      (Var STR ''mn'')))),
  (STR ''allProjects'', Project[1], [], (Set Project[\<^bold>1])[1], True,
   Some (MetaOperationCall Project[1] AllInstancesOp))
  ] :: (classes1 type\<^sub>N\<^sub>E, classes1 expr) oper_spec list"

definition "literals_classes1 \<equiv> fmap_of_list [
  (STR ''E1'' :: classes1 enum, {|STR ''A'', STR ''B''|}),
  (STR ''E2'', {|STR ''C'', STR ''D'', STR ''E''|})]"


lemma assoc_end_min_less_eq_max:
  "assoc |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   role |\<in>| fmdom ends  \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_min end \<le> assoc_end_max end"
  unfolding assoc_end_min_def assoc_end_max_def
  using zero_enat_def one_enat_def numeral_eq_enat apply auto
  by (metis enat_ord_number(1) numeral_One one_le_numeral)

lemma association_ends_unique:
  assumes "association_ends' classes assocs \<C> from role end\<^sub>1"
      and "association_ends' classes assocs \<C> from role end\<^sub>2"
    shows "end\<^sub>1 = end\<^sub>2"
proof -
  have "\<not> association_ends_not_unique' classes assocs" by eval
  with assms show ?thesis
    using association_ends_not_unique'.simps by blast
qed

instance
  apply standard
  unfolding associations_classes1_def
  using assoc_end_min_less_eq_max apply blast
  using association_ends_unique by blast

end

code_pred [show_modes] non_strict_op .
(*
values "{x. \<Gamma>\<^sub>0(STR ''x'' \<mapsto>\<^sub>f OclAny[?]) \<turnstile>\<^sub>E CollectionLiteral SetKind [
  CollectionItem (IntegerLiteral 1),
  CollectionItem NullLiteral,
  CollectionItem (Var STR ''x'')] : x}"
*)

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>
(*
lemma ex_alt_simps [simp]:
  "\<exists>a. a"
  "\<exists>a. \<not> a"
  "(\<exists>a. (a \<longrightarrow> P) \<and> a) = P"
  "(\<exists>a. \<not> a \<and> (\<not> a \<longrightarrow> P)) = P"
  by auto

declare numeral_eq_enat [simp]

(*lemmas basic_type_le_less [simp] = Orderings.order_class.le_less
  for x y :: "'a basic_type"*)

declare element_type_alt_simps [simp]
declare update_element_type.simps [simp]
declare to_unique_collection.simps [simp]
declare to_nonunique_collection.simps [simp]
declare to_ordered_collection.simps [simp]

declare assoc_end_class_def [simp]
declare assoc_end_min_def [simp]
declare assoc_end_max_def [simp]
declare assoc_end_ordered_def [simp]
declare assoc_end_unique_def [simp]

declare oper_name_def [simp]
declare oper_context_def [simp]
declare oper_params_def [simp]
declare oper_result_def [simp]
declare oper_static_def [simp]
declare oper_body_def [simp]

declare oper_in_params_def [simp]
declare oper_out_params_def [simp]

declare assoc_end_type_def [simp]
declare oper_type_def [simp]

declare op_type_alt_simps [simp]
declare typing_alt_simps [simp]
declare normalize_alt_simps [simp]
declare nf_typing.simps [simp]
*)
declare subclass1.intros [intro]
declare less_classes1_def [simp]

declare literals_classes1_def [simp]

lemma attribute_Employee_name [simp]:
  "attribute Employee STR ''name'' \<D> \<tau> =
   (\<D> = Employee \<and> \<tau> = String[1])"
proof -
  have "attribute Employee STR ''name'' Employee String[1]"
    by eval
  thus ?thesis
    using attribute_det by blast
qed

lemma association_end_Project_members [simp]:
  "association_end Project None STR ''members'' \<D> \<tau> =
   (\<D> = Project \<and> \<tau> = (Employee, 1, 20, True, True))"
proof -
  have "association_end Project None STR ''members''
          Project (Employee, 1, 20, True, True)"
    by eval
  thus ?thesis
    using association_end_det by blast
qed

lemma association_end_Employee_projects_simp [simp]:
  "association_end Employee None STR ''projects'' \<D> \<tau> =
   (\<D> = Employee \<and> \<tau> = (Project, 0, \<infinity>, False, True))"
proof -
  have "association_end Employee None STR ''projects''
          Employee (Project, 0, \<infinity>, False, True)"
    by eval
  thus ?thesis
    using association_end_det by blast
qed

lemma static_operation_Project_allProjects [simp]:
  "static_operation \<langle>Project\<rangle>\<^sub>\<T>[1] STR ''allProjects'' [] oper =
   (oper = (STR ''allProjects'', \<langle>Project\<rangle>\<^sub>\<T>[1], [], (Set \<langle>Project\<rangle>\<^sub>\<T>[\<^bold>1])[1], True,
     Some (MetaOperationCall \<langle>Project\<rangle>\<^sub>\<T>[1] AllInstancesOp)))"
proof -
  have "static_operation \<langle>Project\<rangle>\<^sub>\<T>[1] STR ''allProjects'' []
    (STR ''allProjects'', \<langle>Project\<rangle>\<^sub>\<T>[1], [], (Set \<langle>Project\<rangle>\<^sub>\<T>[\<^bold>1])[1], True,
     Some (MetaOperationCall \<langle>Project\<rangle>\<^sub>\<T>[1] AllInstancesOp))"
    by eval
  thus ?thesis
    using static_operation_det by blast
qed

(*** Basic Types ************************************************************)

section \<open>Basic Types\<close>

subsection \<open>Positive Cases\<close>

lemma "UnlimitedNatural < (Real :: classes1 type)" by simp
lemma "\<langle>Employee\<rangle>\<^sub>\<T> < \<langle>Person\<rangle>\<^sub>\<T>" by auto
lemma "\<langle>Person\<rangle>\<^sub>\<T> \<le> OclAny" by simp

subsection \<open>Negative Cases\<close>

lemma "\<not> String \<le> (Boolean :: classes1 type)" by simp

(*** Types ******************************************************************)

section \<open>Types\<close>

subsection \<open>Positive Cases\<close>

lemma "Integer[?] < (OclAny[?] :: classes1 type\<^sub>N\<^sub>E)" by simp
lemma "(Collection Real[\<^bold>?])[1] < (OclAny[1] :: classes1 type\<^sub>N\<^sub>E)" by simp
lemma "(Set (Collection Boolean[\<^bold>1])[\<^bold>1])[1] < (OclAny[?] :: classes1 type\<^sub>N\<^sub>E)" by simp
lemma "(Set (Bag Boolean[\<^bold>1])[\<^bold>1])[1] < (Set (Collection (Boolean[\<^bold>?] :: classes1 type\<^sub>N))[\<^bold>1])[?]"
  by simp
lemma "(Tuple (fmap_of_list [(STR ''a'', Boolean[\<^bold>1]), (STR ''b'', Integer[\<^bold>1])]))[1] <
       (Tuple (fmap_of_list [(STR ''a'', Boolean[\<^bold>?] :: classes1 type\<^sub>N)]))[1!]" by code_simp

lemma "Integer[1] \<squnion> (Real[?] :: classes1 type\<^sub>N\<^sub>E) = Real[?]" by simp
lemma "Set Integer[\<^bold>1] \<squnion> Set (Real[\<^bold>1] :: classes1 type\<^sub>N) = Set Real[\<^bold>1]" by simp
lemma "Set Integer[\<^bold>1] \<squnion> Bag (Boolean[\<^bold>?] :: classes1 type\<^sub>N) =
  Collection OclAny[\<^bold>?]" by simp
lemma "(Set Integer[\<^bold>1])[1] \<squnion> (Real[1!] :: classes1 type\<^sub>N\<^sub>E) = OclAny[1!]" by simp

subsection \<open>Negative Cases\<close>

lemma "\<not> (OrderedSet Boolean[\<^bold>1])[1] < (Set (Boolean[\<^bold>1] :: classes1 type\<^sub>N))[1]" by simp

(*** Typing *****************************************************************)

(*
declare is_iterable_type.simps [simp]
declare iterable_type.simps [simp]
declare collection_type.simps [simp]
declare collection_type\<^sub>N.simps [simp]
declare map_type.simps [simp]
declare map_type\<^sub>N.simps [simp]
declare map_type\<^sub>T.simps [simp]

thm collection_type\<^sub>T.simps

lemma collection_type\<^sub>T_alt_simps:
  "collection_type\<^sub>T \<tau> k \<sigma> = 
     (Collection \<sigma> = \<tau> \<and> CollectionKind = k \<or>
      Set \<sigma> = \<tau> \<and> SetKind = k \<or>
      OrderedSet \<sigma> = \<tau> \<and> OrderedSetKind = k \<or>
      Bag \<sigma> = \<tau> \<and> BagKind = k \<or>
      Sequence \<sigma> = \<tau> \<and> SequenceKind = k)"
  by (auto simp add: collection_type\<^sub>T.simps)

declare collection_type\<^sub>T_alt_simps [simp]
declare op_result_type_is_errorable_def [simp]
*)


section \<open>Typing\<close>

subsection \<open>Positive Cases\<close>



term "Sequence{}"
term "Sequence{x}"
term "Sequence{x\<^bold>, y}"
term "Sequence{x\<^bold>.\<^bold>.y}"
term "Sequence{x\<^bold>, y\<^bold>, z}"
term "Sequence{x\<^bold>, y\<^bold>, Set{x2\<^bold>, Sequence{x \<^bold>.\<^bold>. y}\<^bold>, z}}"




lemma ex_alt_simps [simp]:
  "\<exists>a. a"
  "\<exists>a. \<not> a"
  "(\<exists>a. (a \<longrightarrow> P) \<and> a) = P"
  "(\<exists>a. \<not> a \<and> (\<not> a \<longrightarrow> P)) = P"
  "(\<forall>x. x) = False"
  by auto
(*
declare numeral_eq_enat [simp]

(*lemmas basic_type_le_less [simp] = Orderings.order_class.le_less
  for x y :: "'a basic_type"*)

declare element_type_alt_simps [simp]
declare update_element_type.simps [simp]
declare to_unique_collection.simps [simp]
declare to_nonunique_collection.simps [simp]
declare to_ordered_collection.simps [simp]

declare assoc_end_class_def [simp]
declare assoc_end_min_def [simp]
declare assoc_end_max_def [simp]
declare assoc_end_ordered_def [simp]
declare assoc_end_unique_def [simp]

declare oper_name_def [simp]
declare oper_context_def [simp]
declare oper_params_def [simp]
declare oper_result_def [simp]
declare oper_static_def [simp]
declare oper_body_def [simp]

declare oper_in_params_def [simp]
declare oper_out_params_def [simp]

declare assoc_end_type_def [simp]
declare oper_type_def [simp]


thm collection_type\<^sub>T.simps


declare op_result_type_is_errorable_def [simp]

declare op_type_alt_simps [simp]
declare typing_alt_simps [simp]
*)
thm typing_alt_simps

declare normalize_alt_simps [simp]
declare nf_typing.simps [simp]

declare typing_alt_simps [simp]


lemma collection_type\<^sub>N_left_simps:
  "collection_type\<^sub>N (Required \<tau>) k \<sigma> n = (n = False \<and> collection_type\<^sub>T \<tau> k \<sigma>)"
  "collection_type\<^sub>N (Optional \<tau>) k \<sigma> n = (n = True \<and> collection_type\<^sub>T \<tau> k \<sigma>)"
  by (auto simp add: collection_type\<^sub>N.simps collection_type\<^sub>T.simps)

lemma collection_type\<^sub>N_right_simps:
  "collection_type\<^sub>N \<tau> k \<sigma> False = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> collection_type\<^sub>T \<rho> k \<sigma>)"
  "collection_type\<^sub>N \<tau> k \<sigma> True = (\<exists>\<rho>. \<tau> = Optional \<rho> \<and> collection_type\<^sub>T \<rho> k \<sigma>)"
  by (auto simp add: collection_type\<^sub>N.simps collection_type\<^sub>T.simps)

lemma collection_type_left_simps:
  "collection_type (ErrorFree \<tau>) k \<sigma> n =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "collection_type (Errorable \<tau>) k \<sigma> n =
   (\<exists>\<rho>. \<sigma> = Errorable \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "Ex (collection_type (ErrorFree \<tau>) k \<sigma>) =
   (\<exists>\<rho> n. \<sigma> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "Ex (collection_type (Errorable \<tau>) k \<sigma>) =
   (\<exists>\<rho> n. \<sigma> = Errorable \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  by (auto simp add: collection_type.simps) auto

lemma collection_type_right_simps:
  "collection_type \<tau> k (ErrorFree \<sigma>) n =
   (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  "collection_type \<tau> k (Errorable \<sigma>) n =
   (\<exists>\<rho>. \<tau> = Errorable \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  by (auto simp add: collection_type.simps)

declare collection_type\<^sub>T.simps [simp]
declare collection_type\<^sub>N.simps [simp]
(*declare collection_type.simps [simp]*)
(*declare collection_type\<^sub>N_left_simps [simp]
declare collection_type\<^sub>N_right_simps [simp]*)
declare collection_type_left_simps [simp]
declare collection_type_right_simps [simp]

lemma map_type\<^sub>T_left_simps:
  "map_type\<^sub>T (Map \<tau> \<sigma>) \<rho> \<upsilon> = (\<tau> = \<rho> \<and> \<sigma> = \<upsilon>)"
  by (auto simp add: map_type\<^sub>T.simps)

lemma map_type\<^sub>N_left_simps:
  "map_type\<^sub>N (Required \<tau>) \<sigma> \<rho> n = (n = False \<and> map_type\<^sub>T \<tau> \<sigma> \<rho>)"
  "map_type\<^sub>N (Optional \<tau>) \<sigma> \<rho> n = (n = True \<and> map_type\<^sub>T \<tau> \<sigma> \<rho>)"
  by (auto simp add: map_type\<^sub>N.simps)

lemma map_type_left_simps:
  "map_type (ErrorFree \<tau>) \<sigma> \<rho> n =
   (\<exists>\<upsilon> \<psi>. \<sigma> = ErrorFree \<upsilon> \<and> \<rho> = ErrorFree \<psi> \<and> map_type\<^sub>N \<tau> \<upsilon> \<psi> n)"
  "map_type (Errorable \<tau>) \<sigma> \<rho> n =
   (\<exists>\<upsilon> \<psi>. \<sigma> = Errorable \<upsilon> \<and> \<rho> = Errorable \<psi> \<and> map_type\<^sub>N \<tau> \<upsilon> \<psi> n)"
  "Ex (map_type (ErrorFree \<tau>) \<sigma> \<rho>) =
   (\<exists>\<upsilon> \<psi> n. \<sigma> = ErrorFree \<upsilon> \<and> \<rho> = ErrorFree \<psi> \<and> map_type\<^sub>N \<tau> \<upsilon> \<psi> n)"
  "Ex (map_type (Errorable \<tau>) \<sigma> \<rho>) =
   (\<exists>\<upsilon> \<psi> n. \<sigma> = Errorable \<upsilon> \<and> \<rho> = Errorable \<psi> \<and> Ex (map_type\<^sub>N \<tau> \<upsilon> \<psi>))"
  by (auto simp add: map_type.simps) auto

(*declare map_type\<^sub>T_left_simps [simp]*)
declare map_type\<^sub>T.simps [simp]
declare map_type\<^sub>N_left_simps [simp]
declare map_type_left_simps [simp]

thm map_type\<^sub>T.simps

declare is_iterable_type.simps [simp]
declare iterable_type.simps []

thm iterable_type.simps

thm typing_alt_simps(30)

declare mk_iterator_def [simp]
declare to_nonunique_collection_type\<^sub>T.simps [simp]
declare to_nonunique_collection_type\<^sub>N.simps [simp]
declare to_nonunique_collection_type.simps []

declare update_element_type\<^sub>T.simps [simp]
declare update_element_type\<^sub>N.simps [simp]
declare update_element_type.simps [simp]


lemma to_nonunique_collection_type_left_simps:
  "to_nonunique_collection_type (ErrorFree \<tau>) \<sigma> =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> to_nonunique_collection_type\<^sub>N \<tau> \<rho>)"
  "to_nonunique_collection_type (Errorable \<tau>) \<sigma> =
   (\<exists>\<rho>. \<sigma> = Errorable \<rho> \<and> to_nonunique_collection_type\<^sub>N \<tau> \<rho>)"
  by (simp_all add: to_nonunique_collection_type.simps)

lemma iterable_type_left_simps:
  "iterable_type (ErrorFree \<tau>) \<sigma> =
   (\<exists>k \<rho> \<upsilon> n. \<sigma> = \<rho> \<and>
      (collection_type (ErrorFree \<tau>) k \<rho> n \<or>
       map_type (ErrorFree \<tau>) \<rho> \<upsilon> n))"
  "iterable_type (Errorable \<tau>) \<sigma> =
   (\<exists>k \<rho> \<upsilon> n. \<sigma> = \<rho> \<and>
      (collection_type (Errorable \<tau>) k \<rho> n \<or>
       map_type (Errorable \<tau>) \<rho> \<upsilon> n))"
  by (auto simp add: iterable_type.simps; blast)+

lemma ex_iterable_type_left_simps:
  "Ex (iterable_type (ErrorFree \<tau>)) =
   (\<exists>k \<rho> \<upsilon> n.
      (collection_type (ErrorFree \<tau>) k \<rho> n \<or>
       map_type (ErrorFree \<tau>) \<rho> \<upsilon> n))"
  "Ex (iterable_type (Errorable \<tau>)) =
   (\<exists>k \<rho> \<upsilon> n.
      (collection_type (Errorable \<tau>) k \<rho> n \<or>
       map_type (Errorable \<tau>) \<rho> \<upsilon> n))"
  using iterable_type_left_simps by blast+


declare iterable_type_left_simps [simp]
declare ex_iterable_type_left_simps [simp]

declare op_type_alt_simps [simp]
declare op_result_type_is_errorable_def [simp]


declare numeral_eq_enat [simp]

declare assoc_end_class_def [simp]
declare assoc_end_min_def [simp]
declare assoc_end_max_def [simp]
declare assoc_end_ordered_def [simp]
declare assoc_end_unique_def [simp]

declare oper_name_def [simp]
declare oper_context_def [simp]
declare oper_params_def [simp]
declare oper_result_def [simp]
declare oper_static_def [simp]
declare oper_body_def [simp]

declare oper_in_params_def [simp]
declare oper_out_params_def [simp]

declare assoc_end_type_def [simp]
declare oper_type_def [simp]

declare is_collection_type.simps [simp]
declare to_single_type.simps []

thm to_single_type.simps

text \<open>
  The first argument gets simpler, so the following simplification rules
  does not get stuck.\<close>

lemma to_single_type_left_simps [simp]:
  "to_single_type (ErrorFree \<tau>) \<sigma> =
   ((\<not> is_collection_type (ErrorFree \<tau>) \<and> (ErrorFree \<tau>) = \<sigma>) \<or>
    (\<exists>k \<upsilon> n. collection_type (ErrorFree \<tau>) k \<upsilon> n \<and> to_single_type \<upsilon> \<sigma>))"
  "to_single_type (Errorable \<tau>) \<sigma> =
   ((\<not> is_collection_type (Errorable \<tau>) \<and> (Errorable \<tau>) = \<sigma>) \<or>
    (\<exists>k \<upsilon> n. collection_type (Errorable \<tau>) k \<upsilon> n \<and> to_single_type \<upsilon> \<sigma>))"
  by (subst to_single_type.simps; auto)+

declare to_nonunique_collection_type_left_simps []
declare to_nonunique_collection_type.simps [simp]




declare mk_iterate_def [simp]


declare to_unique_collection_type\<^sub>T.simps [simp]
declare to_unique_collection_type\<^sub>N.simps [simp]
declare to_unique_collection_type.simps [simp]

abbreviation "name \<equiv> Attribute STR ''name''"
abbreviation "projects \<equiv> AssociationEnd None STR ''projects''"
abbreviation "members \<equiv> AssociationEnd None STR ''members''"
abbreviation "allProjects \<equiv> STR ''allProjects''"




text \<open>
\<^verbatim>\<open>E1::A : E1[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> EnumLiteral STR ''E1'' STR ''A'' : (Enum STR ''E1'')[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> \<^bold>t\<^bold>r\<^bold>u\<^bold>e or \<^bold>f\<^bold>a\<^bold>l\<^bold>s\<^bold>e : Boolean[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> \<^bold>n\<^bold>u\<^bold>l\<^bold>l and \<^bold>t\<^bold>r\<^bold>u\<^bold>e : Boolean[?]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> \<^bold>l\<^bold>e\<^bold>t x \<^bold>: Real[1] \<^bold>= \<^bold>5 \<^bold>i\<^bold>n \<lparr>x\<rparr> / \<^bold>7 : Real[1!]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> \<^bold>n\<^bold>u\<^bold>l\<^bold>l\<^bold>.oclIsUndefined() : Boolean[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5\<^bold>, \<^bold>n\<^bold>u\<^bold>l\<^bold>l} : (Sequence Integer[\<^bold>?])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5\<^bold>, \<^bold>n\<^bold>u\<^bold>l\<^bold>l}\<^bold>.oclIsUndefined() : (Sequence Boolean[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5}\<^bold>-\<^bold>>product(Set{StringLiteral ''a''\<^bold>, StringLiteral ''b''}) :
    (Set (Tuple(STR ''first'' \<^bold>: Integer[\<^bold>1]\<^bold>, STR ''second'' \<^bold>: String[\<^bold>1]))[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5\<^bold>, \<^bold>n\<^bold>u\<^bold>l\<^bold>l}\<^bold>?\<^bold>-\<^bold>>iterate(x\<^bold>; acc \<^bold>: Real[1] \<^bold>= \<^bold>0 \<^bold>| \<lparr>acc\<rparr> \<^bold>+ \<lparr>x\<rparr>) : Real[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5\<^bold>, \<^bold>n\<^bold>u\<^bold>l\<^bold>l}\<^bold>?\<^bold>-\<^bold>>max() : Integer[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> \<^bold>l\<^bold>e\<^bold>t x \<^bold>: (Sequence String[\<^bold>?])[1] \<^bold>=
          Sequence{StringLiteral ''abc''\<^bold>, StringLiteral ''zxc''} \<^bold>i\<^bold>n
   \<lparr>x\<rparr>\<^bold>-\<^bold>>any(it \<^bold>| \<lparr>it\<rparr> \<^bold>= StringLiteral ''test'') : String[?!]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> \<^bold>l\<^bold>e\<^bold>t x \<^bold>: (Sequence String[\<^bold>?])[1] \<^bold>=
          Sequence{StringLiteral ''abc''\<^bold>, StringLiteral ''zxc''} \<^bold>i\<^bold>n
   \<lparr>x\<rparr>\<^bold>?\<^bold>-\<^bold>>closure(it \<^bold>| \<lparr>it\<rparr>) : (OrderedSet String[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0(self \<mapsto>\<^sub>f Employee[1]) \<turnstile> \<lparr>self\<rparr>\<^bold>.name : String[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0(self \<mapsto>\<^sub>f Employee[1]) \<turnstile> \<lparr>self\<rparr>\<^bold>.projects : (Set Project[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0(self \<mapsto>\<^sub>f Employee[1]) \<turnstile> \<lparr>self\<rparr>\<^bold>.projects\<^bold>.members : (Bag Employee[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Project[?]\<^bold>.allInstances() : (Set Project[\<^bold>?])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Project[1]\<^bold>:\<^bold>:allProjects( ) : (Set Project[\<^bold>1])[1]"
  by simp

subsection \<open>Negative Cases\<close>

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> \<^bold>t\<^bold>r\<^bold>u\<^bold>e \<^bold>= \<^bold>n\<^bold>u\<^bold>l\<^bold>l : \<tau>"
  by simp

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> \<^bold>l\<^bold>e\<^bold>t x \<^bold>: Boolean[1] \<^bold>= \<^bold>5 \<^bold>i\<^bold>n \<lparr>x\<rparr> and \<^bold>t\<^bold>r\<^bold>u\<^bold>e : \<tau>"
  by simp

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> \<^bold>l\<^bold>e\<^bold>t x \<^bold>: (Sequence String[\<^bold>?])[1] \<^bold>=
    Sequence{StringLiteral ''abc''\<^bold>, StringLiteral ''zxc''} \<^bold>i\<^bold>n
    \<lparr>x\<rparr>\<^bold>-\<^bold>>closure(it \<^bold>| \<^bold>1) : \<tau>"
  by simp

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5\<^bold>, \<^bold>n\<^bold>u\<^bold>l\<^bold>l}\<^bold>-\<^bold>>max() : \<tau>"
proof -
  have "\<not> operation_defined (Integer[?] :: classes1 type\<^sub>N\<^sub>E) STR ''max'' [Integer[?]]"
    by eval
  thus ?thesis by simp
qed

(*** Code *******************************************************************)

section \<open>Code\<close>

subsection \<open>Positive Cases\<close>

values "{(\<D>, \<tau>). attribute Employee STR ''name'' \<D> \<tau>}"
values "{(\<D>, end). association_end Employee None STR ''employees'' \<D> end}"
values "{(\<D>, end). association_end Employee (Some STR ''project_manager'')
  STR ''employees'' \<D> end}"
values "{op. operation Project[1] STR ''membersCount'' [] op}"
values "{op. operation Project[1] STR ''membersByName'' [String[1]] op}"
value "has_literal STR ''E1'' STR ''A''"

text \<open>
\<^verbatim>\<open>context Employee:
projects.members : Bag(Employee[1])[1]\<close>\<close>
values "{\<tau>. \<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile> \<lparr>STR ''self''\<rparr>\<^bold>.projects\<^bold>.members : \<tau>}"

subsection \<open>Negative Cases\<close>

value "has_literal STR ''E1'' STR ''C''"
values "{(\<D>, \<tau>). attribute Employee STR ''name2'' \<D> \<tau>}"
values "{\<tau>. \<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1\<^bold>.\<^bold>.\<^bold>5\<^bold>, \<^bold>n\<^bold>u\<^bold>l\<^bold>l}\<^bold>-\<^bold>>max() : \<tau>}"

end

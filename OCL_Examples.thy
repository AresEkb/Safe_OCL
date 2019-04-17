(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Examples\<close>
theory OCL_Examples
  imports OCL_Normalization
begin

(*
instantiation expr :: (type) numeral
begin

definition "one_expr \<equiv> Literal (IntegerLiteral 1)"

fun plus_expr :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" where
  "plus_expr (Literal (IntegerLiteral x)) (Literal (IntegerLiteral y)) =
      (Literal (IntegerLiteral (x + y)))"
| "plus_expr _ _ = Literal NullLiteral"

lemma literal_expr_add_assoc:
  "(Literal a + Literal b) + Literal c = Literal a + (Literal b + Literal c)"
  for a b c :: "'a literal_expr"
  by (cases a; simp; cases b; simp; cases c; simp)

lemma expr_add_assoc:
  "(a + b) + c = a + (b + c)"
  for a b c :: "'a expr"
  by (cases a; simp; cases b; simp; cases c; simp add: literal_expr_add_assoc)

instance
  apply standard
  by (simp add: expr_add_assoc)
end

term "Set{}"
term "Set{\<^bold>1..\<^bold>2, \<^bold>3, 3}"
term "Set{\<^bold>1, \<^bold>2}"

term "Set{\<^bold>1 .. \<^bold>2, \<^bold>3}"

term "Set Integer[\<^bold>1]"
*)

(*** Symbols ****************************************************************)

section \<open>Symbols\<close>

abbreviation "self \<equiv> STR ''self''"
abbreviation "it \<equiv> STR ''it''"

abbreviation "name \<equiv> STR ''name''"
abbreviation "position \<equiv> STR ''position''"
abbreviation "vip \<equiv> STR ''vip''"
abbreviation "cost \<equiv> STR ''cost''"
abbreviation "description \<equiv> STR ''description''"
abbreviation "priority \<equiv> STR ''priority''"

abbreviation "Priority \<equiv> STR ''Priority''"
abbreviation "Low \<equiv> STR ''Low''"
abbreviation "Medium \<equiv> STR ''Medium''"
abbreviation "High \<equiv> STR ''High''"

abbreviation "ProjectManager \<equiv> STR ''ProjectManager''"
abbreviation "projects \<equiv> STR ''projects''"
abbreviation "manager \<equiv>  STR ''manager''"
abbreviation "ProjectMember \<equiv>  STR ''ProjectMember''"
abbreviation "memberOf \<equiv>  STR ''memberOf''"
abbreviation "members \<equiv>  STR ''members''"
abbreviation "ManagerEmployee \<equiv>  STR ''ManagerEmployee''"
abbreviation "lineManager \<equiv>  STR ''lineManager''"
abbreviation "projectManager \<equiv>  STR ''projectManager''"
abbreviation "employees \<equiv>  STR ''employees''"
abbreviation "ProjectCustomer \<equiv>  STR ''ProjectCustomer''"
abbreviation "customer \<equiv>  STR ''customer''"
abbreviation "ProjectTask \<equiv>  STR ''ProjectTask''"
abbreviation "project \<equiv>  STR ''project''"
abbreviation "tasks \<equiv>  STR ''tasks''"
abbreviation "SprintTaskAssignee \<equiv>  STR ''SprintTaskAssignee''"
abbreviation "sprint \<equiv>  STR ''sprint''"
abbreviation "assignee \<equiv>  STR ''assignee''"

abbreviation "membersCount \<equiv>  STR ''membersCount''"
abbreviation "membersByName \<equiv>  STR ''membersByName''"
abbreviation "allProjects \<equiv>  STR ''allProjects''"

definition "literal_to_call_expr_map \<equiv> fmap_of_list [
  (name, Attribute),
  (position, Attribute),
  (vip, Attribute),
  (cost, Attribute),
  (description, Attribute),
  (priority, Attribute),
  (projects, AssociationEnd None),
  (members, AssociationEnd None),
  (memberOf, AssociationEnd None),
  (manager, AssociationEnd None),
  (lineManager, AssociationEnd None),
  (projectManager, AssociationEnd None),
  (employees, AssociationEnd None),
  (customer, AssociationEnd None),
  (project, AssociationEnd None),
  (tasks, AssociationEnd None),
  (sprint, AssociationEnd None),
  (assignee, AssociationEnd None)]"

definition "literal_to_call_expr lit \<equiv> the (fmlookup literal_to_call_expr_map lit) lit"

(*** Model ******************************************************************)

section \<open>Model\<close>

datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

inductive subclass1 where
  "c \<noteq> Object \<Longrightarrow>
   subclass1 c Object"
| "subclass1 Employee Person"
| "subclass1 Customer Person"

abbreviation "\<Gamma>\<^sub>0 \<equiv> fmempty :: classes1 type\<^sub>N\<^sub>E env"

declare [[coercion "ObjectType :: classes1 \<Rightarrow> classes1 type"]]
declare [[coercion "phantom :: String.literal \<Rightarrow> classes1 enum_type"]]
declare [[coercion "Enum :: classes1 enum_type \<Rightarrow> classes1 type"]]
declare [[coercion "StringLiteral :: string \<Rightarrow> classes1 literal_expr"]]
declare [[coercion "literal_to_call_expr :: String.literal \<Rightarrow> classes1 call_expr"]]

(* TODO: Заменить бесконечность на звездочку *)

definition "model_spec \<equiv>

  enum Priority { Low, Medium, High }

  class Person
    name : String[1]
  
  class Employee
    name : String[1]
    position : String[1]
  
  class Customer
    vip : Boolean[1]
  
  class Project
    name : String[1]
    cost : Real[?]
  
  class Task
    description : String[1]
    priority : Priority[1]

  association ProjectManager
    projects : Project[0..\<infinity>] {unique}
    manager : Employee[1..1]
  
  association ProjectMember
    memberOf : Project[0..\<infinity>]
    members : Employee[1..20] {ordered,unique}
  
  association ManagerEmployee
    lineManager : Employee[0..1]
    projectManager : Employee[0..\<infinity>]
    employees : Employee[3..7]
  
  association ProjectCustomer
    projects : Project[0..\<infinity>] {unique}
    customer : Customer[1..1]
  
  association ProjectTask
    project : Project[1..1]
    tasks : Task[0..\<infinity>] {ordered,unique}
  
  association SprintTaskAssignee
    sprint : Sprint[0..10] {unique}
    tasks : Task[0..5] {unique}
    assignee : Employee[0..1]

  context Project[1]
    def: membersCount() : Integer[1] = \<lparr>self\<rparr>\<^bold>.members->size()

    def: membersByName(name : String[1]) : (Set Employee[\<^bold>1])[1] =
         \<lparr>self\<rparr>\<^bold>.members->select(it | \<lparr>it\<rparr>\<^bold>.name \<^bold>= \<lparr>name\<rparr>)

    static def: allProjects() : (Set Project[\<^bold>1])[1] =
         (MetaOperationCall Project[1] AllInstancesOp)"

(*** Upper Semilattice of Classes *******************************************)

section \<open>Upper Semilattice of Classes\<close>

instantiation classes1 :: semilattice_sup
begin

definition "(<) \<equiv> subclass1"
definition "(\<le>) \<equiv> subclass1\<^sup>=\<^sup>="

primrec sup_classes1 where
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

primrec subclass1_fun where
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
    by (cases \<C>; erule subclass1.cases; simp)
  show "subclass1_fun \<C> \<D> \<Longrightarrow> \<C> < \<D>"
    by (cases \<C>; auto simp add: less_classes1_def subclass1.intros)
qed

lemma less_eq_classes1_code [code]:
  "(\<le>) = (\<lambda>x y. subclass1_fun x y \<or> x = y)"
  unfolding dual_order.order_iff_strict less_classes1_code
  by auto

(*** Object Model ***********************************************************)

section \<open>Object Model\<close>

instantiation classes1 :: ocl_object_model
begin

definition "classes_classes1 \<equiv>
  {|Object, Person, Employee, Customer, Project, Task, Sprint|}"

definition "attributes_classes1 \<equiv> model_spec_attributes model_spec"
definition "associations_classes1 \<equiv> model_spec_assoc_ens model_spec"
definition "association_classes_classes1 \<equiv> fmempty :: classes1 \<rightharpoonup>\<^sub>f assoc"
definition "operations_classes1 \<equiv> model_spec_operations model_spec"
definition "literals_classes1 \<equiv> model_spec_enum_literals model_spec"

abbreviation "assoc_ends \<equiv> model_spec_assoc_ens model_spec"

lemma assoc_end_min_less_eq_max:
  "assoc |\<in>| fmdom assoc_ends \<Longrightarrow>
   fmlookup assoc_ends assoc = Some ends \<Longrightarrow>
   role |\<in>| fmdom ends  \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_min end \<le> assoc_end_max end"
  unfolding object_model_simps object_model_notation_simps model_spec_def
  using zero_enat_def one_enat_def numeral_eq_enat apply auto
  by (metis enat_ord_number(1) numeral_One one_le_numeral)

lemma association_ends_unique:
  assumes "association_ends' classes assoc_ends \<C> from role end\<^sub>1"
      and "association_ends' classes assoc_ends \<C> from role end\<^sub>2"
    shows "end\<^sub>1 = end\<^sub>2"
proof -
  have "\<not> association_ends_not_unique' classes assoc_ends" by eval
  with assms show ?thesis
    using association_ends_not_unique'.simps by blast
qed

instance
  apply standard
  unfolding associations_classes1_def
  using assoc_end_min_less_eq_max apply blast
  using association_ends_unique by blast

end

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>

lemma ex_alt_simps [simp]:
  "\<exists>a. a"
  "\<exists>a. \<not> a"
  "(\<exists>a. (a \<longrightarrow> P) \<and> a) = P"
  "(\<exists>a. \<not> a \<and> (\<not> a \<longrightarrow> P)) = P"
  "(\<exists>a. \<not> a \<and> P \<and> \<not> a) = P"
  "(\<exists>a. a \<and> P \<and> \<not> a) = False"
  "(\<forall>x. x) = False"
  by auto

declare numeral_eq_enat [simp]
declare fmrel_on_fset_alt_def [simp]

declare ocl_syntax_simps [simp]
declare ocl_object_model_simps [simp]
declare ocl_type_helper_simps [simp]
declare ocl_typing_simps [simp]
declare ocl_normalization_simps [simp]

declare model_spec_def [simp]

declare subclass1.simps [simp]
declare less_classes1_def [simp]

declare literal_to_call_expr_def [simp]
declare literal_to_call_expr_map_def [simp]
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
   (oper = (\<langle>Project\<rangle>\<^sub>\<T>[1], STR ''allProjects'', [], (Set \<langle>Project\<rangle>\<^sub>\<T>[\<^bold>1])[1], True,
     Some (MetaOperationCall \<langle>Project\<rangle>\<^sub>\<T>[1] AllInstancesOp)))"
proof -
  have "static_operation \<langle>Project\<rangle>\<^sub>\<T>[1] STR ''allProjects'' []
    (\<langle>Project\<rangle>\<^sub>\<T>[1], STR ''allProjects'', [], (Set \<langle>Project\<rangle>\<^sub>\<T>[\<^bold>1])[1], True,
     Some (MetaOperationCall \<langle>Project\<rangle>\<^sub>\<T>[1] AllInstancesOp))"
    by eval
  thus ?thesis
    using static_operation_det by blast
qed

(*** Basic Types ************************************************************)

section \<open>Basic Types\<close>

subsection \<open>Positive Cases\<close>

lemma "Integer < (Real :: classes1 type)" by simp
lemma "\<langle>Employee\<rangle>\<^sub>\<T> < \<langle>Person\<rangle>\<^sub>\<T>" by auto
lemma "\<langle>Person\<rangle>\<^sub>\<T> \<le> OclAny" by simp

subsection \<open>Negative Cases\<close>

lemma "\<not> String \<le> (Boolean :: classes1 type)" by simp

(*** Types ******************************************************************)

section \<open>Types\<close>

subsection \<open>Positive Cases\<close>

lemma
  "Integer[?] < (OclAny[?] :: classes1 type\<^sub>N\<^sub>E)"
  by simp

lemma
  "(Collection Real[\<^bold>?])[1] < (OclAny[1] :: classes1 type\<^sub>N\<^sub>E)"
  by simp

lemma
  "(Set (Collection Boolean[\<^bold>1])[\<^bold>1])[1] < (OclAny[?] :: classes1 type\<^sub>N\<^sub>E)"
  by simp

lemma
  "(Set (Bag Boolean[\<^bold>1])[\<^bold>1])[1] <
   (Set (Collection (Boolean[\<^bold>?] :: classes1 type\<^sub>N))[\<^bold>1])[?]"
  by simp

lemma
  "Tuple(STR ''a'' : Boolean[\<^bold>1], STR ''b'' : Integer[\<^bold>1])[1] <
   Tuple(STR ''a'' : Boolean[\<^bold>?] :: classes1 type\<^sub>N)[1!]"
  by simp

lemma
  "Integer[1] \<squnion> (Real[?] :: classes1 type\<^sub>N\<^sub>E) = Real[?]"
  by simp

lemma
  "Set Integer[\<^bold>1] \<squnion> Set (Real[\<^bold>1] :: classes1 type\<^sub>N) = Set Real[\<^bold>1]"
  by simp

lemma
  "Set Integer[\<^bold>1] \<squnion> Bag (Boolean[\<^bold>?] :: classes1 type\<^sub>N) = Collection OclAny[\<^bold>?]"
  by simp

lemma
  "(Set Integer[\<^bold>1])[1] \<squnion> (Real[1!] :: classes1 type\<^sub>N\<^sub>E) = OclAny[1!]"
  by simp

subsection \<open>Negative Cases\<close>

lemma
  "\<not> (OrderedSet Boolean[\<^bold>1])[1] < (Set (Boolean[\<^bold>1] :: classes1 type\<^sub>N))[1]"
  by simp

(*** Typing *****************************************************************)

section \<open>Typing\<close>

subsection \<open>Positive Cases\<close>

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Priority\<^bold>:\<^bold>:High : Priority[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> true or false : Boolean[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> null and true : Boolean[?]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> let x : Real[1] = \<^bold>5 in \<lparr>x\<rparr> \<^bold>/ \<^bold>7 : Real[1!]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> null\<^bold>.oclIsUndefined() : Boolean[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5, null} : (Sequence Integer[\<^bold>?])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5, null}\<^bold>.oclIsUndefined() : (Sequence Boolean[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5}->product(Set{''a'', ''b''}) :
    (Set (Tuple(STR ''first'' : Integer[\<^bold>1], STR ''second'' : String[\<^bold>1]))[\<^bold>1])[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5, null}?->
            iterate(x; acc : Real[1] = \<^bold>0 | \<lparr>acc\<rparr> \<^bold>+ \<lparr>x\<rparr>) : Real[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5, null}?->max() : Integer[1]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> let x : (Sequence String[\<^bold>?])[1] = Sequence{''abc'', ''zxc''} in
   \<lparr>x\<rparr>->any(it | \<lparr>it\<rparr> \<^bold>= StringLiteral ''test'') : String[?!]"
  by simp

lemma
  "\<Gamma>\<^sub>0 \<turnstile> let x : (Sequence String[\<^bold>?])[1] =
          Sequence{''abc'', ''zxc''} in
   \<lparr>x\<rparr>?->closure(it | \<lparr>it\<rparr>) : (OrderedSet String[\<^bold>1])[1]"
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
  "\<Gamma>\<^sub>0 \<turnstile> Project[1]::allProjects() : (Set Project[\<^bold>1])[1]"
  by simp

subsection \<open>Negative Cases\<close>

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> true \<^bold>= null : \<tau>"
  by simp

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> let x : Boolean[1] = \<^bold>5 in \<lparr>x\<rparr> and true : \<tau>"
  by simp

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> let x : (Sequence String[\<^bold>?])[1] = Sequence{''abc'', ''zxc''} in
   \<lparr>x\<rparr>->closure(it | \<^bold>1) : \<tau>"
  by simp

lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5, null}->max() : \<tau>"
proof -
  have
    "\<not> operation_defined (Integer[?] :: classes1 type\<^sub>N\<^sub>E) STR ''max'' [Integer[?]]"
    by eval
  thus ?thesis by simp
qed

(*** Code *******************************************************************)

section \<open>Code\<close>

subsection \<open>Positive Cases\<close>

values "{(\<D>, \<tau>). attribute Employee name \<D> \<tau>}"
(* TODO: Тут ошибка. Потому, что если выражение имеет тип,
   то должно иметь и значение. А, нет норм для 1-го варианта
   будут все значения без фильтрации. Но это нужно явно отметить *)
values "{(\<D>, end). association_end Employee None employees \<D> end}"
values "{(\<D>, end).
  association_end Employee (Some projectManager) employees \<D> end}"
values "{op. operation Project[1] membersCount [] op}"
values "{op. operation Project[1] membersByName [String[1]] op}"
values "{\<tau>. \<Gamma>\<^sub>0(self \<mapsto>\<^sub>f Employee[1]) \<turnstile> \<lparr>self\<rparr>\<^bold>.projects\<^bold>.members : \<tau>}"

subsection \<open>Negative Cases\<close>

values "{(\<D>, \<tau>). attribute Employee STR ''name2'' \<D> \<tau>}"
values "{\<tau>. \<Gamma>\<^sub>0 \<turnstile> Sequence{\<^bold>1..\<^bold>5, null}->max() : \<tau>}"

end

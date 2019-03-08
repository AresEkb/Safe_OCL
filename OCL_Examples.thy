(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Examples\<close>
theory OCL_Examples
  imports OCL_Normalization
begin

lemma logic_simps [simp]:
  "\<exists>a. a"
  "\<exists>a. \<not> a"
  "(\<exists>a. (a \<longrightarrow> P) \<and> a) = P"
  "(\<exists>a. \<not> a \<and> (\<not> a \<longrightarrow> P)) = P"
  by auto

(*
lemmas basic_type_le_less [simp] = Orderings.order_le_less for a :: "'a basic_type"
*)




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
  by (simp add: sup_least_classes1)

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

abbreviation "\<Gamma>\<^sub>0 \<equiv> fmempty :: classes1 type env"
declare [[coercion "phantom :: String.literal \<Rightarrow> classes1 enum"]]
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

definition "classes_classes1 \<equiv>
  {|Object, Person, Employee, Customer, Project, Task, Sprint|}"

definition "attributes_classes1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type)]),
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
    (AssociationEndCall (Var STR ''self'') DotCall None STR ''members'')
    ArrowCall CollectionSizeOp [])),
  (STR ''membersByName'', Project[1], [(STR ''mn'', String[1], In)],
    Set Employee[1], False,
   Some (SelectIteratorCall
    (AssociationEndCall (Var STR ''self'') DotCall None STR ''members'')
    ArrowCall [STR ''member''] None
    (OperationCall
      (AttributeCall (Var STR ''member'') DotCall STR ''name'')
      DotCall EqualOp [Var STR ''mn'']))),
  (STR ''allProjects'', Project[1], [], Set Project[1], True,
   Some (MetaOperationCall Project[1] AllInstancesOp))
  ] :: (classes1 type, classes1 expr) oper_spec list"

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
  by (metis enat_ord_simps(1) one_enat_def one_le_numeral)

inductive class_roles_non_unique where
  "class_roles_non_unique" if 
  "class_roles classes assocs \<C> from role end\<^sub>1"
  "class_roles classes assocs \<C> from role end\<^sub>2"
  "end\<^sub>1 \<noteq> end\<^sub>2"

code_pred class_roles_non_unique .

lemma class_roles_unique:
  assumes "class_roles classes assocs \<C> from role end\<^sub>1"
      and "class_roles classes assocs \<C> from role end\<^sub>2"
    shows "end\<^sub>1 = end\<^sub>2"
proof -
  have "\<not> class_roles_non_unique" by eval
  with assms show ?thesis
    using class_roles_non_unique.simps by blast
qed

instance
  apply standard
  unfolding associations_classes1_def
  using assoc_end_min_less_eq_max apply blast
  using class_roles_unique by blast

end



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




values "{x. \<Gamma>\<^sub>0 \<turnstile>\<^sub>E EnumLiteral STR ''E1'' STR ''A'' : x}"


subsection \<open>Positive Cases\<close>

values "{(\<D>, \<tau>). attribute Person STR ''name'' \<D> \<tau>}"
values "{(\<D>, \<tau>). attribute Employee STR ''name'' \<D> \<tau>}"
values "{(\<D>, \<tau>). attribute Employee STR ''name2'' \<D> \<tau>}"
values "{(\<D>, \<tau>). attribute Employee STR ''position'' \<D> \<tau>}"
values "{(\<D>, end). association_end Employee None STR ''projects'' \<D> end}"
(* Тут нужен комментарий, что возвращается два одинаковых типа и это норм.
 Главное, что они совпадают. Хотя нет, это ошибка.
 В рантайме мы не сможем получить список объектов.
 Хотя с другой стороны, мы можем возвращать все объекты,
 а from использовать для фильтрации. Это выглядит полезным *)
values "{(\<D>, end). association_end Employee None STR ''employees'' \<D> end}"
values "{(\<D>, end). association_end Employee (Some STR ''project_manager'') STR ''employees'' \<D> end}"
values "{op. operation Project[1] STR ''membersCount'' [] op}"
values "{op. operation Project[1] STR ''membersByName'' [String[1]] op}"
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
(*
declare unique_closest_attribute.simps [simp]
declare closest_attribute.simps [simp]
declare attribute_not_closest.simps [simp]
declare closest_attribute_not_unique.simps [simp]
declare owned_attribute'.simps []
*)
(*declare attributes_classes1_def [simp]*)
(*declare Least_def [simp]*)
declare has_literal'.simps [simp]

lemma
  "attribute Customer STR ''name'' Person String[1]"
  by eval

lemma
  "association_end Employee None STR ''projects'' Employee (Project, 0, \<infinity>, False, True)"
  by eval


(*** Typing *****************************************************************)

section \<open>Typing\<close>

subsection \<open>Positive Cases\<close>


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


text \<open>
\<^verbatim>\<open>E1::A : E1[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> EnumLiteral STR ''E1'' STR ''A'' : (Enum STR ''E1'')[1]"
  by (auto simp add: literals_classes1_def)

(*
datatype (plugins del: size) 'a type =
  OclSuper
| Required "'a basic_type" ("_[1]" [1000] 1000)
| Optional "'a basic_type" ("_[?]" [1000] 1000)
| Collection "'a type"
| Set "'a type"
| OrderedSet "'a type"
| Bag "'a type"
| Sequence "'a type"
| Tuple "telem \<rightharpoonup>\<^sub>f 'a type"
*)

lemmas basic_type_le_less [simp] = Orderings.order_class.le_less for x y :: "'a basic_type"

text \<open>
\<^verbatim>\<open>true or false : Boolean[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (BooleanLiteral True) DotCall OrOp
    [BooleanLiteral False] : Boolean[1]"
  by simp

text \<open>
\<^verbatim>\<open>null and true : Boolean[?]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (NullLiteral) DotCall AndOp
    [BooleanLiteral True] : Boolean[?]"
  by simp

text \<open>
\<^verbatim>\<open>let x : Real[1] = 5 in x + 7 : Real[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> Let (STR ''x'') (Some Real[1]) (IntegerLiteral 5)
    (OperationCall (Var STR ''x'') DotCall PlusOp [IntegerLiteral 7]) : Real[1]"
  by simp

text \<open>
\<^verbatim>\<open>null.oclIsUndefined() : Boolean[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (NullLiteral) DotCall OclIsUndefinedOp [] : Boolean[1]"
  by simp

(*
declare element_type.intros [intro!]
declare to_nonunique_collection.intros [intro!]
declare update_element_type.intros [intro!]
*)

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}.oclIsUndefined() : Sequence(Boolean[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
      CollectionItem NullLiteral])
    DotCall OclIsUndefinedOp [] : Sequence Boolean[1]"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5}->product(Set{'a', 'b'})
  : Set(Tuple(first: Integer[1], second: String[1]))\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5)])
    ArrowCall ProductOp
    [CollectionLiteral SetKind
      [CollectionItem (StringLiteral ''a''),
      CollectionItem (StringLiteral ''b'')]] :
    Set (Tuple (fmap_of_list [
      (STR ''first'', Integer[1]), (STR ''second'', String[1])]))"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->iterate(x, acc : Real[1] = 0 | acc + x)
  : Real[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> IterateCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
        CollectionItem NullLiteral]) SafeArrowCall
    [STR ''x''] None
    (STR ''acc'') (Some Real[1]) (IntegerLiteral 0)
    (OperationCall (Var STR ''acc'') DotCall PlusOp [Var STR ''x'']) : Real[1]"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->max() : Integer[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> OperationCall (CollectionLiteral SequenceKind
    [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
        CollectionItem NullLiteral])
    SafeArrowCall CollectionMaxOp [] : Integer[1]"
  by simp

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x->any(it | it = 'test') : String[?]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> Let (STR ''x'') (Some (Sequence String[?]))
    (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (AnyIteratorCall (Var STR ''x'') ArrowCall
      [STR ''it''] (Some String[?])
      (OperationCall (Var STR ''it'') DotCall EqualOp
        [StringLiteral ''test''])) : String[?]"
  by simp

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x?->closure(it | it) : OrderedSet(String[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> Let STR ''x'' (Some (Sequence String[?]))
    (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (ClosureIteratorCall (Var STR ''x'') SafeArrowCall
      [STR ''it''] None
      (Var STR ''it'')) : OrderedSet String[1]"
  by simp





text \<open>
\<^verbatim>\<open>context Employee:
name : String[1]\<close>\<close>
lemma
  "\<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AttributeCall (Var STR ''self'') DotCall STR ''name'' : String[1]"
  by simp
(*
lemma association_end_Employee_projects [intro]:
  "association_end Employee None STR ''projects'' Employee (Project, 0, \<infinity>, False, True)"
  by eval
*)

declare assoc_end_type_def [simp]

declare assoc_end_class_def [simp]
declare assoc_end_min_def [simp]
declare assoc_end_max_def [simp]
declare assoc_end_ordered_def [simp]
declare assoc_end_unique_def [simp]

text \<open>
\<^verbatim>\<open>context Employee:
projects : Set(Project[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AssociationEndCall (Var STR ''self'') DotCall None
      STR ''projects'' : Set Project[1]"
  by simp

text \<open>
\<^verbatim>\<open>context Employee:
projects.members : Bag(Employee[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AssociationEndCall (AssociationEndCall (Var STR ''self'')
        DotCall None STR ''projects'')
      DotCall None STR ''members'' : Bag Employee[1]"
  apply simp
  by (metis to_single_type.simps(2) to_single_type.simps(6))

text \<open>
\<^verbatim>\<open>Project[?].allInstances() : Set(Project[?])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> MetaOperationCall Project[?] AllInstancesOp : Set Project[?]"
  by simp

(*
declare static_operation'.simps [simp]
*)

text \<open>
\<^verbatim>\<open>Project[1]::allProjects() : Set(Project[1])\<close>\<close>
lemma
  "\<Gamma>\<^sub>0 \<turnstile> StaticOperationCall Project[1] STR ''allProjects'' [] : Set Project[1]"
  apply auto
(*
  by eval
*)
thm HOL.theI' HOL.the1_equality HOL.theI
  thm static_operation'.simps

subsection \<open>Negative Cases\<close>

text \<open>
\<^verbatim>\<open>true = null\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile> OperationCall (BooleanLiteral True) DotCall EqualOp [NullLiteral] : \<tau>"
  by auto


text \<open>
\<^verbatim>\<open>let x : Boolean[1] = 5 in x and true\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile>
    Let STR ''x'' (Some Boolean[1]) (IntegerLiteral 5)
      (OperationCall (Var STR ''x'') DotCall AndOp [BooleanLiteral True]) : \<tau>"
  by simp

text \<open>
\<^verbatim>\<open>let x : Sequence String[?] = Sequence{'abc', 'zxc'} in
x->closure(it | 1)\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile>
    Let STR ''x'' (Some (Sequence String[?])) (CollectionLiteral SequenceKind
      [CollectionItem (StringLiteral ''abc''),
       CollectionItem (StringLiteral ''zxc'')])
    (ClosureIteratorCall (Var STR ''x'') ArrowCall [STR ''it''] None
      (IntegerLiteral 1)) : \<tau>"
  by simp

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}->max()\<close>\<close>
lemma
  "\<nexists>\<tau>. \<Gamma>\<^sub>0 \<turnstile>
    OperationCall (CollectionLiteral SequenceKind
                [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
                 CollectionItem NullLiteral])
        ArrowCall CollectionMaxOp [] : \<tau>"
  apply auto
  apply eval

end

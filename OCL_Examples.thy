(*  Title:       Safe OCL
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Examples\<close>
theory OCL_Examples
  imports OCL_Normal_Form
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

declare [[coercion "ObjectType :: classes1 \<Rightarrow> classes1 basic_type"]]

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

definition "associations_classes1 \<equiv> fmap_of_list [
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
  (STR ''membersCount'', Project[?], [], Integer[1], False,
   Some (OperationCall
    (AssociationEndCall (Var STR ''self'') DotCall STR ''members'' None)
    ArrowCall CollectionSizeOp [])),
  (STR ''membersCount'', Project[?], [], Set Employee[1], False,
   Some (OperationCall
    (AssociationEndCall (Var STR ''self'') DotCall STR ''members'' None)
    ArrowCall CollectionSizeOp [])),
  (STR ''membersByName'', Project[?], [(STR ''mn'', String[1], In)],
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

instance ..

end

subsection \<open>Positive Cases\<close>

value "find_attribute Employee STR ''name''"
value "find_attribute Employee STR ''position''"
value "find_association_end Employee STR ''projects'' None"
value "find_operation Project[1] STR ''membersCount'' []"
value "find_operation Project[1] STR ''membersByName'' [String[1]]"
value "has_literal STR ''E1'' STR ''A''"

subsection \<open>Negative Cases\<close>

value "find_association_end Person STR ''projects'' None"
value "has_literal STR ''E1'' STR ''C''"

(*** Typing *****************************************************************)

section \<open>Typing\<close>

subsection \<open>Positive Cases\<close>

text \<open>
\<^verbatim>\<open>E1::A : E1[1]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  EnumLiteral STR ''E1'' STR ''A'' : x}"

text \<open>
\<^verbatim>\<open>true or false : Boolean[1]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (BooleanLiteral True) DotCall OrOp [BooleanLiteral False] : x}"

text \<open>
\<^verbatim>\<open>null and true : Boolean[?]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (NullLiteral) DotCall AndOp [BooleanLiteral True] : x}"

text \<open>
\<^verbatim>\<open>let x : Real[1] = 5 in x + 7 : Real[1]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  Let (STR ''x'') (Some Real[1]) (IntegerLiteral 5)
    (OperationCall (Var STR ''x'') DotCall PlusOp [IntegerLiteral 7]) : x}"

text \<open>
\<^verbatim>\<open>null.oclIsUndefined() : Boolean[1]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (NullLiteral) DotCall OclIsUndefinedOp [] : x}"

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}.oclIsUndefined() : Sequence(Boolean[1])\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem NullLiteral])
    DotCall OclIsUndefinedOp [] : x}"

text \<open>
\<^verbatim>\<open>Sequence{1..5}->product(Set{'a', 'b'})
  : Set(Tuple(first: Integer[1], second: String[1]))\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall
    (CollectionLiteral SequenceKind
      [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5)])
    ArrowCall
    ProductOp
    [CollectionLiteral SetKind
      [CollectionItem (StringLiteral ''a''), CollectionItem (StringLiteral ''b'')]] : x}"

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?->iterate(x, acc : Real[1] = 0 | acc + x) : Real[1]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  IterateCall (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem NullLiteral]) SafeArrowCall
      [STR ''x''] None
      (STR ''acc'') (Some Real[1]) (IntegerLiteral 0)
    (OperationCall (Var STR ''acc'') DotCall PlusOp [Var STR ''x'']) : x}"

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x->any(it | it = 'test') : String[?]\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  Let (STR ''x'') (Some (Sequence String[?])) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (AnyIteratorCall (Var STR ''x'') ArrowCall [STR ''it''] (Some String[?])
    (OperationCall (Var STR ''it'') DotCall EqualOp [StringLiteral ''test''])) : x}"

text \<open>
\<^verbatim>\<open>let x : Sequence(String[?]) = Sequence{'abc', 'zxc'} in
x?->closure(it | it) : OrderedSet(String[1])\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  Let STR ''x'' (Some (Sequence String[?])) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (ClosureIteratorCall (Var STR ''x'') SafeArrowCall [STR ''it''] None
    (Var STR ''it'')) : x}"

text \<open>
\<^verbatim>\<open>context Employee:
name : String[1]\<close>\<close>
values "{x. (fmap_of_list [(STR ''self'', Employee[1])] :: classes1 type env) \<turnstile>
  AttributeCall (Var STR ''self'') DotCall STR ''name'' : x}"

text \<open>
\<^verbatim>\<open>context Employee:
projects : Set(Project[1])\<close>\<close>
values "{x. (fmap_of_list [(STR ''self'', Employee[?])] :: classes1 type env) \<turnstile>
  AssociationEndCall (Var STR ''self'') DotCall STR ''projects'' None : x}"

text \<open>
\<^verbatim>\<open>context Employee:
projects.members : Bag(Employee[1])\<close>\<close>
values "{x. (fmap_of_list [(STR ''self'', Employee[?])] :: classes1 type env) \<turnstile>
  AssociationEndCall (AssociationEndCall (Var STR ''self'')
      DotCall STR ''projects'' None)
    DotCall STR ''members'' None : x}"

text \<open>
\<^verbatim>\<open>Project[?].allInstances() : Set(Project[?])\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  MetaOperationCall Project[?] AllInstancesOp : x}"

text \<open>
\<^verbatim>\<open>Project[1]::allProjects() : Set(Project[1])\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  StaticOperationCall Project[1] STR ''allProjects'' [] : x}"

subsection \<open>Negative Cases\<close>

text \<open>
\<^verbatim>\<open>let x : Boolean[1] = 5 in x and true\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  Let STR ''x'' (Some Boolean[1]) (IntegerLiteral 5)
    (OperationCall (Var STR ''x'') DotCall AndOp [BooleanLiteral True]) : x}"

text \<open>
\<^verbatim>\<open>let x : Sequence String[?] = Sequence{'abc', 'zxc'} in
x->closure(it | 1)\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  Let STR ''x'' (Some (Sequence String[?])) (CollectionLiteral SequenceKind
    [CollectionItem (StringLiteral ''abc''),
     CollectionItem (StringLiteral ''zxc'')])
  (ClosureIteratorCall (Var STR ''x'') ArrowCall [STR ''it''] None
    (IntegerLiteral 1)) : x}"

text \<open>
\<^verbatim>\<open>null?._'='(true)\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (NullLiteral) SafeDotCall EqualOp [BooleanLiteral True] : x}"

text \<open>
\<^verbatim>\<open>null?.oclIsUndefined()\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (NullLiteral) SafeDotCall OclIsUndefinedOp [] : x}"

text \<open>
\<^verbatim>\<open>Sequence{1..5, null}?.oclIsUndefined()\<close>\<close>
values "{x. (fmempty :: classes1 type env) \<turnstile>
  OperationCall (CollectionLiteral SequenceKind
              [CollectionRange (IntegerLiteral 1) (IntegerLiteral 5),
               CollectionItem NullLiteral])
    SafeDotCall OclIsUndefinedOp [] : x}"

end

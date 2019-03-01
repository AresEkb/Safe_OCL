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

text \<open>
\<^verbatim>\<open>context Employee:
name : String[1]\<close>\<close>
lemma
  "\<Gamma>(STR ''self'' \<mapsto>\<^sub>f Employee[1]) \<turnstile>
    AttributeCall (Var STR ''self'') DotCall STR ''name'' : String[1]"
  apply (auto simp add: attributes_classes1_def)

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

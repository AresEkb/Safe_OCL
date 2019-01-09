(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Basic OCL Types\<close>
theory OCL_Basic_Types
  imports Main "HOL-Library.FSet" OCL_Common
begin

(*** Basic Types ************************************************************)

section \<open>Definition of Basic Types and a Subtype Relation\<close>

datatype 'a basic_type =
  OclAny
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'a
| Enum "vname fset"

inductive basic_subtype
    :: "('a :: order) basic_type \<Rightarrow> 'a basic_type \<Rightarrow> bool" ("_ \<sqsubset>\<^sub>B _" [65, 65] 65) where
  "Boolean \<sqsubset>\<^sub>B OclAny"
| "UnlimitedNatural \<sqsubset>\<^sub>B Integer"
| "Integer \<sqsubset>\<^sub>B Real"
| "Real \<sqsubset>\<^sub>B OclAny"
| "String \<sqsubset>\<^sub>B OclAny"
| "ObjectType c \<sqsubset>\<^sub>B OclAny"
| "c < d \<Longrightarrow> ObjectType c \<sqsubset>\<^sub>B ObjectType d"
| "Enum literals \<sqsubset>\<^sub>B OclAny"

declare basic_subtype.intros [intro!]

inductive_cases basic_subtype_x_Boolean [elim!]: "\<tau> \<sqsubset>\<^sub>B Boolean"
inductive_cases basic_subtype_x_UnlimitedNatural [elim!]: "\<tau> \<sqsubset>\<^sub>B UnlimitedNatural"
inductive_cases basic_subtype_x_Integer [elim!]: "\<tau> \<sqsubset>\<^sub>B Integer"
inductive_cases basic_subtype_x_Real [elim!]: "\<tau> \<sqsubset>\<^sub>B Real"
inductive_cases basic_subtype_x_String [elim!]: "\<tau> \<sqsubset>\<^sub>B String"
inductive_cases basic_subtype_x_ObjectType [elim!]: "\<tau> \<sqsubset>\<^sub>B ObjectType c"
inductive_cases basic_subtype_x_OclAny [elim!]: "\<tau> \<sqsubset>\<^sub>B OclAny"
inductive_cases basic_subtype_x_Enum [elim!]: "\<tau> \<sqsubset>\<^sub>B Enum literals"

inductive_cases basic_subtype_ObjectType_x [elim!]: "ObjectType c \<sqsubset>\<^sub>B \<sigma>"
inductive_cases basic_subtype_OclAny_x [elim!]: "OclAny \<sqsubset>\<^sub>B \<sigma>"

lemma basic_subtype_asym:
  "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>B \<tau> \<Longrightarrow>
   False"
  by (induct rule: basic_subtype.induct; auto)

(*** Partial Order of Basic Types *******************************************)

section \<open>Partial Order of Basic Types\<close>

instantiation basic_type :: (order) order
begin

definition "(<) \<equiv> basic_subtype\<^sup>+\<^sup>+"

definition "(\<le>) \<equiv> basic_subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

subsection \<open>Introduction Rules\<close>

lemma type_less_eq_x_Real_intro [intro]:
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> \<le> Real"
  "\<tau> = Integer \<Longrightarrow> \<tau> \<le> Real"
  unfolding less_eq_basic_type_def
  apply (rule rtranclp.rtrancl_into_rtrancl; auto)
  apply (rule rtranclp.rtrancl_into_rtrancl; auto)
  done

lemma type_less_eq_x_Integer_intro [intro]:
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> \<le> Integer"
  unfolding less_eq_basic_type_def
  by (rule rtranclp.rtrancl_into_rtrancl; auto)

lemma type_less_eq_x_ObjectType_intro [intro]:
  "\<tau> = ObjectType c \<Longrightarrow> c \<le> d \<Longrightarrow> \<tau> \<le> ObjectType d"
  unfolding less_eq_basic_type_def
  by (metis Nitpick.rtranclp_unfold basic_subtype.intros(7)
            dual_order.order_iff_strict r_into_rtranclp)

lemma type_less_eq_x_OclAny_intro [intro]:
  "\<tau> \<le> OclAny"
proof -
  have "basic_subtype\<^sup>*\<^sup>* Integer OclAny"
    by (rule_tac ?b="Real" in rtranclp.rtrancl_into_rtrancl; auto)
  moreover hence "basic_subtype\<^sup>*\<^sup>* UnlimitedNatural OclAny"
    by (rule_tac ?b="Integer" in converse_rtranclp_into_rtranclp; auto)
  ultimately show ?thesis
    unfolding less_eq_basic_type_def
    by (induct \<tau>; auto)
qed

(*** Elimination Rules ******************************************************)

subsection \<open>Elimination Rules\<close>

lemma type_less_x_Boolean [elim!]:
  "\<tau> < Boolean \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Boolean [elim!]:
  "\<tau> \<le> Boolean \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_UnlimitedNatural [elim!]:
  "\<tau> < UnlimitedNatural \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_UnlimitedNatural [elim!]:
  "\<tau> \<le> UnlimitedNatural \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_Integer [elim!]:
  "\<tau> < Integer \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Integer [elim!]:
  "\<tau> \<le> Integer \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_Real [elim!]:
  "\<tau> < Real \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Real [elim!]:
  "\<tau> \<le> Real \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_String [elim!]:
  "\<tau> < String \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_String [elim!]:
  "\<tau> \<le> String \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_ObjectType [elim!]:
  "\<tau> < ObjectType d \<Longrightarrow>
   (\<And>c. \<tau> = ObjectType c \<Longrightarrow> c < d \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  using less_trans by auto

lemma type_less_eq_x_ObjectType [elim!]:
  "\<tau> \<le> ObjectType d \<Longrightarrow>
   (\<And>c. \<tau> = ObjectType c \<Longrightarrow> c \<le> d \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  using dual_order.order_iff_strict by fastforce

lemma type_less_x_Enum [elim!]:
  "\<tau> < Enum literals \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Enum [elim!]:
  "\<tau> \<le> Enum literals \<Longrightarrow>
   (\<tau> = Enum literals \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_OclAny [elim!]:
  "\<tau> < OclAny \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow>
   (\<And>literals. \<tau> = Enum literals \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>c. \<tau> = ObjectType c \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_OclAny [elim!]:
  "\<tau> \<le> OclAny \<Longrightarrow>
   (\<tau> = OclAny \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow>
   (\<And>literals. \<tau> = Enum literals \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>c. \<tau> = ObjectType c \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule basic_type.exhaust; auto)

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma basic_subtype_irrefl:
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: "'a basic_type"
  by (cases \<tau>; auto)

lemma tranclp_less_basic_type:
  "(\<tau>, \<sigma>) \<in> {(\<tau>, \<sigma>). \<tau> \<sqsubset>\<^sub>B \<sigma>}\<^sup>+ \<longleftrightarrow> \<tau> < \<sigma>"
  by (simp add: tranclp_unfold less_basic_type_def)

lemma basic_subtype_acyclic:
  "acyclicP basic_subtype"
  apply (rule acyclicI)
  using OCL_Basic_Types.basic_subtype_irrefl OCL_Basic_Types.tranclp_less_basic_type by auto

lemma antisym_basic_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a basic_type"
  by (induct \<sigma>, auto)

lemma less_le_not_le_basic_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a basic_type"
  unfolding less_basic_type_def less_eq_basic_type_def
  apply (rule iffI; auto)
  apply (metis (mono_tags) basic_subtype_irrefl less_basic_type_def tranclp_rtranclp_tranclp)
  by (drule rtranclpD; auto)

lemma order_refl_basic_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a basic_type"
  by (simp add: less_eq_basic_type_def)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_basic_type)
  apply (simp)
  apply (auto simp add: less_eq_basic_type_def)[1]
  by (simp add: antisym_basic_type)

end

(*** Upper Semilattice of Basic Types ***************************************)

section \<open>Upper Semilattice of Basic Types\<close>

instantiation basic_type :: (semilattice_sup) semilattice_sup
begin

(* We use "case"-style because it works faster *)
fun sup_basic_type where
  "ObjectType c \<squnion> \<sigma> = (case \<sigma> of ObjectType d \<Rightarrow> ObjectType (c \<squnion> d) | _ \<Rightarrow> OclAny)"
| "\<tau> \<squnion> \<sigma> = (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"

lemma sup_ge1_ObjectType:
  "ObjectType c \<le> ObjectType c \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: basic_subtype.simps less_eq_basic_type_def r_into_rtranclp)
  by (metis Nitpick.rtranclp_unfold basic_subtype.intros(7)
            le_less r_into_rtranclp sup.cobounded1)

lemma sup_ge1_basic_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a basic_type"
  apply (induct \<tau>, auto)
  using sup_ge1_ObjectType by auto
(*  by (induct \<tau>, auto simp add: sup_ge1_ObjectType)*)

lemma sup_commut_basic_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a basic_type"
  by (induct \<tau>; induct \<sigma>; auto simp add: sup.commute)

lemma sup_least_basic_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a basic_type"
  by (induct \<rho>; auto)

instance
  apply intro_classes
  apply (simp add: sup_ge1_basic_type)
  apply (simp add: sup_commut_basic_type sup_ge1_basic_type)
  by (simp add: sup_least_basic_type)

end

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred basic_subtype .

fun basic_subtype_fun :: "'a::order basic_type \<Rightarrow> 'a basic_type \<Rightarrow> bool" where
  "basic_subtype_fun OclAny _ = False"
| "basic_subtype_fun Boolean \<sigma> = (\<sigma> = OclAny)"
| "basic_subtype_fun UnlimitedNatural \<sigma> = (\<sigma> = Integer \<or> \<sigma> = Real \<or> \<sigma> = OclAny)"
| "basic_subtype_fun Integer \<sigma> = (\<sigma> = Real \<or> \<sigma> = OclAny)"
| "basic_subtype_fun Real \<sigma> = (\<sigma> = OclAny)"
| "basic_subtype_fun String \<sigma> = (\<sigma> = OclAny)"
| "basic_subtype_fun (ObjectType c) \<sigma> = (case \<sigma>
    of ObjectType d \<Rightarrow> c < d
     | OclAny \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "basic_subtype_fun (Enum _) \<sigma> = (\<sigma> = OclAny)"

lemma less_eq_basic_type_code [code_abbrev, simp]:
  "\<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
  apply (rule iffI)
  apply (cases \<sigma>; auto; erule basic_subtype_fun.elims; auto)
  apply (cases \<sigma>; auto)
  using le_neq_trans by fastforce

lemma less_basic_type_code [code_abbrev, simp]:
  "basic_subtype_fun = (<)"
  apply (intro ext)
  unfolding less_le
  apply auto
  using less_eq_basic_type_code apply blast
  apply (erule basic_subtype_fun.elims; auto)
  using less_eq_basic_type_code by blast

(*** Test Cases *************************************************************)

section \<open>Test Cases\<close>

datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

class classes = semilattice_sup +
  fixes conforms_to :: "'a \<Rightarrow> 'a set"
  and conforms_to' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes conforms_to_super_or_self [simp]: "d \<in> conforms_to c \<longleftrightarrow> c \<le> d"

instantiation classes1 :: classes
begin

inductive subclass1 where
  "c \<noteq> Object \<Longrightarrow>
   subclass1 c Object"
| "subclass1 Employee Person"
| "subclass1 Customer Person"

code_pred [show_modes] subclass1 .

definition "(<) \<equiv> subclass1"

definition "(c::classes1) \<le> d \<equiv> c = d \<or> c < d"
(*
definition "conforms_to c \<equiv> insert c (set_of_pred (subclass1_i_o c))"
definition "conforms_to c \<equiv> {x. x = c \<or> x \<in> set_of_pred (subclass1_i_o c)}"
*)
definition "conforms_to c \<equiv> {x :: classes1. c \<le> x}"
definition "conforms_to' \<equiv> subclass1_i_o"

lemma conforms_to_code [code_abbrev]:
  "insert c (set_of_pred (subclass1_i_o c)) = conforms_to c"
  by (auto simp add: conforms_to_classes1_def less_classes1_def less_eq_classes1_def subclass1_i_o_def)

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
  using less_eq_classes1_def less_classes1_def subclass1.simps by auto

lemma antisym_classes1:
  "c \<le> d \<Longrightarrow> d \<le> c \<Longrightarrow> c = d"
  for c d :: classes1
  using less_eq_classes1_def less_classes1_def subclass1.simps by auto

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
(*
lemma conforms_to_super_or_self:
  "d \<in> conforms_to c \<longleftrightarrow> c \<le> d"
  for c d :: classes1
  unfolding conforms_to_classes1_def
  apply auto
  done
*)
instance
  apply intro_classes
  apply (simp add: less_le_not_le_classes1)
  apply (simp add: order_refl_classes1)
  apply (rule order_trans_classes1; auto)
  apply (simp add: antisym_classes1)
  apply (simp add: sup_ge1_classes1)
  apply (simp add: sup_ge2_classes1)
  apply (simp add: sup_least_classes1)
  apply (simp add: conforms_to_classes1_def)
  done

end

code_pred [show_modes] subclass1 .

subsection \<open>Positive Cases\<close>

value "(UnlimitedNatural :: classes1 basic_type) < Real"
value "ObjectType Employee < ObjectType Person"
value "ObjectType Person \<le> OclAny"

value "conforms_to Employee"

inductive q where
  "d \<in> conforms_to c \<Longrightarrow> q c d"

code_pred [show_modes] q .

values "{x. q Employee x}"

subsection \<open>Negative Cases\<close>

value "(String :: classes1 basic_type) \<le> Boolean"

end

(*  Title:       Safe OCL
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Basic Types\<close>
theory OCL_Basic_Types
  imports Main "HOL-Library.FSet" "HOL-Library.Phantom_Type"
begin

(*** Basic Types ************************************************************)

section \<open>Definition of Basic Types and a Subtype Relation\label{sec:basic-types-def}\<close>

text \<open>
  Basic types are parameterized over classes.\<close>

type_synonym 'a enum = "('a, String.literal) phantom"
type_synonym elit = String.literal

datatype ('a :: order) basic_type =
  OclAny
| OclVoid
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'a ("\<langle>_\<rangle>\<^sub>\<T>" [0] 1000)
| Enum "'a enum"

inductive basic_subtype ("_ \<sqsubset>\<^sub>B _" [65, 65] 65) where
  "OclVoid \<sqsubset>\<^sub>B Boolean"
| "OclVoid \<sqsubset>\<^sub>B UnlimitedNatural"
| "OclVoid \<sqsubset>\<^sub>B String"
| "OclVoid \<sqsubset>\<^sub>B \<langle>\<C>\<rangle>\<^sub>\<T>"
| "OclVoid \<sqsubset>\<^sub>B Enum \<E>"

| "UnlimitedNatural \<sqsubset>\<^sub>B Integer"
| "Integer \<sqsubset>\<^sub>B Real"
| "\<C> < \<D> \<Longrightarrow> \<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset>\<^sub>B \<langle>\<D>\<rangle>\<^sub>\<T>"

| "Boolean \<sqsubset>\<^sub>B OclAny"
| "Real \<sqsubset>\<^sub>B OclAny"
| "String \<sqsubset>\<^sub>B OclAny"
| "\<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset>\<^sub>B OclAny"
| "Enum \<E> \<sqsubset>\<^sub>B OclAny"

declare basic_subtype.intros [intro!]

inductive_cases basic_subtype_x_OclAny [elim!]: "\<tau> \<sqsubset>\<^sub>B OclAny"
inductive_cases basic_subtype_x_OclVoid [elim!]: "\<tau> \<sqsubset>\<^sub>B OclVoid"
inductive_cases basic_subtype_x_Boolean [elim!]: "\<tau> \<sqsubset>\<^sub>B Boolean"
inductive_cases basic_subtype_x_Real [elim!]: "\<tau> \<sqsubset>\<^sub>B Real"
inductive_cases basic_subtype_x_Integer [elim!]: "\<tau> \<sqsubset>\<^sub>B Integer"
inductive_cases basic_subtype_x_UnlimitedNatural [elim!]: "\<tau> \<sqsubset>\<^sub>B UnlimitedNatural"
inductive_cases basic_subtype_x_String [elim!]: "\<tau> \<sqsubset>\<^sub>B String"
inductive_cases basic_subtype_x_ObjectType [elim!]: "\<tau> \<sqsubset>\<^sub>B \<langle>\<C>\<rangle>\<^sub>\<T>"
inductive_cases basic_subtype_x_Enum [elim!]: "\<tau> \<sqsubset>\<^sub>B Enum \<E>"

inductive_cases basic_subtype_OclAny_x [elim!]: "OclAny \<sqsubset>\<^sub>B \<sigma>"
inductive_cases basic_subtype_ObjectType_x [elim!]: "\<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset>\<^sub>B \<sigma>"

lemma basic_subtype_asym:
  "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<sigma> \<sqsubset>\<^sub>B \<tau> \<Longrightarrow> False"
  by (induct rule: basic_subtype.induct, auto)

(*** Partial Order of Basic Types *******************************************)

section \<open>Partial Order of Basic Types\<close>

instantiation basic_type :: (order) order
begin

definition "(<) \<equiv> basic_subtype\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> basic_subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

subsection \<open>Introduction Rules\<close>

lemma type_less_eq_x_OclAny_intro [intro]:
  "\<tau> \<le> OclAny"
proof -
  have "basic_subtype\<^sup>*\<^sup>* OclVoid OclAny"
    by (rule_tac ?b="Boolean" in rtranclp.rtrancl_into_rtrancl; auto)
  moreover have "basic_subtype\<^sup>*\<^sup>* Integer OclAny"
    by (rule_tac ?b="Real" in rtranclp.rtrancl_into_rtrancl; auto)
  moreover hence "basic_subtype\<^sup>*\<^sup>* UnlimitedNatural OclAny"
    by (rule_tac ?b="Integer" in converse_rtranclp_into_rtranclp; auto)
  ultimately show ?thesis
    unfolding less_eq_basic_type_def
    by (induct \<tau>; auto)
qed

lemma type_less_eq_OclVoid_x_intro [intro]:
  "OclVoid \<le> \<tau>"
proof -
  have "basic_subtype\<^sup>*\<^sup>* OclVoid OclAny"
    by (metis (mono_tags) OCL_Basic_Types.less_eq_basic_type_def
          OCL_Basic_Types.type_less_eq_x_OclAny_intro)
  moreover have "basic_subtype\<^sup>*\<^sup>* OclVoid Integer"
    by (rule_tac ?b="UnlimitedNatural" in rtranclp.rtrancl_into_rtrancl; auto)
  moreover hence "basic_subtype\<^sup>*\<^sup>* OclVoid Real"
    by (rule_tac ?b="Integer" in rtranclp.rtrancl_into_rtrancl; auto)
  ultimately show ?thesis
    unfolding less_eq_basic_type_def
    by (induct \<tau>; auto)
qed

lemma type_less_eq_x_Real_intro [intro]:
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> \<le> Real"
  "\<tau> = Integer \<Longrightarrow> \<tau> \<le> Real"
  unfolding less_eq_basic_type_def
  by (rule rtranclp.rtrancl_into_rtrancl; auto)+

lemma type_less_eq_x_Integer_intro [intro]:
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> \<le> Integer"
  unfolding less_eq_basic_type_def
  by (rule rtranclp.rtrancl_into_rtrancl; auto)

lemma type_less_eq_x_ObjectType_intro [intro]:
  "\<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> \<le> \<D> \<Longrightarrow> \<tau> \<le> \<langle>\<D>\<rangle>\<^sub>\<T>"
  unfolding less_eq_basic_type_def
  using dual_order.order_iff_strict by blast

(*** Elimination Rules ******************************************************)

subsection \<open>Elimination Rules\<close>

lemma type_less_x_OclAny [elim!]:
  "\<tau> < OclAny \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<E>. \<tau> = Enum \<E> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<C>. \<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_OclAny [elim!]:
  "\<tau> \<le> OclAny \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclAny \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<E>. \<tau> = Enum \<E> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<C>. \<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule basic_type.exhaust; auto)

lemma type_less_x_OclVoid [elim!]:
  "\<tau> < OclVoid \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_OclVoid [elim!]:
  "\<tau> \<le> OclVoid \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_Boolean [elim!]:
  "\<tau> < Boolean \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Boolean [elim!]:
  "\<tau> \<le> Boolean \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_Real [elim!]:
  "\<tau> < Real \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Real [elim!]:
  "\<tau> \<le> Real \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_Integer [elim!]:
  "\<tau> < Integer \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Integer [elim!]:
  "\<tau> \<le> Integer \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_UnlimitedNatural [elim!]:
  "\<tau> < UnlimitedNatural \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_UnlimitedNatural [elim!]:
  "\<tau> \<le> UnlimitedNatural \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_String [elim!]:
  "\<tau> < String \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_String [elim!]:
  "\<tau> \<le> String \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

lemma type_less_x_ObjectType [elim!]:
  "\<tau> < \<langle>\<D>\<rangle>\<^sub>\<T> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<C>. \<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> < \<D> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  using less_trans by auto

lemma type_less_eq_x_ObjectType [elim!]:
  "\<tau> \<le> \<langle>\<D>\<rangle>\<^sub>\<T> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<C>. \<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> \<le> \<D> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  using dual_order.order_iff_strict by fastforce

lemma type_less_x_Enum [elim!]:
  "\<tau> < Enum \<E> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_eq_x_Enum [elim!]:
  "\<tau> \<le> Enum \<E> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Enum \<E> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  by (induct rule: converse_rtranclp_induct; auto)

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
  using OCL_Basic_Types.basic_subtype_irrefl
    OCL_Basic_Types.tranclp_less_basic_type by auto

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

notation sup (infixl "\<squnion>" 65)

instantiation basic_type :: (semilattice_sup) semilattice_sup
begin

(* We use "case"-style because it works faster *)
fun sup_basic_type where
  "\<langle>\<C>\<rangle>\<^sub>\<T> \<squnion> \<sigma> = (case \<sigma> of OclVoid \<Rightarrow> \<langle>\<C>\<rangle>\<^sub>\<T> | \<langle>\<D>\<rangle>\<^sub>\<T> \<Rightarrow> \<langle>\<C> \<squnion> \<D>\<rangle>\<^sub>\<T> | _ \<Rightarrow> OclAny)"
| "\<tau> \<squnion> \<sigma> = (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"

lemma sup_ge1_ObjectType:
  "\<langle>\<C>\<rangle>\<^sub>\<T> \<le> \<langle>\<C>\<rangle>\<^sub>\<T> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: basic_subtype.simps less_eq_basic_type_def r_into_rtranclp)
  by (metis less_eq_basic_type_def sup.cobounded1 type_less_eq_x_ObjectType_intro)

lemma sup_ge1_basic_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a basic_type"
  apply (induct \<tau>, auto)
  using sup_ge1_ObjectType by auto

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
| "basic_subtype_fun OclVoid \<sigma> = (\<sigma> \<noteq> OclVoid)"
| "basic_subtype_fun Boolean \<sigma> = (\<sigma> = OclAny)"
| "basic_subtype_fun Real \<sigma> = (\<sigma> = OclAny)"
| "basic_subtype_fun Integer \<sigma> = (\<sigma> = Real \<or> \<sigma> = OclAny)"
| "basic_subtype_fun UnlimitedNatural \<sigma> = (\<sigma> = Integer \<or> \<sigma> = Real \<or> \<sigma> = OclAny)"
| "basic_subtype_fun String \<sigma> = (\<sigma> = OclAny)"
| "basic_subtype_fun \<langle>\<C>\<rangle>\<^sub>\<T> \<sigma> = (case \<sigma>
    of \<langle>\<D>\<rangle>\<^sub>\<T> \<Rightarrow> \<C> < \<D>
     | OclAny \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "basic_subtype_fun (Enum _) \<sigma> = (\<sigma> = OclAny)"

lemma less_eq_basic_type_code [code_abbrev, simp]:
  "\<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
proof
  show "\<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>"
    by (cases \<sigma>; auto; erule basic_subtype_fun.elims; auto)
  show "\<tau> \<le> \<sigma> \<Longrightarrow> \<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma>"
    apply (cases \<sigma>; auto)
    using le_neq_trans by fastforce
qed

lemma less_basic_type_code [code_abbrev, simp]:
  "basic_subtype_fun = (<)"
proof (intro ext)
  have "\<And>\<tau>. basic_subtype_fun \<tau> \<tau> \<Longrightarrow> False"
    by (erule basic_subtype_fun.elims; auto)
  thus "\<And>\<tau> \<sigma>. basic_subtype_fun \<tau> \<sigma> = (\<tau> < \<sigma>)"
    by (metis less_eq_basic_type_code order.strict_iff_order)
qed

end

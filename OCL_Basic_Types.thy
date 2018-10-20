theory OCL_Basic_Types
  imports
    Main
    Transitive_Closure_Ext
    OCL_Common
    "~~/src/HOL/Library/FSet"
begin

(*
  Тут много определений и теорем для систем типов:
  http://gallium.inria.fr/~remy/mpri/cours1.pdf
*)

notation
  sup (infixl "\<squnion>" 65)

(*** Basic Types ************************************************************)

(* Во многих языках перечисления упорядочены, но в OCL нет, поэтому
   используем множество, а не список *)

datatype basic_type =
  OclAny
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType cls
| Enum "vname fset"

(* TODO: Min and max occurs in collections *)
(* Зачем SupType? По спецификации вроде все типы соответствуют OclAny или нет? 
   В 11.2.1 написано, что OclAny - это супер-тип для всех остальных типов
   В A.2.6 Special Types написано, что OclAny не является супер-типом для коллекций

   OclVoid и OclInvalid являются подтипами и для коллекций тоже
   Хотя в A.2.5.1 для коллекций ничего не сказано про \<epsilon>
   Но в A.2.6 говорится, что всё таки это подтипы для всех типов и без оговорок
*)

(* Возможно стоит переименовать ObjectType в Class.
   Нужно посмотреть спецификацию, там различают классы и типы для классов
   Посмотреть название в спецификации
*)

inductive direct_basic_subtype :: "basic_type \<Rightarrow> basic_type \<Rightarrow> bool" ("_ \<sqsubset>\<^sub>s _" [65, 65] 65) where
  "Boolean \<sqsubset>\<^sub>s OclAny"
| "UnlimitedNatural \<sqsubset>\<^sub>s Integer"
| "Integer \<sqsubset>\<^sub>s Real"
| "Real \<sqsubset>\<^sub>s OclAny"
| "String \<sqsubset>\<^sub>s OclAny"
| "ObjectType cls \<sqsubset>\<^sub>s OclAny"
| "Enum literals \<sqsubset>\<^sub>s OclAny"

inductive_cases direct_basic_subtype_x_Boolean[elim!]: "\<tau> \<sqsubset>\<^sub>s Boolean"
inductive_cases direct_basic_subtype_Boolean_x[elim!]: "Boolean \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_UnlimitedNatural[elim!]: "\<tau> \<sqsubset>\<^sub>s UnlimitedNatural"
inductive_cases direct_basic_subtype_UnlimitedNatural_x[elim!]: "UnlimitedNatural \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_Integer[elim!]: "\<tau> \<sqsubset>\<^sub>s Integer"
inductive_cases direct_basic_subtype_Integer_x[elim!]: "Integer \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_Real[elim!]: "\<tau> \<sqsubset>\<^sub>s Real"
inductive_cases direct_basic_subtype_Real_x[elim!]: "Real \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_String[elim!]: "\<tau> \<sqsubset>\<^sub>s String"
inductive_cases direct_basic_subtype_String_x[elim!]: "String \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_ObjectType[elim!]: "\<tau> \<sqsubset>\<^sub>s ObjectType cls"
inductive_cases direct_basic_subtype_ObjectTypen_x[elim!]: "ObjectType cls \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_OclAny[elim!]: "\<tau> \<sqsubset>\<^sub>s OclAny"
inductive_cases direct_basic_subtype_OclAny_x[elim!]: "OclAny \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_Enum[elim!]: "\<tau> \<sqsubset>\<^sub>s Enum literals"
inductive_cases direct_basic_subtype_Enum_x[elim!]: "Enum literals \<sqsubset>\<^sub>s \<sigma>"

code_pred [show_modes] direct_basic_subtype .

(*** Order for Basic Types **************************************************)

instantiation basic_type :: order
begin

definition "less_basic_type \<equiv> direct_basic_subtype\<^sup>+\<^sup>+"

definition "less_eq_basic_type \<equiv> direct_basic_subtype\<^sup>*\<^sup>*"

lemma subtype_Boolean_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> Boolean < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_UnlimitedNatural_x_intro [intro]:
  "\<sigma> = Integer \<Longrightarrow> UnlimitedNatural < \<sigma>"
  "\<sigma> = Real \<Longrightarrow> UnlimitedNatural < \<sigma>"
  "\<sigma> = OclAny \<Longrightarrow> UnlimitedNatural < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_Integer_x_intro [intro]:
  "\<sigma> = Real \<Longrightarrow> Integer < \<sigma>"
  "\<sigma> = OclAny \<Longrightarrow> Integer < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_Real_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> Real < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_String_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> String < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_ObjectType_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> ObjectType cls < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_Enum_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> Enum literals < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto


lemma subtype_Boolean_x [elim!]:
  "Boolean < \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma subtype_Real_x [elim!]:
  "Real < \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma subtype_Integer_x [elim!]:
  "Integer < \<sigma> \<Longrightarrow>
   (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (erule converse_tranclpE)
  using less_basic_type_def by auto

lemma subtype_UnlimitedNatural_x [elim!]:
  "UnlimitedNatural < \<sigma> \<Longrightarrow>
   (\<sigma> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (erule converse_tranclpE)
  using less_basic_type_def by auto

lemma subtype_String_x [elim!]:
  "String < \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma subtype_ObjectType_x [elim!]:
  "ObjectType cls < \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma subtype_Enum_x [elim!]:
  "Enum literals < \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma subtype_OclAny_x [elim!]:
  "OclAny < \<sigma> \<Longrightarrow> False"
  unfolding less_basic_type_def
  by (drule tranclpD; auto)

lemma subtype_x_Boolean [elim!]:
  "\<tau> < Boolean \<Longrightarrow> False"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using rtranclp.cases by fastforce

lemma subtype_x_UnlimitedNatural [elim!]:
  "\<tau> < UnlimitedNatural \<Longrightarrow> False"
  unfolding less_basic_type_def
  using tranclp.cases by fastforce

lemma subtype_x_Integer [elim!]:
  "\<tau> < Integer \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  apply (unfold Nitpick.rtranclp_unfold)
  using direct_basic_subtype.simps less_basic_type_def subtype_OclAny_x by auto

lemma subtype_x_Real [elim!]:
  "\<tau> < Real \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (erule tranclp.cases)
  using less_basic_type_def by auto

lemma subtype_x_String [elim!]:
  "\<tau> < String \<Longrightarrow> False"
  unfolding less_basic_type_def
  using tranclp.cases by fastforce

lemma subtype_x_ObjectType [elim!]:
  "\<tau> < ObjectType cls \<Longrightarrow> False"
  unfolding less_basic_type_def
  using tranclp.cases by fastforce

lemma subtype_x_Enum [elim!]:
  "\<tau> < Enum literals \<Longrightarrow> False"
  unfolding less_basic_type_def
  using tranclp.cases by fastforce


lemma basic_subtype_acyclic':
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: basic_type
  by (cases \<tau>; auto)

lemma tranclp_less_basic_type:
  "(\<tau>, \<sigma>) \<in> {(\<tau>, \<sigma>). \<tau> \<sqsubset>\<^sub>s \<sigma>}\<^sup>+ \<longleftrightarrow> \<tau> < \<sigma>"
  by (simp add: tranclp_unfold less_basic_type_def)

lemma basic_subtype_acyclic:
  "acyclicP direct_basic_subtype"
  apply (rule acyclicI)
  apply (auto)
  unfolding tranclp_less_basic_type
  by (erule basic_subtype_acyclic')

lemma direct_basic_subtype_antisym:
  "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>s \<tau> \<Longrightarrow>
   False"
  using direct_basic_subtype.simps by auto
  
lemma direct_basic_subtype_not_trans:
  "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>s \<rho> \<Longrightarrow>
   \<not> \<rho> \<sqsubset>\<^sub>s \<tau>"
  apply (erule direct_basic_subtype.cases)
  using direct_basic_subtype.simps by auto

lemma direct_basic_subtype_det:
  "direct_basic_subtype \<tau> \<sigma> \<Longrightarrow>
   direct_basic_subtype \<tau> \<rho> \<Longrightarrow>
   \<sigma> = \<rho>"
  using direct_basic_subtype.simps by auto

lemma less_le_not_le_basic_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: basic_type
  unfolding less_basic_type_def less_eq_basic_type_def
  apply (rule iffI; auto)
  apply (metis (mono_tags, lifting) less_basic_type_def basic_subtype_acyclic' tranclp_rtranclp_tranclp)
  by (drule rtranclpD; auto)

lemma order_refl_basic_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: basic_type
  by (simp add: less_eq_basic_type_def)

lemma order_trans_basic_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: basic_type
  by (auto simp add: less_eq_basic_type_def)

lemma antisym_basic_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: basic_type
  by (metis (mono_tags, lifting) less_eq_basic_type_def less_le_not_le_basic_type less_basic_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_basic_type)
  apply (simp)
  using order_trans_basic_type apply blast
  by (simp add: antisym_basic_type)

end

(*** Upper Semilattice for Basic Types **************************************)

instantiation basic_type :: semilattice_sup
begin

definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"

lemma sup_ge1_basic_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: basic_type
  apply (auto simp: less_eq_basic_type_def sup_basic_type_def)
  apply (induct \<tau>)
  using direct_basic_subtype.intros by auto

lemma sup_commut_basic_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: basic_type
  by (simp add: sup_basic_type_def antisym_basic_type)

lemma sup_least_basic_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: basic_type
  apply (auto simp: less_eq_basic_type_def sup_basic_type_def)
  apply (erule converse_rtranclpE)
  apply simp
  apply (erule converse_rtranclpE)
  apply (simp add: converse_rtranclp_into_rtranclp)
  using direct_basic_subtype.simps by auto

instance
  apply intro_classes
  apply (simp add: sup_ge1_basic_type)
  apply (simp add: sup_commut_basic_type sup_ge1_basic_type)
  by (simp add: sup_least_basic_type)

end

(*** Minimal Basic Types ****************************************************)

definition "is_min_basic_type \<tau> \<equiv> \<nexists>\<sigma>. \<sigma> \<sqsubset>\<^sub>s \<tau>"

lemma is_min_basic_type_code [code]:
  "is_min_basic_type \<tau> \<longleftrightarrow>
   \<tau> = Boolean \<or> \<tau> = UnlimitedNatural \<or> \<tau> = String \<or>
   (case \<tau> of ObjectType _ \<Rightarrow> True | _ \<Rightarrow> False) \<or>
   (case \<tau> of Enum _ \<Rightarrow> True | _ \<Rightarrow> False)"
  apply (simp add: is_min_basic_type_def)
  apply (rule iffI)
  apply (cases \<tau>; simp add: direct_basic_subtype.simps)
  apply auto[1]
  using direct_basic_subtype.simps by force

lemma Boolean_is_min [simp]:
  "is_min_basic_type Boolean"
  by (auto simp add: is_min_basic_type_def)

lemma UnlimitedNatural_is_min [simp]:
  "is_min_basic_type UnlimitedNatural"
  by (auto simp add: is_min_basic_type_def)

lemma String_is_min [simp]:
  "is_min_basic_type String"
  by (auto simp add: is_min_basic_type_def)

lemma ObjectType_is_min [simp]:
  "is_min_basic_type (ObjectType cls)"
  by (auto simp add: is_min_basic_type_def)

lemma Enum_is_min [simp]:
  "is_min_basic_type (Enum literals)"
  by (auto simp add: is_min_basic_type_def)

(*** Code Setup for Basic Types *********************************************)

fun basic_subtype_fun :: "basic_type \<Rightarrow> basic_type \<Rightarrow> bool" where
  "basic_subtype_fun OclAny _ = False"
| "basic_subtype_fun Boolean OclAny = True"
| "basic_subtype_fun Boolean _ = False"
| "basic_subtype_fun UnlimitedNatural Integer = True"
| "basic_subtype_fun UnlimitedNatural Real = True"
| "basic_subtype_fun UnlimitedNatural OclAny = True"
| "basic_subtype_fun UnlimitedNatural _ = False"
| "basic_subtype_fun Integer Real = True"
| "basic_subtype_fun Integer OclAny = True"
| "basic_subtype_fun Integer _ = False"
| "basic_subtype_fun Real OclAny = True"
| "basic_subtype_fun Real _ = False"
| "basic_subtype_fun String OclAny = True"
| "basic_subtype_fun String _ = False"
| "basic_subtype_fun (ObjectType _) OclAny = True"
| "basic_subtype_fun (ObjectType _) _ = False"
| "basic_subtype_fun (Enum _) OclAny = True"
| "basic_subtype_fun (Enum _) _ = False"

lemma less_basic_type_code [code_abbrev, simp]:
  "basic_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  apply (rule iffI)
  apply (erule basic_subtype_fun.elims; auto)
  apply (cases \<tau>; auto)
  done

lemma less_eq_basic_type_code [code_abbrev, simp]:
  "\<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
  using le_less less_basic_type_code by auto

(*** Test Cases *************************************************************)

value "Integer \<sqsubset>\<^sub>s Real"
value "basic_subtype_fun Integer Real"
value "basic_subtype_fun Integer OclAny"
value "basic_subtype_fun Boolean Integer"
(*
value "direct_basic_subtype\<^sup>+\<^sup>+ Integer Real"
value "direct_basic_subtype\<^sup>*\<^sup>* Integer Real"
values "{x. direct_basic_subtype\<^sup>*\<^sup>* Integer Real}"
values "{x. direct_basic_subtype\<^sup>*\<^sup>* Integer x}"
values "{x. Integer < x}"
*)
value "UnlimitedNatural < Real"
value "UnlimitedNatural \<le> Real"
value "Real < Real"
value "Real \<le> Real"

end

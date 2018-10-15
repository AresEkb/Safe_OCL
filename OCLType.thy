theory OCLType
  imports
    Main
(*    Complex_Main*)
(*    "~~/src/HOL/Library/Extended_Nat"*)
    Transitive_Closure_Ext
(*    "~~/src/HOL/Library/Transitive_Closure_Table"*)
(*    ProgLang*)
begin

(*
  Тут много определений и теорем для систем типов:
  http://gallium.inria.fr/~remy/mpri/cours1.pdf
*)

notation
  sup (infixl "\<squnion>" 65)


(*** Kinds ******************************************************************************)

type_synonym cls = "string"
type_synonym attr = "string"
type_synonym assoc = "string"
type_synonym role = "string"
type_synonym oid = "string"

(*** Types ******************************************************************************)

datatype simple_type =
  OclAny
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType cls

(* TODO: Min and max occurs in collections *)
(* Зачем SupType? По спецификации вроде все типы соответствуют OclAny или нет? 
   В 11.2.1 написано, что OclAny - это супер-тип для всех остальных типов
   В A.2.6 Special Types написано, что OclAny не является супер-типом для коллекций

   OclVoid и OclInvalid являются подтипами и для коллекций тоже
   Хотя в A.2.5.1 для коллекций ничего не сказано про \<epsilon>
   Но в A.2.6 говорится, что всё таки это подтипы для всех типов и без оговорок
*)

inductive direct_simple_subtype :: "simple_type \<Rightarrow> simple_type \<Rightarrow> bool" ("_ \<sqsubset>\<^sub>s _" [65, 65] 65) where
  "Boolean \<sqsubset>\<^sub>s OclAny"
| "UnlimitedNatural \<sqsubset>\<^sub>s Integer"
| "Integer \<sqsubset>\<^sub>s Real"
| "Real \<sqsubset>\<^sub>s OclAny"
| "String \<sqsubset>\<^sub>s OclAny"
| "ObjectType cls \<sqsubset>\<^sub>s OclAny"

inductive_cases direct_simple_subtype_x_Boolean[elim!]: "\<tau> \<sqsubset>\<^sub>s Boolean"
inductive_cases direct_simple_subtype_Boolean_x[elim!]: "Boolean \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_simple_subtype_x_UnlimitedNatural[elim!]: "\<tau> \<sqsubset>\<^sub>s UnlimitedNatural"
inductive_cases direct_simple_subtype_UnlimitedNatural_x[elim!]: "UnlimitedNatural \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_simple_subtype_x_Integer[elim!]: "\<tau> \<sqsubset>\<^sub>s Integer"
inductive_cases direct_simple_subtype_Integer_x[elim!]: "Integer \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_simple_subtype_x_Real[elim!]: "\<tau> \<sqsubset>\<^sub>s Real"
inductive_cases direct_simple_subtype_Real_x[elim!]: "Real \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_simple_subtype_x_String[elim!]: "\<tau> \<sqsubset>\<^sub>s String"
inductive_cases direct_simple_subtype_String_x[elim!]: "String \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_simple_subtype_x_ObjectType[elim!]: "\<tau> \<sqsubset>\<^sub>s ObjectType cls"
inductive_cases direct_simple_subtype_ObjectTypen_x[elim!]: "ObjectType cls \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_simple_subtype_x_OclAny[elim!]: "\<tau> \<sqsubset>\<^sub>s OclAny"
inductive_cases direct_simple_subtype_OclAny_x[elim!]: "OclAny \<sqsubset>\<^sub>s \<sigma>"

code_pred [show_modes] direct_simple_subtype .

lemma simple_subtype_OclAny_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ OclAny \<sigma> \<Longrightarrow> False"
  apply (drule tranclpD)
  by (simp add: direct_simple_subtype.simps)

lemma simple_subtype_Boolean_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ Boolean \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma simple_subtype_Real_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ Real \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma simple_subtype_Integer_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ Integer \<sigma> \<Longrightarrow>
   (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  using converse_tranclpE by fastforce

lemma simple_subtype_UnlimitedNatural_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ UnlimitedNatural \<sigma> \<Longrightarrow>
   (\<sigma> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  using converse_tranclpE by fastforce

lemma simple_subtype_String_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ String \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma simple_subtype_ObjectType_x [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ (ObjectType cls) \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma simple_subtype_x_Boolean [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> Boolean \<Longrightarrow> False"
  using tranclp.cases by fastforce

lemma simple_subtype_x_UnlimitedNatural [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> UnlimitedNatural \<Longrightarrow> False"
  using tranclp.cases by fastforce

lemma simple_subtype_x_Integer [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> Integer \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  apply (unfold Nitpick.rtranclp_unfold)
  using direct_simple_subtype.cases simple_subtype_OclAny_x by blast

lemma simple_subtype_x_Real [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> Real \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  apply (unfold Nitpick.rtranclp_unfold)
  using tranclp.cases by fastforce

lemma simple_subtype_x_String [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> String \<Longrightarrow> False"
  using tranclp.cases by fastforce

lemma simple_subtype_x_ObjectType [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> (ObjectType cls) \<Longrightarrow> False"
  using tranclp.cases by fastforce

lemma acyclic_direct_simple_subtype:
  "acyclicP direct_simple_subtype"
  apply (rule acyclicI)
  apply (auto)
  apply (erule tranclE)
  using direct_simple_subtype.simps apply auto[1]
  apply (erule tranclE)
  using direct_simple_subtype.simps apply auto[1]
  apply (erule tranclE)
  using direct_simple_subtype.simps apply auto[1]
  apply (erule tranclE)
  using direct_simple_subtype.simps apply auto[1]
  using direct_simple_subtype.simps apply auto[1]
  done

lemma direct_simple_subtype_antisym:
  "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>s \<tau> \<Longrightarrow>
   False"
  using direct_simple_subtype.simps by auto
  
lemma direct_simple_subtype_not_trans:
  "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>s \<rho> \<Longrightarrow>
   \<not> \<rho> \<sqsubset>\<^sub>s \<tau>"
  apply (erule direct_simple_subtype.cases)
  using direct_simple_subtype.simps by auto

lemma direct_simple_subtype_det:
  "direct_simple_subtype \<tau> \<sigma> \<Longrightarrow>
   direct_simple_subtype \<tau> \<rho> \<Longrightarrow>
   \<sigma> = \<rho>"
  using direct_simple_subtype.simps by auto

(* Верхняя полурешетка для простых типов *)

instantiation simple_type :: semilattice_sup
begin

definition "less_simple_type \<equiv> direct_simple_subtype\<^sup>+\<^sup>+"

definition "less_eq_simple_type \<equiv> direct_simple_subtype\<^sup>*\<^sup>*"

definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"

lemma less_le_not_le_simple_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: simple_type
  apply (rule iffI; auto simp add: less_simple_type_def less_eq_simple_type_def)
  apply (metis acyclic_alt acyclic_direct_simple_subtype tranclpD tranclp_rtranclp_tranclp)
  by (metis rtranclpD)

lemma order_refl_simple_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: simple_type
  by (simp add: less_eq_simple_type_def)

lemma order_trans_simple_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: simple_type
  by (auto simp add: less_eq_simple_type_def)

lemma antisym_simple_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: simple_type
  by (metis (mono_tags, lifting) less_eq_simple_type_def less_le_not_le_simple_type less_simple_type_def rtranclpD)

lemma sup_ge1_simple_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: simple_type
  apply (auto simp: less_eq_simple_type_def sup_simple_type_def)
  apply (induct \<tau>)
  apply simp
  apply (simp add: direct_simple_subtype.intros(1) r_into_rtranclp)
  apply (simp add: direct_simple_subtype.intros(4) r_into_rtranclp)
  using direct_simple_subtype.intros(3) direct_simple_subtype.intros(4) apply auto[1]
  using direct_simple_subtype.intros(2) direct_simple_subtype.intros(3) direct_simple_subtype.intros(4) apply auto[1]
  apply (simp add: direct_simple_subtype.intros(5) r_into_rtranclp)
  by (simp add: direct_simple_subtype.intros(6) r_into_rtranclp)

lemma sup_commut_simple_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: simple_type
  by (simp add: sup_simple_type_def antisym_simple_type)

lemma sup_least_simple_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: simple_type
  apply (auto simp: less_eq_simple_type_def sup_simple_type_def)
  apply (erule converse_rtranclpE)
  apply simp
  apply (erule converse_rtranclpE)
  apply (simp add: converse_rtranclp_into_rtranclp)
  using direct_simple_subtype.simps by auto

instance
  apply intro_classes
  apply (simp add: less_le_not_le_simple_type)
  apply (simp)
  using order_trans_simple_type apply blast
  apply (simp add: antisym_simple_type)
  using less_eq_simple_type_def sup_ge1_simple_type sup_simple_type_def apply auto[1]
  using less_eq_simple_type_def sup_commut_simple_type sup_ge1_simple_type sup_simple_type_def apply auto[1]
  by (simp add: sup_least_simple_type)

end

fun simple_subtype_fun :: "simple_type \<Rightarrow> simple_type \<Rightarrow> bool" where
  "simple_subtype_fun OclAny _ = False"
| "simple_subtype_fun Boolean OclAny = True"
| "simple_subtype_fun Boolean _ = False"
| "simple_subtype_fun UnlimitedNatural Integer = True"
| "simple_subtype_fun UnlimitedNatural Real = True"
| "simple_subtype_fun UnlimitedNatural OclAny = True"
| "simple_subtype_fun UnlimitedNatural _ = False"
| "simple_subtype_fun Integer Real = True"
| "simple_subtype_fun Integer OclAny = True"
| "simple_subtype_fun Integer _ = False"
| "simple_subtype_fun Real OclAny = True"
| "simple_subtype_fun Real _ = False"
| "simple_subtype_fun String OclAny = True"
| "simple_subtype_fun String _ = False"
| "simple_subtype_fun (ObjectType _) OclAny = True"
| "simple_subtype_fun (ObjectType _) _ = False"

lemma less_simple_type_code [code_abbrev]:
  "simple_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  apply (simp add: less_simple_type_def)
  apply (rule iffI)
  apply (erule simple_subtype_fun.elims)
  using direct_simple_subtype.intros apply auto
  apply (cases \<tau>; auto)
  done

lemma less_eq_simple_type_code [code_abbrev]:
  "\<tau> = \<sigma> \<or> simple_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
  using le_less less_simple_type_code by auto

value "Integer \<sqsubset>\<^sub>s Real"
value "simple_subtype_fun Integer Real"
value "simple_subtype_fun Integer OclAny"
value "simple_subtype_fun Boolean Integer"
(*
value "direct_simple_subtype\<^sup>+\<^sup>+ Integer Real"
value "direct_simple_subtype\<^sup>*\<^sup>* Integer Real"
values "{x. direct_simple_subtype\<^sup>*\<^sup>* Integer Real}"
values "{x. direct_simple_subtype\<^sup>*\<^sup>* Integer x}"
values "{x. Integer < x}"
*)
value "UnlimitedNatural < Real"
value "UnlimitedNatural \<le> Real"
value "Real < Real"
value "Real \<le> Real"




(* Для упрощения можно запретить вложенные коллекции *)
datatype type =
  SupType
| OclInvalid
| OclVoid
| Required simple_type ("_[1]" [1000] 1000)
| Optional simple_type ("_[?]" [1000] 1000)
| Collection type
| Set type
| OrderedSet type
| Bag type
| Sequence type

term "Set Real[?]"
term "Set Real[1]"

(* Иерархия типов описана в A.2.7 Type Hierarchy *)

definition "is_min_simple_type \<tau> \<equiv> \<nexists>\<sigma>. \<sigma> \<sqsubset>\<^sub>s \<tau>"

lemma is_min_simple_type_code [code]:
  "is_min_simple_type \<tau> \<longleftrightarrow>
   \<tau> = Boolean \<or> \<tau> = UnlimitedNatural \<or> \<tau> = String \<or> (case \<tau> of ObjectType _ \<Rightarrow> True | _ \<Rightarrow> False)"
  apply (simp add: is_min_simple_type_def)
  apply (rule iffI)
  apply (cases \<tau>; simp add: direct_simple_subtype.simps)
  apply auto[1]
  using direct_simple_subtype.simps by force

inductive direct_subtype :: "type \<Rightarrow> type \<Rightarrow> bool" ("_ \<sqsubset> _" [65, 65] 65) where
  "OclInvalid \<sqsubset> OclVoid"
| "is_min_simple_type \<sigma> \<Longrightarrow> OclInvalid \<sqsubset> Required \<sigma>"
| "is_min_simple_type \<sigma> \<Longrightarrow> OclVoid \<sqsubset> Optional \<sigma>"
| "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow> Required \<tau> \<sqsubset> Required \<sigma>"
| "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow> Optional \<tau> \<sqsubset> Optional \<sigma>"
| "Required \<tau> \<sqsubset> Optional \<tau>"
| "OclInvalid \<sqsubset> Set OclInvalid"
| "OclInvalid \<sqsubset> OrderedSet OclInvalid"
| "OclInvalid \<sqsubset> Bag OclInvalid"
| "OclInvalid \<sqsubset> Sequence OclInvalid"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"
| "Optional OclAny \<sqsubset> SupType"
(*| "Collection SupType \<sqsubset> SupType"*)

code_pred [show_modes] direct_subtype .

inductive_cases direct_subtype_x_OclInvalid[elim]: "\<tau> \<sqsubset> OclInvalid"
inductive_cases direct_subtype_OclInvalid_x[elim]: "OclInvalid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_OclVoid[elim]: "\<tau> \<sqsubset> OclVoid"
inductive_cases direct_subtype_OclVoid_x[elim]: "OclVoid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Required[elim]: "\<tau> \<sqsubset> \<sigma>[1]"
inductive_cases direct_subtype_Required_x[elim]: "\<tau>[1] \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Optional[elim]: "\<tau> \<sqsubset> \<sigma>[?]"
inductive_cases direct_subtype_Optional_x[elim]: "\<tau>[?] \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Collection[elim]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases direct_subtype_Collection_x[elim]: "Collection \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Set[elim]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases direct_subtype_Set_x[elim]: "Set \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_OrderedSet[elim]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases direct_subtype_OrderedSet_x[elim]: "OrderedSet \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Bag[elim]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases direct_subtype_Bag_x[elim]: "Bag \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Sequence[elim]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases direct_subtype_Sequence_x[elim]: "Sequence \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_SupType[elim]: "\<tau> \<sqsubset> SupType"
inductive_cases direct_subtype_SupType_x[elim]: "SupType \<sqsubset> \<sigma>"

lemma subtype_OclInvalid_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ OclInvalid \<sigma> \<Longrightarrow>
   (\<sigma> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: tranclp_induct; blast)

lemma subtype_OclVoid_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ OclVoid \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: tranclp_induct; blast)

lemma subtype_Required_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau>[1] \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis direct_subtype_Required_x less_simple_type_def order_refl_simple_type tranclp.r_into_trancl)
  apply (simp add: less_simple_type_def less_eq_simple_type_def)
  by (smt direct_subtype_Optional_x direct_subtype_Required_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl tranclp.trancl_into_trancl tranclp_into_rtranclp)

lemma subtype_Optional_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau>[?] \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis direct_subtype_Optional_x less_eq_simple_type_def r_into_rtranclp)
  by (metis (full_types) direct_subtype_Optional_x direct_subtype_SupType_x dual_order.order_iff_strict less_simple_type_def tranclp.simps)

lemma q:
  "direct_subtype\<^sup>+\<^sup>+ (Set \<tau>) \<sigma> \<Longrightarrow> \<exists>\<rho>. \<sigma> = (Set \<rho>)"

lemma subtype_Set_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ (Set \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Set \<rho>) \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Collection \<rho>) \<Longrightarrow> \<tau> = \<rho> \<or> direct_subtype\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
(*
  by (induct rule: tranclp_induct; blast)
*)
lemma subtype_OrderedSet_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ (OrderedSet \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (OrderedSet \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Collection \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: tranclp_induct; blast)

lemma subtype_Bag_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ (Bag \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Bag \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Collection \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: tranclp_induct; blast)

lemma subtype_Sequence_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ (Sequence \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Sequence \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Collection \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: tranclp_induct; blast)

lemma subtype_Collection_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ (Collection \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = (Collection \<rho>) \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct rule: tranclp_induct; blast)

lemma subtype_SupType_x [elim]:
  "direct_subtype\<^sup>+\<^sup>+ SupType \<sigma> \<Longrightarrow> False"
  by (meson direct_subtype_SupType_x tranclpD)


lemma Required_functor:
  "functor_under_rel direct_simple_subtype direct_subtype Required"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)

lemma Optional_functor:
  "functor_under_rel direct_simple_subtype direct_subtype Optional"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)

lemma Required_Optional_natural:
  "natural_under_rel direct_simple_subtype direct_subtype Required Optional"
  apply (auto simp add: natural_under_rel_def Required_functor Optional_functor direct_subtype.intros(6))
  by (metis direct_subtype_SupType_x subtype_Required_x tranclpD)

lemma Set_functor:
  "functor_under_rel direct_subtype direct_subtype Set"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)

lemma OrderedSet_functor:
  "functor_under_rel direct_subtype direct_subtype OrderedSet"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)

lemma Bag_functor:
  "functor_under_rel direct_subtype direct_subtype Bag"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)

lemma Sequence_functor:
  "functor_under_rel direct_subtype direct_subtype Sequence"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)

lemma Collection_functor:
  "functor_under_rel direct_subtype direct_subtype Collection"
  by (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)


lemma subtype_x_OclInvalid [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> OclInvalid \<Longrightarrow> False"
  by (metis direct_subtype_x_OclInvalid tranclp.cases)

lemma subtype_x_OclVoid [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis direct_subtype_x_OclVoid subtype_x_OclInvalid tranclp.cases)

lemma subtype_x_Required':
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD; auto)
  apply (erule direct_subtype.cases; auto)
  apply (drule rtranclpD; auto)
  apply (unfold Nitpick.rtranclp_unfold; auto)
  apply (meson converse_rtranclpE direct_subtype_SupType_x type.distinct(5))
  done

lemma subtype_x_Required'':
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Required_functor subtype_x_Required' tranclp_fun_preserve_gen_1a)

lemma subtype_x_Required [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  using less_simple_type_def subtype_x_Required'' by auto

lemma subtype_x_Optional':
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<exists>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow> 
   (\<exists>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD; auto)
  apply (erule direct_subtype.cases; auto)
  done

lemma subtype_x_Optional'':
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> = \<sigma> \<or> direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (full_types) Optional_functor Required_Optional_natural subtype_x_Optional' tranclp_fun_preserve1b tranclp_fun_preserve_gen_1a)

lemma subtype_x_Optional [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis eq_refl less_imp_le less_simple_type_def subtype_x_Optional'')

lemma subtype_x_Set [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> (Set \<sigma>) \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = (Set \<rho>) \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis direct_subtype_x_Set tranclp.cases)

lemma subtype_x_Collection [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> (Collection \<sigma>) \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = (Collection \<rho>) \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = (Set \<rho>) \<Longrightarrow> \<rho> = \<sigma> \<or> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = (OrderedSet \<rho>) \<Longrightarrow> \<rho> = \<sigma> \<or> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = (Bag \<rho>) \<Longrightarrow> \<rho> = \<sigma> \<or> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = (Sequence \<rho>) \<Longrightarrow> \<rho> = \<sigma> \<or> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis direct_subtype_x_Collection tranclp.cases)

(*
lemma subtype_x_SupType [elim]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> SupType \<Longrightarrow> (\<tau> \<noteq> SupType \<Longrightarrow> P) \<Longrightarrow> P"
  using subtype_SupType_x by auto

lemma subtype_x_SupType_intro:
  "direct_subtype\<^sup>*\<^sup>* \<tau> SupType"
  apply (induct \<tau>)
  apply simp
*)
lemma direct_subtype_antisym:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset> \<tau> \<Longrightarrow>
   False"
  apply (induct rule: direct_subtype.induct)
  using direct_simple_subtype_antisym by auto
  
lemma direct_subtype_not_trans:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset> \<rho> \<Longrightarrow>
   \<not> \<rho> \<sqsubset> \<tau>"
  apply (induct arbitrary: \<rho> rule: direct_subtype.induct)
  using direct_simple_subtype.simps by auto

lemma direct_subtype_acyclic':
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<tau> \<Longrightarrow> False"
  apply (induct \<tau>)
  apply (meson direct_subtype_SupType_x tranclpD)
  apply auto[1]
  apply auto[1]
  using less_simple_type_def apply auto[1]
  using less_simple_type_def apply auto[1]
  apply (meson direct_subtype_Collection_x tranclpD)
  apply (meson direct_subtype_Set_x tranclpD)
  apply (meson direct_subtype_OrderedSet_x tranclpD)
  apply (meson direct_subtype_Bag_x tranclpD)
  apply (meson direct_subtype_Sequence_x tranclpD)
  done

lemma direct_subtype_acyclic:
  "acyclicP direct_subtype"
  apply (rule acyclicI)
  apply (auto simp add: trancl_def)
  apply (erule direct_subtype_acyclic')
  done

instantiation type :: order
begin

definition "less_type \<equiv> direct_subtype\<^sup>+\<^sup>+"

definition "less_eq_type \<equiv> direct_subtype\<^sup>*\<^sup>*"

(*definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else SupType))"*)

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: type
  apply (rule iffI; auto simp add: less_type_def less_eq_type_def)
  apply (meson direct_subtype_acyclic' tranclp_rtranclp_tranclp)
  by (metis rtranclpD)

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: type
  by (simp add: less_eq_type_def)

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  by (auto simp add: less_eq_type_def)

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: type
  by (metis (mono_tags, lifting) less_eq_type_def less_le_not_le_type less_type_def rtranclpD)
(*
lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: type
  apply (auto simp: less_eq_type_def sup_type_def)
  apply (induct \<tau>)
  apply simp
  apply (rule tranclp_into_rtranclp)
  apply (simp add: direct_simple_subtype.intros(1) r_into_rtranclp)
  apply (simp add: direct_simple_subtype.intros(4) r_into_rtranclp)
  using direct_simple_subtype.intros(3) direct_simple_subtype.intros(4) apply auto[1]
  using direct_simple_subtype.intros(2) direct_simple_subtype.intros(3) direct_simple_subtype.intros(4) apply auto[1]
  apply (simp add: direct_simple_subtype.intros(5) r_into_rtranclp)
  by (simp add: direct_simple_subtype.intros(6) r_into_rtranclp)

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: type
  by (simp add: sup_type_def antisym_type)

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (auto simp: less_eq_type_def sup_type_def)
  apply (erule converse_rtranclpE)
  apply simp
  apply (erule converse_rtranclpE)
  apply (simp add: converse_rtranclp_into_rtranclp)
  using direct_simple_subtype.simps by auto
*)
instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  done

end

fun subtype_fun :: "type \<Rightarrow> type \<Rightarrow> bool" where
  "subtype_fun OclInvalid \<sigma> = (\<sigma> \<noteq> OclInvalid)"
| "subtype_fun OclVoid \<sigma> = (\<sigma> \<noteq> OclInvalid \<and> \<sigma> \<noteq> OclVoid)"
| "subtype_fun (Required \<tau>) (Required \<sigma>) = simple_subtype_fun \<tau> \<sigma>"
| "subtype_fun (Required \<tau>) (Optional \<sigma>) = (\<tau> = \<sigma> \<or> simple_subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Required \<tau>) SupType = True"
| "subtype_fun (Required \<tau>) _ = False"
| "subtype_fun (Optional \<tau>) (Optional \<sigma>) = simple_subtype_fun \<tau> \<sigma>"
| "subtype_fun (Optional \<tau>) SupType = True"
| "subtype_fun (Optional \<tau>) _ = False"
| "subtype_fun _ _ = False"

value "direct_subtype OclInvalid Boolean[1]"
value "direct_subtype Boolean[1] OclAny[1]"

lemma subtype_x_Required_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1]"
  "\<tau> = \<rho>[1] \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1]"
  apply (auto)
  apply (induct \<sigma>)
  apply (metis direct_simple_subtype.intros(1) direct_simple_subtype_x_Boolean direct_subtype.intros(2) direct_subtype.intros(4) is_min_simple_type_def tranclp.r_into_trancl tranclp_into_tranclp2)
  using direct_subtype.intros(2) is_min_simple_type_def apply auto[1]
  apply (metis direct_simple_subtype.intros(2) direct_simple_subtype.intros(3) direct_subtype.intros(2) direct_subtype.intros(4) is_min_simple_type_code tranclp.simps)
  apply (metis direct_simple_subtype.intros(2) direct_subtype.intros(2) direct_subtype.intros(4) is_min_simple_type_code tranclp.simps)
  using direct_subtype.intros(2) is_min_simple_type_def apply auto[1]
  using direct_subtype.intros(2) is_min_simple_type_def apply auto[1]
  using direct_subtype.intros(2) is_min_simple_type_def apply auto[1]
  by (metis direct_subtype.intros(4) fun_preserve_morphism_composition')

lemma subtype_x_Optional_intro [intro]:
  "\<tau> = OclVoid \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[?]"
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[?]"
  apply (auto)
  apply (induct \<sigma>)
  apply (metis direct_simple_subtype.intros(1) direct_subtype.intros(3) direct_subtype.intros(5) is_min_simple_type_code tranclp.simps)
  using direct_subtype.intros(3) is_min_simple_type_code apply auto[1]
  apply (metis direct_simple_subtype.intros(2) direct_simple_subtype.intros(3) direct_subtype.intros(3) direct_subtype.intros(5) is_min_simple_type_code tranclp.simps)
  apply (metis direct_simple_subtype.intros(2) direct_subtype.intros(3) direct_subtype.intros(5) is_min_simple_type_code tranclp.simps)
  using direct_subtype.intros(3) is_min_simple_type_code apply auto[1]
  using direct_subtype.intros(3) is_min_simple_type_code apply auto[1]
  using direct_subtype.intros(3) is_min_simple_type_def apply blast
  apply (simp add: direct_subtype.intros(6) tranclp.trancl_into_trancl)
  by (metis direct_subtype.intros(5) fun_preserve_morphism_composition')
(*
lemma subtype_x_Set_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> (Set \<sigma>)"
  "\<tau> = (Set \<rho>) \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> direct_subtype\<^sup>+\<^sup>+ \<tau> (Set \<sigma>)"
  apply (auto)
*)

lemma subtype_OclInvalid_x_intro [intro]:
  "\<sigma> \<noteq> OclInvalid \<Longrightarrow>
   \<nexists>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow>
   \<nexists>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow>
   \<nexists>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow>
   \<nexists>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow>
   \<nexists>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ OclInvalid \<sigma>"
  apply (induct)
  apply (metis direct_simple_subtype.intros(1) direct_simple_subtype_x_Boolean direct_subtype.intros(1) direct_subtype.intros(3) direct_subtype.intros(5) direct_subtype.intros(7) is_min_simple_type_def rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl rtranclpD)
  apply simp
  apply (simp add: direct_subtype.intros(1) tranclp.r_into_trancl)
  apply auto
  done

lemma less_type_code [code_abbrev]:
  "subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  apply (simp add: less_type_def)
  apply (rule iffI)
  apply (erule subtype_fun.elims)
  using direct_subtype.intros apply auto
  apply (cases \<tau>; auto)
  done

lemma less_eq_type_code [code_abbrev]:
  "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
  using le_less less_type_code by auto


value "Optional OclAny \<sqsubset> SupType"
value "Collection (Optional OclAny) \<sqsubset> SupType"
value "Collection (Optional OclAny) \<lless> SupType"
value "Collection (Collection (Optional OclAny)) \<sqsubset> SupType"
value "Collection (Collection (Optional OclAny)) \<lless> SupType"
value "Collection SupType \<sqsubset> SupType"
value "Set OclInvalid \<sqsubset> Set (OrderedSet OclInvalid)"
value "Collection (Collection SupType) \<sqsubset> Collection SupType"
value "Collection (Collection (Collection SupType)) \<sqsubset> Collection (Collection SupType)"
value "Collection (Collection (Collection (Collection SupType))) \<sqsubset> Collection (Collection (Collection SupType))"
value "Collection (Collection (Collection SupType)) \<sqsubset> Collection SupType"
value "Set (Required Integer) \<sqsubset> Collection (Optional Real)"
value "Set (Required Integer) \<sqsubset> Set (Required Real)"
value "Required Integer \<squnion> Optional Real"
value "(Set (Required Integer)) \<squnion> (Set (Required Real))"
value "(Set (Required Integer)) \<squnion> (Bag (Optional Boolean))"
value "(Set (Required Integer)) \<squnion> Optional Real"

end

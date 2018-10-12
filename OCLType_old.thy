theory OCLType
  imports
    Complex_Main
    "~~/src/HOL/Library/Extended_Nat"
    Transitive_Closure_Ext
(*    "~~/src/HOL/Library/Transitive_Closure_Table"*)
    ProgLang
begin

(*
  Тут много определений и теорем для систем типов:
  http://gallium.inria.fr/~remy/mpri/cours1.pdf
*)


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

inductive_cases direct_simple_subtype_x_OclAny[elim!]: "\<tau> \<sqsubset>\<^sub>s OclAny"
inductive_cases direct_simple_subtype_x_Real[elim!]: "\<tau> \<sqsubset>\<^sub>s Real"
inductive_cases direct_simple_subtype_x_Integer[elim!]: "\<tau> \<sqsubset>\<^sub>s Integer"

code_pred [show_modes] direct_simple_subtype .

thm tranclD2

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

print_statement classical

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

lemma direct_simple_subtype_OclAny_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ OclAny \<sigma> \<Longrightarrow> False"
  apply (drule tranclpD)
  by (simp add: direct_simple_subtype.simps)

lemma direct_simple_subtype_Boolean_intro [intro!]:
  "\<sigma> = OclAny \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ Boolean \<sigma>"
  using direct_simple_subtype.intros(1) by auto

lemma direct_simple_subtype_Boolean_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ Boolean \<sigma> \<Longrightarrow> (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  by (metis Nitpick.rtranclp_unfold direct_simple_subtype.intros(1) direct_simple_subtype_OclAny_elim direct_simple_subtype_det)

lemma direct_simple_subtype_Real_intro [intro!]:
  "\<sigma> = OclAny \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ Real \<sigma>"
  using direct_simple_subtype.intros(4) by auto

lemma direct_simple_subtype_Real_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ Real \<sigma> \<Longrightarrow> (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  by (metis Nitpick.rtranclp_unfold direct_simple_subtype.intros(4) direct_simple_subtype_OclAny_elim direct_simple_subtype_det)

lemma direct_simple_subtype_Integer_intro [intro!]:
  "(\<sigma> = Real \<or> \<sigma> = OclAny) \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ Integer \<sigma>"
  by (metis direct_simple_subtype.intros(3) direct_simple_subtype.intros(4) tranclp.simps)

lemma direct_simple_subtype_Integer_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ Integer \<sigma> \<Longrightarrow> (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow> (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  by (metis Nitpick.rtranclp_unfold direct_simple_subtype.intros(3) direct_simple_subtype_Real_elim direct_simple_subtype_det)

lemma direct_simple_subtype_UnlimitedNatural_intro [intro!]:
  "(\<sigma> = Integer \<or> \<sigma> = Real \<or> \<sigma> = OclAny) \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ UnlimitedNatural \<sigma>"
  by (meson direct_simple_subtype.intros(2) direct_simple_subtype_Integer_intro tranclp.simps tranclp_into_tranclp2)

lemma direct_simple_subtype_UnlimitedNatural_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ UnlimitedNatural \<sigma> \<Longrightarrow> (\<sigma> = Integer \<Longrightarrow> P) \<Longrightarrow> (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow> (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  by (metis direct_simple_subtype.intros(2) direct_simple_subtype_Integer_elim direct_simple_subtype_det le_neq_trans less_eq_simple_type_def less_simple_type_def)

lemma direct_simple_subtype_String_intro [intro!]:
  "\<sigma> = OclAny \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ String \<sigma>"
  using direct_simple_subtype.intros(5) by auto

lemma direct_simple_subtype_String_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ String \<sigma> \<Longrightarrow> (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  by (metis Nitpick.rtranclp_unfold direct_simple_subtype.intros(5) direct_simple_subtype_OclAny_elim direct_simple_subtype_det)

lemma direct_simple_subtype_ObjectType_intro [intro!]:
  "\<sigma> = OclAny \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ (ObjectType cls) \<sigma>"
  using direct_simple_subtype.intros(6) by auto

lemma direct_simple_subtype_ObjectType_elim [elim!]:
  "direct_simple_subtype\<^sup>+\<^sup>+ (ObjectType cls) \<sigma> \<Longrightarrow> (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule tranclpD)
  by (metis Nitpick.rtranclp_unfold direct_simple_subtype.intros(6) direct_simple_subtype_OclAny_elim direct_simple_subtype_det)

lemma less_simple_type_code [code_abbrev]:
  "simple_subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  apply (simp add: less_simple_type_def)
  apply (rule iffI)
  apply (erule simple_subtype_fun.elims; auto)
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
| "Collection SupType \<sqsubset> SupType"

inductive subtype :: "type \<Rightarrow> type \<Rightarrow> bool" ("_ \<lless> _" [65, 65] 65) where
  "\<sigma> \<noteq> OclInvalid \<Longrightarrow> OclInvalid \<lless> \<sigma>"
| "\<sigma> \<noteq> OclInvalid \<Longrightarrow> \<sigma> \<noteq> OclVoid \<Longrightarrow> OclVoid \<lless> \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Required \<tau> \<lless> Required \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Optional \<tau> \<lless> Optional \<sigma>"
| "Required \<tau> \<lless> Optional \<tau>"
| "\<tau> \<lless> \<sigma> \<Longrightarrow> Set \<tau> \<lless> Set \<sigma>"
| "\<tau> \<lless> \<sigma> \<Longrightarrow> OrderedSet \<tau> \<lless> OrderedSet \<sigma>"
| "\<tau> \<lless> \<sigma> \<Longrightarrow> Bag \<tau> \<lless> Bag \<sigma>"
| "\<tau> \<lless> \<sigma> \<Longrightarrow> Sequence \<tau> \<lless> Sequence \<sigma>"
| "\<tau> \<lless> \<sigma> \<Longrightarrow> Collection \<tau> \<lless> Collection \<sigma>"
| "Set \<tau> \<lless> Collection \<tau>"
| "OrderedSet \<tau> \<lless> Collection \<tau>"
| "Bag \<tau> \<lless> Collection \<tau>"
| "Sequence \<tau> \<lless> Collection \<tau>"
| "\<tau> \<noteq> SupType \<Longrightarrow> \<tau> \<lless> SupType"


thm subtype.cases

lemma q:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> \<tau> \<lless> \<sigma>"
  apply (erule direct_subtype.cases)
  apply (simp add: subtype.intros(1))
  apply (simp add: subtype.intros(1))
  apply (simp add: subtype.intros(2))
  apply (simp add: less_simple_type_def subtype.intros(3) tranclp.r_into_trancl)
  apply (simp add: less_simple_type_def rtranclp_into_tranclp2 subtype.intros(4))
  apply (simp add: subtype.intros(5))
  apply (simp add: subtype.intros(1))
  apply (simp add: subtype.intros(1))
  apply (simp add: subtype.intros(1))
  apply (simp add: subtype.intros(1))
(*
  apply (induct)
  apply (smt direct_subtype.cases subtype.simps type.distinct(1) type.simps(13) type.simps(15) type.simps(17) type.simps(19) type.simps(21) type.simps(23) type.simps(25))
  using direct_subtype.cases apply blast
  apply (smt direct_subtype.cases subtype.simps type.distinct(41) type.distinct(47) type.simps(27) type.simps(43) type.simps(45) type.simps(47) type.simps(51) type.simps(53))
*)






code_pred [show_modes] direct_subtype .
code_pred [show_modes] subtype .

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

inductive_cases direct_subtype_x_OclInvalid[elim]: "\<tau> \<sqsubset> OclInvalid"
inductive_cases direct_subtype_OclInvalid_x[elim]: "OclInvalid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_OclVoid[elim]: "\<tau> \<sqsubset> OclVoid"
inductive_cases direct_subtype_OclVoid_x[elim]: "OclVoid \<sqsubset> \<sigma>"
print_theorems
inductive_cases direct_subtype_x_Required[elim]: "\<tau> \<sqsubset> \<sigma>[1]"
print_theorems
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
(*
lemma direct_subtype_trancl:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> is_min_simple_type \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"

print_theorems
*)

lemma subtype_x_OclInvalid [elim!]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> OclInvalid \<Longrightarrow> P"
  by (erule tranclp.cases; auto)
(*
lemma subtype_OclInvalid_x:
  "direct_subtype\<^sup>+\<^sup>+ OclInvalid \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (erule tranclp.cases; auto)
  apply (erule direct_subtype.cases; auto)
  done
*)
lemma subtype_x_OclVoid [elim!]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> OclVoid \<Longrightarrow> (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule tranclp.cases; auto)

thm direct_subtype_x_Required

lemma subtype_x_Required [elim!]:
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (cases \<tau>)
  apply (meson direct_subtype_SupType_x tranclpD)
  apply simp
(*
  apply (erule tranclp.cases; auto)
  apply (metis direct_subtype_x_Required less_simple_type_def tranclp.r_into_trancl)
  apply (cases \<sigma>)
*)
(*  apply (metis direct_subtype_x_Required less_simple_type_def tranclp.r_into_trancl)*)

thm direct_subtype.cases

lemma q:
  "direct_subtype\<^sup>+\<^sup>+ OclVoid (Set \<tau>) \<Longrightarrow> False"
  apply (induct)
  apply (induct)

lemma subtype_OclVoid_x:
  "direct_subtype\<^sup>+\<^sup>+ OclVoid \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
(*
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> P) \<Longrightarrow>
*)
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow>
   P"
  apply (erule tranclp.cases; auto)
  apply (erule direct_subtype.cases; auto)
  done

lemma q1:
  "direct_subtype \<tau>[1] \<sigma>[1] \<Longrightarrow>
   direct_simple_subtype \<tau> \<sigma>"
  by blast

lemma q2:
  "direct_simple_subtype \<tau> \<sigma> \<Longrightarrow>
   direct_subtype \<tau>[1] \<sigma>[1]"
  by (simp add: direct_subtype.intros(4))


lemma q4:
  "(\<lambda>\<tau> \<sigma>. direct_subtype \<tau>[1] \<sigma>[1])\<^sup>+\<^sup>+ \<tau> \<sigma> \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau>[1] \<sigma>[1]"
  by (simp add: tranclp_fun_preserve_gen_2)

lemma q5:
  "direct_simple_subtype\<^sup>+\<^sup>+ \<tau> \<sigma> \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau>[1] \<sigma>[1]"
  by (metis (no_types, lifting) less_simple_type_def mono_rtranclp direct_subtype.intros(4) q4 rtranclpD sup.strict_order_iff tranclp_into_rtranclp)

lemma q14:
  "rel_limited_under direct_subtype (range Required)"
  apply (simp add: rel_limited_under_def)
  by blast
(*
lemma q15:
  "rel_limited_under direct_subtype\<^sup>+\<^sup>+ (range Required)"
  apply (auto simp add: rel_limited_under_def)
*)
lemma q12:
  "rel_limited_under direct_subtype\<^sup>+\<^sup>+ (range Required) \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau>[1] \<sigma>[1] \<Longrightarrow>
   (\<lambda>\<tau> \<sigma>. direct_subtype \<tau>[1] \<sigma>[1])\<^sup>+\<^sup>+ \<tau> \<sigma>"
  apply (simp add: inj_def tranclp_fun_preserve_gen_1)
  done

lemma q13:
  "rel_limited_under direct_subtype\<^sup>+\<^sup>+ (range Required) \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau>[1] \<sigma>[1] \<Longrightarrow>
   (\<lambda>\<tau> \<sigma>. direct_simple_subtype \<tau> \<sigma>)\<^sup>+\<^sup>+ \<tau> \<sigma>"
  by (smt q1 q12 tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)

(*
lemma q7:
  "direct_subtype\<^sup>+\<^sup>+ \<tau>[1] \<sigma>[1] \<Longrightarrow>
   (\<lambda>\<tau> \<sigma>. direct_subtype \<tau>[1] \<sigma>[1])\<^sup>+\<^sup>+ \<tau> \<sigma>"
*)

lemma trancl_direct_subtype_x_Required [elim!]:
  "rel_limited_under direct_subtype\<^sup>+\<^sup>+ (range Required) \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   \<tau> = OclInvalid \<or> (\<forall>\<rho>. \<tau> = \<rho>[1] \<longrightarrow> \<rho> < \<sigma>)"
  apply (simp add: less_simple_type_def)
  apply (erule tranclp.cases)
  apply auto[1]
  apply auto[1]
  by (simp add: q13 tranclp.trancl_into_trancl)

lemma trancl_direct_subtype_x_Required [elim!]:
  "rel_limited_under direct_subtype\<^sup>+\<^sup>+ (range Required) \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   \<tau> = OclInvalid \<or> (\<exists>\<rho>. \<tau> = \<rho>[1])"
  apply (simp add: less_simple_type_def)
  apply (erule tranclp.cases)
  apply auto[1]
  apply auto[1]
  by (simp add: q13 tranclp.trancl_into_trancl)

(*
?\<tau> \<sqsubset> ?\<sigma>[1] \<Longrightarrow> (?\<tau> = OclInvalid \<Longrightarrow> is_min_simple_type ?\<sigma> \<Longrightarrow> ?P) \<Longrightarrow> (\<And>\<tau>. ?\<tau> = \<tau>[1] \<Longrightarrow> \<tau> \<sqsubset>\<^sub>s ?\<sigma> \<Longrightarrow> ?P) \<Longrightarrow> ?P
*)

lemma q:
  "(A \<Longrightarrow> (C \<and> D)) \<Longrightarrow> A \<Longrightarrow> (C \<Longrightarrow> D \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

(*
  direct_subtype_x_Required:
    ?\<tau> \<sqsubset> ?\<sigma>[1] \<Longrightarrow>
    (?\<tau> = OclInvalid \<Longrightarrow> is_min_simple_type ?\<sigma> \<Longrightarrow> ?P) \<Longrightarrow> (\<And>\<tau>. ?\<tau> = \<tau>[1] \<Longrightarrow> \<tau> \<sqsubset>\<^sub>s ?\<sigma> \<Longrightarrow> ?P) \<Longrightarrow> ?P
*)

thm direct_simple_subtype_Real_intro

lemma q:
  "(\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow>
          direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow>
          P) \<Longrightarrow>
    \<sigma> = OclAny \<Longrightarrow>
    direct_simple_subtype\<^sup>+\<^sup>+ Real \<sigma> \<Longrightarrow> P"

lemma q:
  "\<sigma> = OclAny \<Longrightarrow>
    direct_simple_subtype\<^sup>+\<^sup>+ \<tau> \<sigma> \<Longrightarrow> \<exists>\<rho>. \<rho> = Real \<and> \<rho> = \<tau>"

lemma q123:
  "(\<And>x.
          x < z \<Longrightarrow>
          R x y \<Longrightarrow>
          P) \<Longrightarrow>
    z = 3 \<Longrightarrow>
    R (5::nat) y \<Longrightarrow> P"
  apply simp
  done


lemma q:
  "(\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow>
          direct_simple_subtype\<^sup>+\<^sup>+ \<rho> \<sigma> \<Longrightarrow>
          P) \<Longrightarrow>
    \<sigma> = OclAny \<Longrightarrow> P"
  apply (frule direct_simple_subtype_Real_intro)
  apply simp

lemma trancl_direct_subtype_x_Required [elim!]:
  "rel_limited_under direct_subtype\<^sup>+\<^sup>+ (range Required) \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<tau> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (simp add: less_simple_type_def)
  apply (cases \<tau>)
  apply (meson direct_subtype_SupType_x tranclpD)
  apply simp
  apply (cases \<sigma>)
(*
  apply (drule_tac ?\<tau>="\<tau>" and ?\<sigma>="\<sigma>" in trancl_direct_subtype_x_Required)
  apply (simp)
  apply (auto)
*)
(*
   apply (simp add: less_simple_type_def)
  apply (erule tranclp.cases)
  apply (metis direct_subtype_x_Required tranclp.r_into_trancl)
  apply auto[1]
  apply (cases \<sigma>; auto simp: less_simple_type_def)
*)
(*
  apply (erule tranclp.cases)
  apply (metis direct_subtype_x_Required tranclp.r_into_trancl)
  apply auto[1]
  apply (erule direct_subtype.cases; simp)
  apply auto[1]
  apply auto[1]
  apply (erule tranclp.cases)
  apply (metis direct_subtype_x_Required tranclp.r_into_trancl tranclp.trancl_into_trancl)
  apply auto[1]
*)
(*
  apply (erule tranclp.cases)
  apply (smt Nitpick.rtranclp_unfold direct_simple_subtype_not_cyclic direct_subtype_x_OclInvalid direct_subtype_x_Required less_simple_type_def rtranclp.rtrancl_into_rtrancl)
  apply (smt direct_subtype_x_OclInvalid direct_subtype_x_Required less_simple_type_def tranclp.r_into_trancl tranclp_into_tranclp2)
*)
(*
  apply (erule tranclp.cases)
  apply (metis direct_subtype_x_OclInvalid direct_subtype_x_Required tranclp.r_into_trancl tranclp_into_tranclp2)
*)
lemma direct_subtype_acyclic:
  "direct_subtype \<tau> \<sigma> \<Longrightarrow>
   direct_subtype\<^sup>+\<^sup>+ \<sigma> \<tau> \<Longrightarrow> False"
  apply (induct rule: direct_subtype.induct)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (erule tranclp.cases)
  using direct_subtype.intros(4) direct_subtype_antisym apply auto[1]
  apply auto[1]
  apply (erule direct_subtype_x_Required)
  apply (metis direct_subtype_x_OclInvalid tranclp.cases)
(*
  apply (cases \<tau>)
  apply (meson direct_subtype_SupType_x tranclpD)
  apply auto[1]
  apply (metis direct_subtype_antisym direct_subtype_x_OclInvalid direct_subtype_x_OclVoid tranclp.cases)
*)
(*
  apply (induct rule: tranclp.induct)
  using direct_subtype_antisym apply auto[1]
  apply (erule tranclp.cases)
  using direct_subtype_not_trans apply blast
  apply (erule tranclp.cases)
  apply auto[1]
*)
(*
  apply (induct rule: direct_subtype.induct)
  apply (metis direct_subtype_x_OclInvalid tranclp.cases)
  apply (metis direct_subtype_x_OclInvalid tranclp.cases)
  apply (metis direct_subtype.intros(3) direct_subtype_x_OclInvalid direct_subtype_x_OclVoid tranclp.cases)
  apply (erule tranclp.cases)
  using direct_subtype.intros(4) direct_subtype_antisym apply auto[1]
  apply auto[1]
*)
(*
  apply (induct rule: tranclp.induct)
  using direct_subtype_antisym apply auto[1]
*)
(*
term acyclicP

lemma acyclic_direct_subtype:
  "acyclicP direct_subtype"
  apply (rule acyclicI)
  apply (auto)
  apply (erule tranclE)
  using direct_subtype_antisym apply blast
  apply (erule tranclE)
  using direct_subtype_antisym apply blast
  apply (erule tranclE)
  apply (auto)
  using direct_subtype_not_trans apply blast
  apply (erule tranclE)
*)

print_theorems

value "Set (Required Integer) \<sqsubset> Collection (Optional Real)"
value "Set (Required Integer) \<sqsubset> Set (Required Real)"


(* Дальше идет очень длинное доказательство того, что вся система типов OCL
   включая коллекции и опциональные типы образует верхнюю полурешетку.
   Было бы не плохо её нарисовать. Ещё как-то обосновать ввод SupType *)

instantiation type :: semilattice_sup
begin

definition "less_type \<equiv> direct_subtype\<^sup>+\<^sup>+"

definition "less_eq_type \<equiv> direct_subtype\<^sup>*\<^sup>*"

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: type
  apply (rule iffI; simp add: less_type_def less_eq_type_def)
  apply auto[1]


(*
value "Integer \<sqsubset>\<^sub>s Real"
value "Integer < Real"
value "Collection (Required Integer) < Collection (Optional Real)"
value "Set (Required Integer) < Collection (Required Real)"
value "Collection (Required Integer) < Collection (Required Integer)"

definition "\<tau> \<le> \<sigma> \<equiv> \<tau> = \<sigma> \<or> \<tau> < \<sigma>" for \<tau> \<sigma> :: type

definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else SupType))"

value "Real \<squnion> Boolean"
value "Real[1] \<squnion> Boolean[?]"
*)
(*definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"*)
(*
definition sup_type where
  "\<tau> \<squnion> \<sigma> \<equiv> (case (\<tau>, \<sigma>) of (ST \<tau>, ST \<sigma>) \<Rightarrow>
    ST (if ST \<tau> \<le> ST \<sigma> then \<sigma> else (if ST \<sigma> \<le> ST \<tau> then \<tau> else OclAny))
    | (CT \<tau>, CT \<sigma>) \<Rightarrow>
     CT (if CT \<tau> \<le> CT \<sigma> then \<sigma> else (if CT \<sigma> \<le> CT \<tau> then \<tau> else Collection (ST Real))))"
*)
(*
definition sup_simple_type where
 "sup_simple_type \<tau> \<sigma> \<equiv> (if ST \<tau> \<le> ST \<sigma> then \<sigma> else (if ST \<sigma> \<le> ST \<tau> then \<tau> else OclAny))"
*)
(*
fun sup_simple_type where
  "sup_simple_type OclAny _ = OclAny"
| "sup_simple_type _ OclAny = OclAny"
| "sup_simple_type OclInvalid \<tau> = \<tau>"
| "sup_simple_type \<tau> OclInvalid = \<tau>"
| "sup_simple_type OclVoid \<tau> = \<tau>"
| "sup_simple_type \<tau> OclVoid = \<tau>"
| "sup_simple_type Boolean Boolean = Boolean"
| "sup_simple_type Boolean _ = OclAny"
| "sup_simple_type _ Boolean = OclAny"
| "sup_simple_type String String = String"
| "sup_simple_type String _ = OclAny"
| "sup_simple_type _ String = OclAny"
| "sup_simple_type Real Real = Real"
| "sup_simple_type Real Integer = Real"
| "sup_simple_type Real UnlimitedNatural = Real"
| "sup_simple_type Real _ = OclAny"
| "sup_simple_type Integer Real = Real"
| "sup_simple_type Integer Integer = Integer"
| "sup_simple_type Integer UnlimitedNatural = Integer"
| "sup_simple_type Integer _ = OclAny"
| "sup_simple_type UnlimitedNatural Real = Real"
| "sup_simple_type UnlimitedNatural Integer = Integer"
| "sup_simple_type UnlimitedNatural UnlimitedNatural = UnlimitedNatural"
| "sup_simple_type UnlimitedNatural _ = OclAny"
| "sup_simple_type _ Real = OclAny"
| "sup_simple_type _ Integer = OclAny"
| "sup_simple_type _ UnlimitedNatural = OclAny"
| "sup_simple_type _ _ = OclAny"

fun sup_type and sup_collection_type where
  "sup_type (ST \<tau>) (ST \<sigma>) = ST (sup_simple_type \<tau> \<sigma>)"
| "sup_type (CT \<tau>) (CT \<sigma>) = CT (sup_collection_type \<tau> \<sigma>)"
| "sup_type _ _ = ET"
| "sup_collection_type (Set \<tau>) (Set \<sigma>) = Set (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (OrderedSet \<sigma>) = OrderedSet (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Bag \<sigma>) = Bag (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Sequence \<sigma>) = Sequence (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
*)
(*
lemma collection_not_less_self[iff]:
  "\<not> Collection \<tau> < Collection \<tau>" by (induct; simp)

lemma set_not_less_self[iff]:
  "\<not> Set \<tau> < Set \<tau>" by (induct; simp)

lemma ordered_set_not_less_self[iff]:
  "\<not> OrderedSet \<tau> < OrderedSet \<tau>" by (induct; simp)

lemma bag_not_less_self[iff]:
  "\<not> Bag \<tau> < Bag \<tau>" by (induct; simp)

lemma sequence_not_less_self[iff]:
  "\<not> Sequence \<tau> < Sequence \<tau>" by (induct; simp)

lemma required_less_ex:
  "Required \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Required \<rho> \<or> \<sigma> = Optional \<rho> \<or> \<sigma> = Optional \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma set_less_ex:
  "Set \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Set \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma ordered_set_less_ex:
  "OrderedSet \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = OrderedSet \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma bag_less_ex:
  "Bag \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Bag \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma sequence_less_ex:
  "Sequence \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Sequence \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma not_less_invalid [iff]:
  "\<not> \<tau> < OclInvalid"
  by (induct \<tau>; simp)

lemma invalid_less_void [simp]:
  "\<tau> < OclVoid \<Longrightarrow> \<tau> = OclInvalid"
  by (induct \<tau>; simp)
*)
(*inductive_cases e2[elim!]: "\<tau> <: SupType"*)

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: type
  apply (rule iffI; simp add: less_type_def less_eq_type_def)
(*
  by (rule iffI; auto simp add: less_eq_type_def less_type_def;
      induct \<tau> arbitrary: \<sigma>; auto)
*)
lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: type
  by (simp add: less_eq_type_def)

lemma conforms_to_optional:
  "\<tau>[?] <: \<rho> \<Longrightarrow> OclVoid <: \<rho>"
  apply (induct; auto)
  apply (simp add: Any_conforms_to_SupType)
  by (simp add: conforms_to.intros(2))

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (auto simp add: less_eq_type_def less_type_def)
  apply (erule notE)
  apply (induct \<tau> \<sigma> arbitrary: \<rho> rule: conforms_to.induct)
  apply auto[1]
  apply (simp add: conforms_to_optional)
  apply (metis Invalid_conforms_to_Any less_invalid_elim)
  using Any_conforms_to_SupType Required_conforms_to_Required Required_conforms_to_Optional apply force
  apply (erule optional_less_elim; simp add: conforms_to.intros)
  using Required_conforms_to_Optional dual_order.strict_trans apply blast
  using Any_conforms_to_SupType Optional_conforms_to_Optional order.strict_trans1 apply auto[1]
  using Any_conforms_to_SupType Collection_conforms_to_Collection apply auto[1]
  apply (erule set_less_elim; auto simp add: conforms_to.intros)
  apply (erule ordered_set_less_elim; auto simp add: conforms_to.intros)
  apply (erule bag_less_elim; auto simp add: conforms_to.intros)
  apply (erule sequence_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  done

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: type
  by (simp add: less_eq_type_def; auto simp add: less_le_not_le_type)

(*
fun sup_type where
  "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "\<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> SupType
     | OrderedSet \<rho> \<Rightarrow> SupType
     | Bag \<rho> \<Rightarrow> SupType
     | Sequence \<rho> \<Rightarrow> SupType
     | Collection \<rho> \<Rightarrow> SupType
     | _ \<Rightarrow> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny)))"
*)
(*definition sup_simple_type where
  "sup_simple_type \<tau> \<sigma> \<equiv> (case \<sigma>
    of Set \<rho> \<Rightarrow> SupType
     | OrderedSet \<rho> \<Rightarrow> SupType
     | Bag \<rho> \<Rightarrow> SupType
     | Sequence \<rho> \<Rightarrow> SupType
     | Collection \<rho> \<Rightarrow> SupType
     | _ \<Rightarrow> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny)))"
*)

(*
datatype type =
  SupType
| OclVoid
| OclInvalid
| Required simple_type ("_[1]")
| Optional simple_type ("_[?]")
| Collection type
| Set type
| OrderedSet type
| Bag type
| Sequence type
*)

function sup_type where
  "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Set \<tau>
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> OrderedSet \<tau>
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Bag \<tau>
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Sequence \<tau>
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Collection \<tau>
     | _ \<Rightarrow> SupType)"
| "OclVoid \<squnion> \<sigma> = (case \<sigma>
    of OclVoid \<Rightarrow> OclVoid
     | OclInvalid \<Rightarrow> OclVoid
     | Required \<rho> \<Rightarrow> Optional \<rho>
     | Optional \<rho> \<Rightarrow> Optional \<rho>
     | _ \<Rightarrow> SupType)"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "SupType \<squnion> \<sigma> = SupType"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Required \<tau>
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Optional \<tau>
     | _ \<Rightarrow> SupType)"
  by pat_completeness auto
  termination by lexicographic_order

(*
function sup_type where
  "SupType \<squnion> \<sigma> = SupType"
| "\<tau> \<squnion> SupType = SupType"
| "OclVoid \<squnion> \<sigma> = \<sigma>"
| "\<tau> \<squnion> OclVoid = \<tau>"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "\<tau> \<squnion> OclInvalid = \<tau>"
| "Required \<tau> \<squnion> Required \<sigma> = Required (\<tau> \<squnion> \<sigma>)"
| "Required \<tau> \<squnion> Optional \<sigma> = Optional (\<tau> \<squnion> \<sigma>)"
| "Optional \<tau> \<squnion> Required \<sigma> = Optional (\<tau> \<squnion> \<sigma>)"
| "Optional \<tau> \<squnion> Optional \<sigma> = Optional (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Set \<sigma> = Set (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> OrderedSet \<sigma> = OrderedSet (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Bag \<sigma> = Bag (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Sequence \<sigma> = Sequence (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
  apply pat_completeness
*)
(*(case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OclVoid \<squnion> \<sigma> = (if \<sigma> = OclInvalid then OclVoid else \<sigma>)"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "SupType \<squnion> \<sigma> = SupType"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Required \<tau>
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Optional \<tau>
     | _ \<Rightarrow> SupType)"
  by pat_completeness auto
  termination by lexicographic_order
*)

value "Required Integer \<squnion> Optional Real"
value "(Set (Required Integer)) \<squnion> (Set (Required Real))"
value "(Set (Required Integer)) \<squnion> (Bag (Optional Boolean))"
value "(Set (Required Integer)) \<squnion> Optional Real"
(*
lemma collection_less_eq_alt_def:
  "Collection \<tau> \<le> \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> \<le> \<rho> \<and> \<sigma> = Collection \<rho> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp add: less_eq_type_def)

lemma collection_less_eq_elim:
  "Collection \<tau> \<le> \<sigma> \<Longrightarrow> (\<exists>\<rho>. \<tau> \<le> \<rho> \<and> \<sigma> = Collection \<rho> \<or> \<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct \<sigma>; simp add: less_eq_type_def)

lemma q:
  "\<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow>
   \<exists>\<tau>. \<tau> \<le> \<tau> \<squnion> \<sigma>"
  by (metis less_eq_type_def less_type.simps(1))

lemma q2:
  "(\<And>\<tau>. \<tau> \<le> \<tau> \<squnion> \<sigma> \<Longrightarrow>
             Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>) \<Longrightarrow>
       \<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow>

       Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma> \<Longrightarrow>

       Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  apply auto

lemma q:
  "Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>"

lemma q1:
  "(\<And>\<tau>. \<tau> \<le> \<tau> \<squnion> Collection \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  by blast

lemma q2:
  "(\<And>\<sigma>. Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  by blast

lemma q:
  "\<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> = Collection \<rho> \<or> \<tau> = SupType"

value "Collection SupType < SupType"
value "Collection SupType < Collection SupType"
value "Collection SupType < Collection (Collection SupType)"
value "Collection (Collection SupType) < Collection SupType"

lemma q:
  "Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  apply (induct \<sigma> arbitrary: \<tau>)

lemma q:
  "(\<And>\<tau>. \<tau> \<le> \<tau> \<squnion> \<sigma> \<Longrightarrow> Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   \<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"

lemma q:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> Collection \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma> \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"

thm collection_less_alt_def
*)
(*
lemma q:
  "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> (P \<Longrightarrow> \<not> Q)"
*)


lemma void_less_eq_sup:
  "OclVoid \<le> OclVoid \<squnion> \<sigma>"
  by (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)

lemma required_less_eq_sup:
  "Required \<tau> \<le> Required \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Required_conforms_to_Required less_eq_simple_type_def sup_ge1_simple_type apply blast
  using Required_conforms_to_Optional less_eq_simple_type_def sup_ge1_simple_type apply auto
  done

lemma optional_less_eq_sup:
  "Optional \<tau> \<le> Optional \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Optional_conforms_to_Optional less_eq_simple_type_def sup_ge1_simple_type apply blast
  using Optional_conforms_to_Optional less_eq_simple_type_def sup_ge1_simple_type apply blast
  done

lemma collection_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Collection_conforms_to_Collection apply auto
  done

lemma set_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Set \<tau> \<le> Set \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Set_conforms_to_Set apply auto
  done

lemma ordered_set_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   OrderedSet \<tau> \<le> OrderedSet \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using OrderedSet_conforms_to_OrderedSet apply auto
  done

lemma bag_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Bag \<tau> \<le> Bag \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Bag_conforms_to_Bag apply auto
  done

lemma sequence_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Sequence \<tau> \<le> Sequence \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Sequence_conforms_to_Sequence apply auto
  done

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: type
  apply (induct \<tau> arbitrary: \<sigma>)
  apply simp
  using void_less_eq_sup apply auto[1]
  apply (metis (mono_tags, lifting) conforms_to.intros(3) less_eq_type_def less_type_def)
  using required_less_eq_sup apply auto[1]
  using optional_less_eq_sup apply auto[1]
  using collection_less_eq_sup apply auto[1]
  using set_less_eq_sup apply auto[1]
  using ordered_set_less_eq_sup apply auto[1]
  using bag_less_eq_sup apply auto[1]
  using sequence_less_eq_sup apply auto[1]
  done

lemma sup_sup_commut:
  "SupType \<squnion> \<sigma> = \<sigma> \<squnion> SupType"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma void_sup_commut:
  "OclVoid \<squnion> \<sigma> = \<sigma> \<squnion> OclVoid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma invalid_sup_commut:
  "OclInvalid \<squnion> \<sigma> = \<sigma> \<squnion> OclInvalid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma required_sup_commut:
  "Required \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Required \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma optional_sup_commut:
  "Optional \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Optional \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma collection_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Collection \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Collection \<tau>"
  by (cases \<sigma>; simp)

lemma set_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Set \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Set \<tau>"
  by (cases \<sigma>; simp)

lemma ordered_set_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   OrderedSet \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> OrderedSet \<tau>"
  by (cases \<sigma>; simp)

lemma bag_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Bag \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Bag \<tau>"
  by (cases \<sigma>; simp)

lemma sequence_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Sequence \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Sequence \<tau>"
  by (cases \<sigma>; simp)

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: type
  apply (induct \<tau> arbitrary: \<sigma>)
  using sup_sup_commut apply auto[1]
  using void_sup_commut apply auto[1]
  using invalid_sup_commut apply auto[1]
  using required_sup_commut apply auto[1]
  using optional_sup_commut apply auto[1]
  using collection_sup_commut apply auto[1]
  using set_sup_commut apply auto[1]
  using ordered_set_sup_commut apply auto[1]
  using bag_sup_commut apply auto[1]
  using sequence_sup_commut apply auto[1]
  done
(*
lemma less_le_not_le_type2:
  "\<tau> < \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: type
  using less_le_not_le_type by auto

lemma less_eq_type_code [code]:
  "\<tau> \<le> \<sigma> \<equiv> \<tau> = \<sigma> \<or> \<tau> < \<sigma>"
  for \<tau> \<sigma> :: type
  by (simp add: less_eq_type_def)

lemma sup_type_code [code]:
  "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"
  by (simp add: sup_type_def)
*)
lemma sup_type_idem:
  "\<tau> \<squnion> \<tau> = \<tau>"
  for \<tau> :: type
  by (induct \<tau>; simp)

lemma sup_type_strict_order:
  "\<sigma> < \<tau> \<Longrightarrow> \<tau> \<squnion> \<sigma> = \<tau>"
  for \<tau> \<sigma> :: type
  apply (simp only: less_type_def)
  apply (induct rule: conforms_to.induct)
  apply auto[1]
  apply auto[1]
  using sup_commut_type sup_type.simps(7) apply auto[1]
  apply (simp add: sup.strict_order_iff)
  using sup.absorb1 apply auto[1]
  apply (simp add: sup.strict_order_iff)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  using sup_type_idem apply auto[1]
  using sup_type_idem apply auto[1]
  using sup_type_idem apply auto[1]
  using sup_type_idem apply auto[1]
  done

lemma sup_less_then_self_eq_self2:
  "\<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> < \<sigma> \<or> \<sigma> < \<tau> \<Longrightarrow> \<tau> \<squnion> \<sigma> < \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (auto simp only: less_eq_type_def less_type_def)
  apply (simp add: less_type_def sup_commut_type sup_type_strict_order)
  apply (simp add: less_type_def sup_type_strict_order)
  done

lemma sup_less_eq_sup:
  "\<tau> < SupType \<Longrightarrow> \<sigma> < SupType \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> SupType"
  using conforms_to.intros(1) less_eq_type_def less_type_def by auto

lemma sup_less_eq_void:
  "\<tau> < OclVoid \<Longrightarrow> \<sigma> < OclVoid \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> OclVoid"
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def less_void_elim sup_type_idem)

lemma sup_less_eq_invalid:
  "\<tau> < OclInvalid \<Longrightarrow> \<sigma> < OclInvalid \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> OclInvalid"
  using less_type_def by auto

lemma sup_less_eq_required:
  "\<tau> < Required \<rho> \<Longrightarrow> \<sigma> < Required \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> Required \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_required_elim)
  apply (simp add: conforms_to.intros(3) less_eq_type_def less_type_def)
  apply (simp add: conforms_to.intros(4) less_eq_type_def less_type_def)
  apply (simp add: conforms_to.intros(4) less_eq_type_def less_type_def)
  apply (simp add: conforms_to.intros less_eq_type_def less_type_def)
  by (metis Required_conforms_to_Required sup.assoc sup.strict_order_iff)

(*  by (smt conforms_to.intros(4) le_neq_trans less_eq_type_def less_type_def sup.orderI sup.strict_order_iff sup_assoc sup_type.simps(9) type.inject(1) type.simps(101))*)

lemma sup_less_eq_optional:
  "\<tau> < Optional \<rho> \<Longrightarrow> \<sigma> < Optional \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> Optional \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_optional_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Required_conforms_to_Optional less_eq_simple_type_def sup_least_simple_type apply auto[1]
  apply (meson Optional_conforms_to_Optional eq_refl less_imp_le order.not_eq_order_implies_strict sup_least_simple_type)
  using Optional_conforms_to_Optional apply auto[1]
  apply (metis (no_types, lifting) Required_conforms_to_Optional sup.idem sup.strict_order_iff sup_assoc)
  apply (metis (no_types, lifting) Optional_conforms_to_Optional sup.left_commute sup.strict_order_iff sup_commut_simple_type)
  apply (metis (no_types, lifting) Optional_conforms_to_Optional sup.strict_order_iff sup_commut_simple_type sup_left_commute)
  apply (metis conforms_to.intros(6) sup.assoc sup.strict_order_iff)
  done

lemma sup_less_eq_collection:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Collection \<rho> \<Longrightarrow>
   \<sigma> < Collection \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Collection \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_collection_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Collection_conforms_to_Collection apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Set_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using OrderedSet_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Bag_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Sequence_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  done

lemma sup_less_eq_set:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Set \<rho> \<Longrightarrow>
   \<sigma> < Set \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Set \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_set_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Set_conforms_to_Set by auto

lemma sup_less_eq_ordered_set:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < OrderedSet \<rho> \<Longrightarrow>
   \<sigma> < OrderedSet \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> OrderedSet \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_ordered_set_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using OrderedSet_conforms_to_OrderedSet by auto

lemma sup_less_eq_bag:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Bag \<rho> \<Longrightarrow>
   \<sigma> < Bag \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Bag \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_bag_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Bag_conforms_to_Bag by auto

lemma sup_less_eq_sequence:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Sequence \<rho> \<Longrightarrow>
   \<sigma> < Sequence \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Sequence \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_sequence_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Sequence_conforms_to_Sequence by auto

lemma sup_type_strict_order2:
  "\<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (induct \<rho> arbitrary: \<tau> \<sigma>)
  apply (simp add: sup_less_eq_sup)
  apply (simp add: sup_less_eq_void)
  apply (simp add: sup_less_eq_invalid)
  apply (simp add: sup_less_eq_required)
  apply (simp add: sup_less_eq_optional)
  apply (simp add: sup_less_eq_collection)
  apply (simp add: sup_less_eq_set)
  apply (simp add: sup_less_eq_ordered_set)
  apply (simp add: sup_less_eq_bag)
  apply (simp add: sup_less_eq_sequence)
  done

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (simp add: less_eq_type_def)
  apply (elim disjE)
  using sup_type_idem apply auto[1]
  apply (simp add: sup_type_strict_order)
  apply (simp add: sup_type_strict_order sup_commut_type)
  using less_eq_type_def sup_type_strict_order2 apply auto
  done

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end

(*** Values *****************************************************************************)


(* unat может быть скастован в int или real, поэтому это не функция.
   Хотя стоп, напрямую в real не должен, только через int.
   Всё-таки это не функция. Потому что \<bottom> кастуется в разные значения.
   Хотя если добавить сюда целевой тип, то это будет функция

   Это нужно будет заменить на явное перечисление типов, когда будут значения для всех типов:
   cast_any_fun Invalid _ = \<bottom>

   Непонятно что делать с кастом unat в real. Запретить его (разрешить только через int) или нет
   Если запрещать, то это тоже нужно запретить:
   cast_any_fun Invalid Real = (RealVal \<bottom>) *)








(* Комментарий отсюда до конца файла


fun cast_any_fun :: "any \<Rightarrow> simple_type \<Rightarrow> any option" where
  "cast_any_fun (BoolVal \<bottom>) OclAny = Some InvalidAny"
| "cast_any_fun (UnlimNatVal \<bottom>) OclAny = Some InvalidAny"
| "cast_any_fun (RealVal \<bottom>) OclAny = Some InvalidAny"

| "cast_any_fun InvalidAny OclAny = None"
| "cast_any_fun (UnlimNatVal \<infinity>) OclAny = Some InvalidAny"
| "cast_any_fun x OclAny = Some x"

| "cast_any_fun InvalidAny _ = None"

| "cast_any_fun (BoolVal x) _ = None"
| "cast_any_fun (UnlimNatVal \<bottom>) Real = Some (RealVal \<bottom>)"
| "cast_any_fun (UnlimNatVal (eunat x)) Real = Some (RealVal (real x)\<^sub>\<bottom>)"
| "cast_any_fun (UnlimNatVal \<infinity>) Real = Some (RealVal \<bottom>)"
| "cast_any_fun (UnlimNatVal _) _ = None"
| "cast_any_fun (RealVal x) _ = None"

fun cast_any_fun' :: "any \<Rightarrow> simple_type \<Rightarrow> any option" where
  "cast_any_fun' InvalidAny OclAny = Some InvalidAny"
| "cast_any_fun' InvalidAny t = cast_any_fun InvalidAny t"
| "cast_any_fun' (BoolVal x) Boolean = Some (BoolVal x)"
| "cast_any_fun' (BoolVal x) t = cast_any_fun (BoolVal x) t"
| "cast_any_fun' (UnlimNatVal x) UnlimitedNatural = Some (UnlimNatVal x)"
| "cast_any_fun' (UnlimNatVal x) t = cast_any_fun (UnlimNatVal x) t"
| "cast_any_fun' (RealVal x) Real = Some (RealVal x)"
| "cast_any_fun' (RealVal x) t = cast_any_fun (RealVal x) t"

fun type_of_any :: "any \<Rightarrow> simple_type" where
(*  "type_of_any Invalid = OclInvalid"
|*) "type_of_any (BoolVal _) = Boolean"
| "type_of_any (UnlimNatVal v) = UnlimitedNatural"
| "type_of_any (RealVal v) = Real"
| "type_of_any (InvalidAny) = OclAny"
(*  "\<T> (NullVal) = OclVoid"
| "\<T> (BooleanVal _) = Boolean"
| "\<T> (RealVal _) = Real"
| "\<T> (IntegerVal _) = Integer"
| "\<T> (UnlimNatVal _) = UnlimitedNatural"
| "\<T> (StringVal _) = String"
| "\<T> (AnyVal) = OclAny"
| "\<T> (ObjectVal c _) = ObjectType c"
| "\<T> (ObjectVals c _) = ObjectType c"
*)

fun type_of_oany :: "oany \<Rightarrow> simple_type" where
  "type_of_oany (OBoolVal _) = Boolean"
| "type_of_oany (OUnlimNatVal v) = UnlimitedNatural"
| "type_of_oany (ORealVal v) = Real"
| "type_of_oany (OInvalidAny) = OclAny"
| "type_of_oany (NullAny) = OclAny"

lemma type_of_oany_eq_type_of_any:
  "type_of_oany (any_to_oany x) = type_of_any x"
  apply (cases x; simp)
  done

(*
  "cast_any x y \<Longrightarrow> any_oany x ox \<Longrightarrow> any_oany y oy \<Longrightarrow> cast_oany ox oy"
| "cast_oany (OUnlimNatVal \<epsilon>) (ORealVal \<epsilon>)"
| "cast_oany (OBoolVal \<epsilon>) NullAny"
| "cast_oany (ORealVal \<epsilon>) NullAny"
*)

fun cast_oany_fun :: "oany \<Rightarrow> simple_type \<Rightarrow> oany option" where
  "cast_oany_fun NullAny _ = None"
| "cast_oany_fun OInvalidAny _ = None"
| "cast_oany_fun (OBoolVal \<epsilon>) OclAny = Some NullAny"
| "cast_oany_fun (OBoolVal \<epsilon>) _ = None"
| "cast_oany_fun (OUnlimNatVal \<epsilon>) OclAny = Some NullAny"
| "cast_oany_fun (OUnlimNatVal \<epsilon>) Real = Some (ORealVal \<epsilon>)"
| "cast_oany_fun (OUnlimNatVal \<epsilon>) _ = None"
| "cast_oany_fun (ORealVal \<epsilon>) OclAny = Some NullAny"
| "cast_oany_fun (ORealVal \<epsilon>) _ = None"
| "cast_oany_fun (OBoolVal x\<^sub>\<box>) t = map_option any_to_oany (cast_any_fun (BoolVal x) t)"
| "cast_oany_fun (OUnlimNatVal x\<^sub>\<box>) t = map_option any_to_oany (cast_any_fun (UnlimNatVal x) t)"
| "cast_oany_fun (ORealVal x\<^sub>\<box>) t = map_option any_to_oany (cast_any_fun (RealVal x) t)"

fun cast_oany_fun' :: "oany \<Rightarrow> simple_type \<Rightarrow> oany option" where
  "cast_oany_fun' NullAny OclAny = Some NullAny"
| "cast_oany_fun' NullAny t = cast_oany_fun NullAny t"
| "cast_oany_fun' OInvalidAny OclAny = Some OInvalidAny"
| "cast_oany_fun' OInvalidAny t = cast_oany_fun OInvalidAny t"
| "cast_oany_fun' (OBoolVal x) Boolean = Some (OBoolVal x)"
| "cast_oany_fun' (OBoolVal x) t = cast_oany_fun (OBoolVal x) t"
| "cast_oany_fun' (OUnlimNatVal x) UnlimitedNatural = Some (OUnlimNatVal x)"
| "cast_oany_fun' (OUnlimNatVal x) t = cast_oany_fun (OUnlimNatVal x) t"
| "cast_oany_fun' (ORealVal x) Real = Some (ORealVal x)"
| "cast_oany_fun' (ORealVal x) t = cast_oany_fun (ORealVal x) t"

thm "tranclp_induct"

lemma cast_any_implies_cast_any_fun:
  "cast_any x y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any_fun x t = Some y"
  apply (induct rule: cast_any.induct; simp)
  done
(*
lemma q13:
  "cast_any_fun x OclInvalid \<noteq> Some Invalid"
  apply (cases x; simp)
  done

lemma q14:
  "cast_any_fun x UnlimitedNatural = Some (UnlimNatVal \<bottom>) \<Longrightarrow> x = Invalid"
  apply (cases x; simp)
  done

lemma q15:
  "cast_any_fun x UnlimitedNatural = Some (UnlimNatVal xa) \<Longrightarrow> x = Invalid"
  apply (cases x; simp)
  done

lemma q16:
  "cast_any_fun x Boolean = Some (BoolVal \<bottom>) \<Longrightarrow> x = Invalid"
  apply (cases x; simp)
  done
*)
lemma q14 [simp]:
  "cast_any_fun x UnlimitedNatural \<noteq> Some (UnlimNatVal \<bottom>)"
  apply (cases x; simp)
  done

lemma q15 [simp]:
  "cast_any_fun x UnlimitedNatural \<noteq> Some (UnlimNatVal xa)"
  apply (cases x; simp)
  done

lemma q16 [simp]:
  "cast_any_fun x Boolean \<noteq> Some (BoolVal \<bottom>)"
  apply (cases x; simp)
  done

lemma q17:
  "cast_any_fun (UnlimNatVal x) Real = Some (RealVal \<bottom>) \<Longrightarrow> x = \<bottom> \<or> x = \<infinity>"
  apply (cases x; simp)
  done
(*
lemma q18:
  "cast_any_fun x Real = Some (RealVal \<bottom>) \<Longrightarrow> x = Invalid \<or> x = UnlimNatVal \<bottom> \<or> x = UnlimNatVal \<infinity>"
  apply (cases x; simp add: q17)
  done
*)
lemma q18:
  "cast_any_fun x Real = Some (RealVal \<bottom>) \<Longrightarrow> x = UnlimNatVal \<bottom> \<or> x = UnlimNatVal \<infinity>"
  apply (cases x; simp add: q17)
  done

lemma cast_any_implies_cast_any_fun2:
  "cast_any y z \<Longrightarrow>
   (\<And>t. type_of_any y = t \<Longrightarrow>
    cast_any_fun x t = Some y) \<Longrightarrow>
   type_of_any z = t \<Longrightarrow>
   cast_any_fun x t = Some z"
  apply (induct rule: cast_any.induct)
(*  using bot_any_def q13 apply auto[1]
  using bot_any_def q13 apply auto[1]*)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  using q18 by fastforce

lemma cast_any_closure_implies_cast_any_fun:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any_fun x t = Some y"
  apply (induct arbitrary: t rule: tranclp_induct)
  apply (simp add: cast_any_implies_cast_any_fun)
  using cast_any_implies_cast_any_fun2 by blast

lemma q21:
  "cast_any_fun (BoolVal x) OclAny = Some InvalidAny \<Longrightarrow> x = \<bottom>"
  apply (cases x; simp)
  done

lemma q22:
  "cast_any_fun (UnlimNatVal x) Real = Some (RealVal y) \<Longrightarrow>
   cast_any\<^sup>+\<^sup>+ (UnlimNatVal x) (RealVal y)"
  apply (cases x; cases y; simp)
  using cast_any.simps by auto

lemma q23:
  "cast_any_fun (UnlimNatVal x) OclAny = Some InvalidAny \<Longrightarrow>
   cast_any\<^sup>+\<^sup>+ (UnlimNatVal x) InvalidAny"
  apply (cases x; simp)
  using cast_any.intros(3) cast_any.intros(5) apply auto[1]
  using cast_any.intros(1) cast_any.intros(5) apply auto
  done

lemma q24:
  "cast_any_fun (RealVal x) OclAny = Some InvalidAny \<Longrightarrow> x = \<bottom>"
  apply (cases x; simp)
  done

lemma cast_any_fun_implies_cast_any_closure:
  "cast_any_fun x t = Some y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp)
  using cast_any.intros(4) q21 apply auto[1]
  apply (simp add: q22)
  apply (simp add: q23)
  using cast_any.intros(5) q24 apply auto
(*  using bot_any_def cast_any.intros(1) apply auto[1]
  using bot_any_def cast_any.intros apply auto[1]
  using bot_any_def cast_any.intros apply auto[1]
  using bot_any_def cast_any.intros apply auto[1]
  using cast_any.intros(6) q21 apply auto[1]
  apply (simp add: q22)
  apply (simp add: q23)
  using cast_any.intros(7) q24 apply auto[1]*)
  done

lemma cast_any_closure_eq_cast_any_fun:
  "cast_any\<^sup>+\<^sup>+ x y \<longleftrightarrow> cast_any_fun x (type_of_any y) = Some y"
  using cast_any_closure_implies_cast_any_fun cast_any_fun_implies_cast_any_closure by blast

lemma cast_oany_eq_cast_any:
  "cast_oany x y = cast_any x y"
  apply (cases x; cases y; simp add: any_oany.simps cast_oany.simps)
  done

lemma cast_oany_eq_cast_any2:
  "cast_oany x y \<Longrightarrow> cast_any x y"
  apply (cases x; cases y; simp add: any_oany.simps cast_oany.simps)
  done

lemma cast_oany_eq_cast_any3:
  "cast_any x y \<Longrightarrow> cast_oany x y"
  apply (cases x; cases y; simp add: any_oany.simps cast_oany.simps)
  done

lemma q31:
  "cast_any_fun (UnlimNatVal x) Real = Some (RealVal y) \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (OUnlimNatVal x\<^sub>\<box>) (ORealVal y\<^sub>\<box>)"
  apply (cases x; cases y; simp)
  using any_oany.intros(2) any_oany.intros(3) cast_any.intros(2) cast_oany.intros(1) apply blast
  using cast_any.intros(3) cast_oany_eq_cast_any3 apply fastforce
  using cast_any.intros(1) cast_oany_eq_cast_any3 by fastforce

lemma cast_oany_eq_cast_any1:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp add: cast_any_closure_eq_cast_any_fun)
  using cast_any.intros(4) cast_oany_eq_cast_any3 q21 apply fastforce
  apply (simp add: q31)
  apply (metis any.distinct(9) any_to_oany.simps(2) any_to_oany.simps(4) cast_any.intros(1) cast_any.intros(3) cast_any.intros(5) cast_any_fun.simps(7) cast_oany_eq_cast_any3 eunat.exhaust nullable.inject nullable_def tranclp.simps)
  using cast_any.intros(5) cast_oany_eq_cast_any3 q24 by fastforce

lemma qx1:
  "(\<And>x y. P x y \<Longrightarrow> Q x y) \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> Q\<^sup>+\<^sup>+ x y"
  by (smt tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)

lemma qx2:
  "(\<And>x y. P (any_to_oany x) (any_to_oany y) \<Longrightarrow> Q x y) \<Longrightarrow> P\<^sup>+\<^sup>+ (any_to_oany x) (any_to_oany y) \<Longrightarrow> Q\<^sup>+\<^sup>+ x y"
  apply (erule qx1)

lemma qx3:
  "P\<^sup>+\<^sup>+ x y \<Longrightarrow> (\<lambda>x y. P x y)\<^sup>+\<^sup>+ x y"
  by simp

lemma tranclp_implies_tranclfun:
  "(\<And>x y. x \<noteq> y \<Longrightarrow> f x \<noteq> f y) \<Longrightarrow>
   P\<^sup>+\<^sup>+ (f x) (f y) \<Longrightarrow>
   (\<lambda>x y. P (f x) (f y))\<^sup>+\<^sup>+ x y"

term "(\<lambda>x y. P (f x) (f y))\<^sup>+\<^sup>+"
  
  term "(\<lambda>x y. ((\<lambda>z. undefined)(a\<^sub>1 := {a\<^sub>2}, a\<^sub>2 := {a\<^sub>1})) x y)\<^sup>+\<^sup>+"

lemma qx4:
  "(\<And>x y. cast_oany (any_to_oany x) (any_to_oany y) \<Longrightarrow> cast_any x y) \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ (any_to_oany x) (any_to_oany y) \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  apply (erule qx1)

lemma cast_oany_eq_cast_any2:
  "cast_oany\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  apply (erule converse_tranclpE)
   apply (simp add: cast_oany_eq_cast_any2 tranclp.r_into_trancl)
  apply (rule tranclp_rtranclp_tranclp)
(*  apply (cases x; cases y; simp)
  apply (metis any.distinct(3) any.distinct(5) any_oany.cases cast_any.simps cast_oany.cases oany.distinct(1) oany.distinct(3) oany.distinct(5) oany.distinct(7) tranclp.cases)*)

  thm cast_any_fun_implies_cast_any_closure
(*
lemma cast_oany_eq_cast_any:
  "cast_oany\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp)
*)
(*
  apply (erule tranclp.cases)
  apply (simp add: cast_oany_eq_cast_any2 tranclp.r_into_trancl)
  apply (cases x; cases y; simp)
*)
(*
  apply (erule converse_tranclpE)
  apply (simp add: cast_oany_eq_cast_any)
  apply (rule_tac cast_any_fun_implies_cast_any_closure)
*)

(*
cast_any_fun x t = Some y \<Longrightarrow>
          x = InvalidAny \<Longrightarrow>
          y = BoolVal x1 \<Longrightarrow>
          cast_oany_fun (any_to_oany x) t =
          Some (any_to_oany y)
*)
(*
value "cast_any_fun InvalidAny Boolean"
value "cast_any_fun InvalidAny UnlimitedNatural"
value "cast_any_fun InvalidAny Real"
value "cast_any_fun InvalidAny OclAny"

value "cast_oany_fun InvalidAny Boolean"
value "cast_oany_fun InvalidAny UnlimitedNatural"
value "cast_oany_fun InvalidAny Real"
value "cast_oany_fun InvalidAny OclAny"
*)

lemma q41 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some (BoolVal y)"
  by (cases t; simp)

lemma q42 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some (UnlimNatVal y)"
  by (cases t; simp)

lemma q43 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some (RealVal y)"
  by (cases t; simp)

lemma q44 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some InvalidAny"
  by (cases t; simp)

lemma cast_any_fun_implies_cast_oany_fun:
  "cast_any_fun x t = Some y \<Longrightarrow> cast_oany_fun x t = Some y"
  apply (cases x; cases y; simp)
  done
(*
lemma cast_oany_fun_implies_cast_any_fun:
  "cast_oany_fun x t = Some y \<Longrightarrow> cast_any_fun x t = Some y"
  apply (cases x; cases y)
  done
*)

lemma any_oany_implies_any_to_oany:
  "any_oany x y \<Longrightarrow> any_to_oany x = y"
  by (induct rule: any_oany.induct; simp)

lemma any_to_oany_implies_any_oany:
  "any_to_oany x = y \<Longrightarrow> any_oany x y"
  apply (induct rule: any_to_oany.induct)
  using any_oany.intros apply auto
  done

lemma cast_oany_implies_cast_oany_fun:
  "cast_oany x y \<Longrightarrow> cast_oany_fun x (type_of_oany y) = Some y"
  apply (induct rule: cast_oany.induct)
  apply (metis any_oany_implies_any_to_oany cast_any_fun_implies_cast_oany_fun cast_any_implies_cast_any_fun type_of_oany_eq_type_of_any)
  apply simp_all
  done

lemma q51:
  "t \<noteq> OclAny \<Longrightarrow> cast_oany_fun (OBoolVal x) t = None"
  by (cases t; cases x; simp)

lemma q52:
  "cast_oany_fun (OBoolVal x) OclAny = Some NullAny \<Longrightarrow> x = \<epsilon>"
  apply (cases x; simp)
  by (metis any_to_oany.simps(1) any_to_oany.simps(4) cast_any_fun.simps(1) cast_any_fun.simps(6) ebool_not.cases oany.distinct(19) oany.distinct(5) option.inject)

lemma q53:
  "cast_oany_fun (OBoolVal x) OclAny = Some OInvalidAny \<Longrightarrow> x = \<bottom>\<^sub>\<box>"
  apply (cases x; simp)
  by (metis any_to_oany.simps(4) cast_any.intros(4) cast_any_closure_eq_cast_any_fun cast_oany_eq_cast_any cast_oany_eq_cast_any3 q21 tranclp.r_into_trancl type_of_oany_eq_type_of_any)

lemma q54:
  "cast_oany_fun (OUnlimNatVal x) Boolean = None"
  by (cases x; simp)

lemma q55:
  "cast_oany_fun (OUnlimNatVal x) UnlimitedNatural = None"
  by (cases x; simp)

lemma q56:
  "cast_oany_fun (OUnlimNatVal x) Real = Some (ORealVal y) \<Longrightarrow>
   cast_oany (OUnlimNatVal x) (ORealVal y)"
  apply (cases x; cases y; simp)
  apply (metis any.distinct(1) any_to_oany.simps(2) cast_any.cases cast_any_closure_eq_cast_any_fun cast_any_fun.simps(52) cast_oany_eq_cast_any converse_tranclpE option.simps(3) type_of_oany.simps(3) type_of_oany_eq_type_of_any)
  apply (metis any.distinct(1) any_to_oany.simps(2) cast_any.simps cast_any_closure_eq_cast_any_fun cast_any_fun.simps(52) cast_oany_eq_cast_any converse_tranclpE option.distinct(1) type_of_oany.simps(3) type_of_oany_eq_type_of_any)
  by (simp add: cast_oany.intros(2))

lemma q57:
  "cast_oany_fun (OUnlimNatVal x) OclAny = Some NullAny \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ (OUnlimNatVal x) NullAny"
  apply (cases x; simp)
  apply (metis any_to_oany.simps(4) cast_any_fun.simps(2) cast_any_fun.simps(5) cast_any_fun.simps(7) eunat.exhaust oany.distinct(19) option.inject simple_type.distinct(7) type_of_any.simps(2) type_of_oany.simps(5) type_of_oany_eq_type_of_any)
  using cast_oany.intros(2) cast_oany.intros(4) by auto

lemma q58:
  "cast_oany_fun (OUnlimNatVal x) OclAny = Some OInvalidAny \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (OUnlimNatVal x) OInvalidAny"
  apply (cases x; simp)
  by (metis any_to_oany.simps(2) cast_any_fun_implies_cast_any_closure cast_oany_eq_cast_any1 type_of_oany.simps(4) type_of_oany_eq_type_of_any)

lemma q59:
  "cast_oany_fun (ORealVal x) Boolean = None"
  by (cases x; simp)

lemma q60:
  "cast_oany_fun (ORealVal x) UnlimitedNatural = None"
  by (cases x; simp)

lemma q61:
  "cast_oany_fun (ORealVal x) Real = None"
  by (cases x; simp)

lemma q62:
  "cast_oany_fun (ORealVal x) OclAny = Some NullAny \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (ORealVal x) NullAny"
  apply (cases x; simp)
  apply (metis any_to_oany.simps(3) cast_any_fun_implies_cast_any_closure cast_oany_eq_cast_any1 type_of_oany.simps(5) type_of_oany_eq_type_of_any)
  by (simp add: cast_oany.intros(4) tranclp.r_into_trancl)

lemma q63:
  "cast_oany_fun (ORealVal x) OclAny = Some OInvalidAny \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (ORealVal x) OInvalidAny"
  apply (cases x; simp)
  by (metis any_to_oany.simps(3) cast_any_fun_implies_cast_any_closure cast_oany_eq_cast_any1 type_of_oany.simps(4) type_of_oany_eq_type_of_any)

lemma cast_oany_fun_implies_cast_oany:
  "cast_oany_fun x (type_of_oany y) = Some y \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp)
  apply (simp add: cast_oany.simps q51 q52)
  apply (simp add: cast_oany.simps q51 q52)
  apply (simp add: cast_oany.simps q51 q52)
  using cast_oany.intros(3) q52 apply auto[1]
  using cast_any.intros(4) cast_oany_eq_cast_any3 q53 apply fastforce
  apply (simp add: q54)
  apply (simp add: q55)
  apply (simp add: q56 tranclp.r_into_trancl)
  apply (simp add: q57)
  apply (simp add: q58)
  apply (simp add: q59)
  apply (simp add: q60)
  apply (simp add: q61)
  apply (simp add: q62)
  apply (simp add: q63)
  done

lemma q71:
  "cast_any y z \<Longrightarrow>
   cast_oany_fun x (type_of_oany y) = Some (any_to_oany y) \<Longrightarrow>
   cast_oany_fun x (type_of_oany z) = Some (any_to_oany z)"

lemma cast_oany_implies_cast_oany_fun2:
  "cast_oany y z \<Longrightarrow>
   cast_oany_fun x (type_of_oany y) = Some y \<Longrightarrow>
   cast_oany_fun x (type_of_oany z) = Some z"
  apply (induct rule: cast_oany.induct)


lemma cast_oany_closure_implies_cast_oany_fun:
  "cast_oany\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_oany_fun x (type_of_oany y) = Some y"
  apply (induct rule: tranclp_induct)
  apply (simp add: cast_oany_implies_cast_oany_fun)


(*

lemma cast_any_implies_cast_any_fun2:
  "cast_any y z \<Longrightarrow>
   (\<And>t. type_of_any y = t \<Longrightarrow>
    cast_any_fun x t = Some y) \<Longrightarrow>
   type_of_any z = t \<Longrightarrow>
   cast_any_fun x t = Some z"
  apply (induct rule: cast_any.induct)
(*  using bot_any_def q13 apply auto[1]
  using bot_any_def q13 apply auto[1]*)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  using q18 by fastforce

lemma cast_any_closure_implies_cast_any_fun:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any_fun x t = Some y"
  apply (induct arbitrary: t rule: tranclp_induct)
  apply (simp add: cast_any_implies_cast_any_fun)
  using cast_any_implies_cast_any_fun2 by blast


*)


lemma cast_oany_closure_eq_cast_oany_fun:
  "cast_oany\<^sup>+\<^sup>+ x y \<longleftrightarrow> cast_oany_fun x (type_of_oany y) = Some y"

(* Если добавить тип в качестве параметра, то из SetVal его можно убрать *)

(*
| "cast_oany (OBoolVal x) (OBoolVal y) \<Longrightarrow> cast_val (OptionalVal (OBoolVal x)) (OptionalVal (OBoolVal y))"
*)

inductive cast_val :: "val \<Rightarrow> val \<Rightarrow> bool" where
  "cast_any x y \<Longrightarrow> cast_val (RequiredVal x) (RequiredVal y)"
| "cast_oany x y \<Longrightarrow> cast_val (OptionalVal x) (OptionalVal y)"
| "cast_val (RequiredVal x) (OptionalVal x)"
| "rel_fset cast_val xs ys \<Longrightarrow>
   cast_val (SetVal xs\<^sub>\<bottom>) (SetVal ys\<^sub>\<bottom>)"

code_pred [show_modes] cast_val .

value "cast_val
         (SetVal (errorable
           {|RequiredVal (BoolVal True\<^sub>\<bottom>), RequiredVal (BoolVal False\<^sub>\<bottom>)|}))
         (SetVal (errorable
           {|OptionalVal (BoolVal False\<^sub>\<bottom>), OptionalVal (BoolVal True\<^sub>\<bottom>)|}))"
value "cast_val
         (SetVal (errorable
           {|RequiredVal (BoolVal True\<^sub>\<bottom>)|}))
         (SetVal (errorable
           {|OptionalVal (BoolVal True\<^sub>\<bottom>), OptionalVal (BoolVal False\<^sub>\<bottom>)|}))"
(*value "cast_val
         (SetVal (errorable
           {|RequiredVal (BoolVal True\<^sub>\<bottom>), RequiredVal (Invalid)|}))
         (SetVal (errorable
           {|OptionalVal (OInvalid), OptionalVal (BoolVal True\<^sub>\<bottom>)|}))"*)

term "Predicate.the (cast_oany_i_o x)"

definition "cast_any_fun2 x \<equiv> Predicate.the (cast_any_i_o x)"
definition "cast_oany_fun2 x \<equiv> Predicate.the (cast_oany_i_o x)"

term map_option
term "map_option RequiredVal"
term the

fun cast_val_fun :: "val \<Rightarrow> type \<Rightarrow> val option" where
  "cast_val_fun (RequiredVal x) (Required t) = map_option RequiredVal (cast_any_fun x t)"
| "cast_val_fun (OptionalVal x) (Optional t) = map_option OptionalVal (cast_oany_fun x t)"
| "cast_val_fun (RequiredVal x) (Optional t) = map_option OptionalVal (cast_oany_fun x t)"
| "cast_val_fun (OptionalVal x) _ = None"
| "cast_val_fun (RequiredVal x) _ = None"
| "cast_val_fun (SetVal xs\<^sub>\<bottom>) (Set t) = Some (SetVal (fimage (\<lambda>x. the (cast_val_fun x t)) xs)\<^sub>\<bottom>)"
| "cast_val_fun (SetVal xs) _ = None"

fun cast_val_fun' :: "val \<Rightarrow> type \<Rightarrow> val option" where
  "cast_val_fun' (RequiredVal x) (Required t) = map_option RequiredVal (cast_any_fun' x t)"
| "cast_val_fun' (OptionalVal x) (Optional t) = map_option OptionalVal (cast_oany_fun' x t)"
| "cast_val_fun' (RequiredVal x) (Optional t) = map_option OptionalVal (cast_oany_fun' x t)"
| "cast_val_fun' (OptionalVal x) _ = None"
| "cast_val_fun' (RequiredVal x) _ = None"
| "cast_val_fun' (SetVal xs\<^sub>\<bottom>) (Set t) = Some (SetVal (fimage (\<lambda>x. the (cast_val_fun' x t)) xs)\<^sub>\<bottom>)"
| "cast_val_fun' (SetVal xs) _ = None"

value "cast_any_fun (UnlimNatVal (eunat 1)) Real"
value "cast_val_fun (RequiredVal (UnlimNatVal (eunat 1))) UnlimitedNatural[1]"
value "cast_val_fun (RequiredVal (UnlimNatVal (eunat 1))) UnlimitedNatural[?]"
value "cast_val_fun' (RequiredVal (UnlimNatVal (eunat 1))) UnlimitedNatural[1]"
value "cast_val_fun' (RequiredVal (UnlimNatVal (eunat 1))) UnlimitedNatural[?]"
value "cast_val_fun (RequiredVal (UnlimNatVal (eunat 1))) Real[1]"
value "cast_val_fun (RequiredVal (UnlimNatVal (eunat 1))) Real[?]"
value "cast_val_fun (RequiredVal (UnlimNatVal (eunat 1))) OclAny[?]"
value "cast_val_fun (SetVal {|RequiredVal (UnlimNatVal (eunat 1))|}\<^sub>\<bottom>) (Set Real[?])"

(*
Collection - 
Set        - set
OrderedSet - list? dlist?
Bag        - multiset
Sequence   - list
*)

definition cast (infix "as!" 55) where
  "cast \<equiv> cast_val\<^sup>+\<^sup>+"

definition cast_eq (infix "as" 55) where
  "cast_eq \<equiv> cast_val\<^sup>*\<^sup>*"


lemma cast_any_not_refl:
  "cast_any x y \<Longrightarrow> cast_any y x \<Longrightarrow> False"
  by (induct rule: cast_any.induct; simp add: cast_any.simps)

inductive_cases cast_oany_NullAny_OBoolVal: "cast_oany NullAny (OBoolVal \<epsilon>)"
inductive_cases cast_oany_NullAny_ORealVal: "cast_oany NullAny (ORealVal \<epsilon>)"

lemma cast_oany_not_refl:
  "cast_oany x y \<Longrightarrow> cast_oany y x \<Longrightarrow> False"
  apply (induct rule: cast_oany.induct)
  using any_oany_implies_any_to_oany cast_any_not_refl cast_oany_eq_cast_any2 apply blast
  apply (metis any_oany_implies_any_to_oany cast_any_not_refl cast_oany.cases cast_oany.intros(2) cast_oany_eq_cast_any2 oany.distinct(11) oany.distinct(9))
  apply (metis any_oany_implies_any_to_oany cast_any_not_refl cast_oany.intros(3) cast_oany_eq_cast_any2 cast_oany_NullAny_OBoolVal)
  apply (erule cast_oany_NullAny_ORealVal)
  using any_oany_implies_any_to_oany cast_any_not_refl cast_oany.intros(4) cast_oany_eq_cast_any2 by fastforce

lemma cast_any_not_refl2:
  "cast_any x y \<Longrightarrow> \<not> cast_any\<^sup>*\<^sup>* y x"
  by (metis cast_any.cases cast_any_closure_eq_cast_any_fun cast_any_fun.simps(4) cast_any_fun.simps(52) option.distinct(1) rtranclp_into_tranclp1 type_of_any.simps(3) type_of_any.simps(4))

lemma cast_any_cl_implies_cast_oany_cl:
  "cast_any\<^sup>*\<^sup>* x y \<Longrightarrow> cast_oany\<^sup>*\<^sup>* x y"
  by (metis Nitpick.rtranclp_unfold cast_oany_eq_cast_any1 tranclp_into_rtranclp)

thm cast_oany_eq_cast_any1


lemma q:
  "(\<And>x y. P x y \<Longrightarrow> Q x y) \<Longrightarrow> P\<^sup>*\<^sup>* x y \<Longrightarrow> Q\<^sup>*\<^sup>* x y"
  by (metis mono_rtranclp)

lemma q2:
  "(\<And>x y. P (any_to_oany x) (any_to_oany y) \<Longrightarrow> Q x y) \<Longrightarrow> P\<^sup>*\<^sup>* (any_to_oany x) (any_to_oany y) \<Longrightarrow> Q\<^sup>*\<^sup>* x y"

thm mono_rtranclp

lemma q2:
  "(\<And>x y. cast_oany x y \<Longrightarrow> cast_any x y) \<Longrightarrow> cast_oany\<^sup>*\<^sup>* x y \<Longrightarrow> cast_any\<^sup>*\<^sup>* x y"
  apply (erule q)
  apply (induct rule: rtranclp_induct)

lemma cast_oany_cl_implies_cast_any_cl:
  "cast_oany\<^sup>*\<^sup>* x y \<Longrightarrow> cast_any\<^sup>*\<^sup>* x y"

lemma cast_oany_not_refl2:
  "cast_oany x y \<Longrightarrow> cast_oany\<^sup>*\<^sup>* y x \<Longrightarrow> False"
  apply (erule cast_oany.cases)
  apply (cases x; cases y; simp)
(*  apply (induct rule: cast_oany.induct)*)





(*
inductive cast_either :: "val \<times> val \<Rightarrow> val \<times> val \<Rightarrow> bool" (infix "as*" 55) where
  "x as* x"
| "a = x \<Longrightarrow> b as! y \<Longrightarrow> (a, b) as* (x, y)"
| "a as! x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"

inductive_cases cast_eitherE[elim!]: "(a, b) as* (x, y)"

code_pred [show_modes] cast_either .
*)
(*** Type of Val ************************************************************************)

fun type_of_val :: "val \<Rightarrow> type" ("\<T> _" [75] 75) where
  "\<T> (NullVal) = OclVoid"
| "\<T> (BooleanVal _) = Boolean"
| "\<T> (RealVal _) = Real"
| "\<T> (IntegerVal _) = Integer"
| "\<T> (UnlimNatVal _) = UnlimitedNatural"
| "\<T> (StringVal _) = String"
| "\<T> (AnyVal) = OclAny"
| "\<T> (ObjectVal c _) = ObjectType c"
| "\<T> (ObjectVals c _) = ObjectType c"

(*
fun type_of_val :: "val \<Rightarrow> (oid \<Rightarrow> cls) \<Rightarrow> type" ("\<T> _ _" [75] 75) where
  "\<T> (NullVal) x = VoidType"
| "\<T> (BooleanVal _) x = BooleanType"
| "\<T> (RealVal _) x = RealType"
| "\<T> (IntegerVal _) x = IntegerType"
| "\<T> (UnlimNatVal _) x = UnlimNatType"
| "\<T> (StringVal _) x = StringType"
| "\<T> (AnyVal) x = OclAny"
| "\<T> (ObjectVal i) x = ObjectType (x i)"
*)
lemma type_of_val_less_any_type:
  "(x \<noteq> AnyVal) = (\<T> x < OclAny)"
  apply (cases x)
  using less_type.simps by auto
(*
lemma type_of_val_less_any_type:
  "(x \<noteq> AnyVal \<and> (\<forall>y. x \<noteq> ObjectVal y)) = (\<T> x < OclAny)"
  apply (cases x; auto)
*)
lemma type_of_val_less:
  "x as! y \<Longrightarrow>
   \<T> x < \<T> y"
  by (induct rule: cast.induct; simp add: type_of_val_less_any_type less_type.simps)

lemma type_of_val_less_eq:
  "x as y \<Longrightarrow>
   \<T> x \<le> \<T> y"
  using cast_eq_def less_eq_type_def type_of_val_less by auto
(*
lemma type_of_pair_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   \<T> x \<squnion> \<T> y = \<tau>"
  apply (erule cast_eitherE; simp)
  apply (metis sup.strict_order_iff type_of_val_less)
  by (metis sup.strict_order_iff sup_commut_type type_of_val_less)

lemma type_of_pair_less_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b"
  apply (erule cast_eitherE; simp)
  apply (simp add: less_eq_type_def less_supI2 type_of_val_less)
  apply (simp add: less_eq_type_def less_supI1 type_of_val_less)
  done  
*)
(*** Val for Type ***********************************************************************)

lemma type_of_val_eq_rev:
  "\<T> x = t \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x = y"
  by auto
(*
lemma type_of_val_less_rev:
  "\<T> x < t \<Longrightarrow> t \<noteq> ObjectType c \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as! y"
  apply (induct x; induct t; simp)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  (*using cast.intros type_of_val.simps apply blast*)
  apply (metis cast.intros(6) cast.intros(7) cast.intros(8) errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(7) cast.intros(8) cast.intros(9) errorable.exhaust type_of_val.simps(3))*)
  using cast.intros type_of_val.simps apply blast
  apply (metis cast.intros(13) cast.intros(14) cast.intros(15) cast.intros(16) enat.exhaust errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(14) cast.intros(15) cast.intros(16) cast.intros(17) enat.exhaust errorable.exhaust type_of_val.simps(3))*)
  apply (metis cast.intros(9) cast.intros(10) cast.intros(11) cast.intros(12) enat.exhaust errorable.exhaust type_of_val.simps(4))
  (*apply (metis cast.intros(10) cast.intros(11) cast.intros(12) cast.intros(13) enat.exhaust errorable.exhaust type_of_val.simps(4))*)
  using cast.intros type_of_val.simps apply blast
  (*using cast.intros(18) type_of_val.simps(7) apply blast*)
  done
*)
lemma type_of_val_less_rev:
  "\<T> x < t \<Longrightarrow> \<forall>c. t \<noteq> ObjectType c \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as! y"
  apply (induct x; induct t; simp add: less_type.simps)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  apply auto[1]
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  (*using cast.intros type_of_val.simps apply blast*)
  apply (metis cast.intros(6) cast.intros(7) cast.intros(8) errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(7) cast.intros(8) cast.intros(9) errorable.exhaust type_of_val.simps(3))*)
  using cast.intros type_of_val.simps apply blast
  apply (metis cast.intros(13) cast.intros(14) cast.intros(15) cast.intros(16) enat.exhaust errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(14) cast.intros(15) cast.intros(16) cast.intros(17) enat.exhaust errorable.exhaust type_of_val.simps(3))*)
  apply (metis cast.intros(9) cast.intros(10) cast.intros(11) cast.intros(12) enat.exhaust errorable.exhaust type_of_val.simps(4))
  (*apply (metis cast.intros(10) cast.intros(11) cast.intros(12) cast.intros(13) enat.exhaust errorable.exhaust type_of_val.simps(4))*)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  done

lemma type_of_val_less_eq_rev:
  "\<T> x \<le> t \<Longrightarrow> \<forall>c. t \<noteq> ObjectType c \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as y"
  by (meson cast_eq_def less_eq_type_def type_of_val_less_rev)

(*** Type System ************************************************************************)
(*
interpretation ocl_type_system: type_system
  "op \<squnion> :: type \<Rightarrow> type \<Rightarrow> type"
  "op \<le> :: type \<Rightarrow> type \<Rightarrow> bool"
  "op < :: type \<Rightarrow> type \<Rightarrow> bool"
  cast_eq
  cast
  type_of_val
  apply (standard)
  apply (simp add: less_le_not_le_val)
  apply (simp add: cast_eq_def)
  using order_trans_val apply blast
  apply (simp add: eq_iff less_eq_val_def)
  apply simp
  apply (simp add: type_of_val_less_eq)
  apply (simp add: type_of_val_less)
  apply simp
  apply (simp add: type_of_val_less_eq_rev)
  apply (simp add: type_of_val_less_rev)
  done
*)
inductive cast_either :: "val \<times> val \<Rightarrow> val \<times> val \<Rightarrow> bool" (infix "as*" 55) where
(*  "x as* x"*)
  "a = x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"
| "a = x \<Longrightarrow> b as! y \<Longrightarrow> (a, b) as* (x, y)"
| "a as! x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"

lemma cast_either_perm:
  "(a, b) as* (x, y) = (b, a) as* (y, x)"
  apply (auto; erule cast_either.cases; elim Pair_inject)
  using cast_either.intros apply auto
  done

lemma type_of_pair_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   \<T> x \<squnion> \<T> y = \<tau>"
  apply (erule cast_either.cases; elim Pair_inject)
  apply simp
  apply (metis sup.strict_order_iff type_of_val_less)
  apply (metis sup.strict_order_iff type_of_val_less sup_commut_type)
  (*apply (metis ocl_type_system.type_of_val_less sup.strict_order_iff)
  apply (metis ocl_type_system.type_of_val_less sup.strict_order_iff sup_commut_type)*)
  done

lemma type_of_pair_less_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b"
  apply (erule cast_either.cases; elim Pair_inject; auto)
  apply (simp add: le_supI2 less_le_not_le_val type_of_val_less_eq)
  apply (simp add: le_supI1 less_le_not_le_val type_of_val_less_eq)
  (*apply (simp add: le_supI2 ocl_type_system.type_of_val_less_eq)
  apply (simp add: le_supI1 ocl_type_system.type_of_val_less_eq)*)
  done  

(*** Misc *******************************************************************************)

lemma type_max_simp:
  "x \<squnion> y = (t :: type) \<Longrightarrow> t \<noteq> OclAny \<Longrightarrow> (x = t \<and> y \<le> t) \<or> (x \<le> t \<and> y = t)"
  using sup_type_def by auto

lemma type_max_simp_elim:
  "x \<squnion> y = (t :: type) \<Longrightarrow>
   (t \<noteq> OclAny) \<Longrightarrow>
   (x = t \<and> y \<le> t \<Longrightarrow> P) \<Longrightarrow>
   (x \<le> t \<and> y = t \<Longrightarrow> P) \<Longrightarrow> P"
  using type_max_simp by blast

lemma type_of_val_eq_rev_elim:
  "\<T> x = t \<Longrightarrow>
   (\<exists>y. \<T> y = t \<and> x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma type_of_val_less_eq_rev_elim:
  "\<T> x \<le> t \<Longrightarrow> \<forall>c. t \<noteq> ObjectType c \<Longrightarrow>
   (\<exists>y. \<T> y = t \<and> x as y \<Longrightarrow> P) \<Longrightarrow> P"
  using type_of_val_less_eq_rev by blast

lemma type_of_pair_eq_rev:
  "\<T> x \<squnion> \<T> y = \<tau> \<Longrightarrow>
   \<tau> \<noteq> OclAny \<Longrightarrow>
   \<forall>c. \<tau> \<noteq> ObjectType c \<Longrightarrow>
   \<exists>a b.
      \<T> a = \<tau> \<and> \<T> b = \<tau> \<and>
      (x, y) as* (a, b)"
  apply (erule type_max_simp_elim)
  apply (simp)
  apply (erule conjE)
  apply (erule type_of_val_less_eq_rev_elim)
  apply simp (* \<forall>c. \<tau> \<noteq> ObjectType c \<Longrightarrow> *)
  apply (erule type_of_val_eq_rev_elim)
  apply (metis cast_either.intros(1) cast_either.intros(2) cast_eq_def)
  apply (erule conjE)
  apply (erule type_of_val_less_eq_rev_elim)
  apply (erule type_of_val_eq_rev_elim)
  apply simp (* \<forall>c. \<tau> \<noteq> ObjectType c \<Longrightarrow> *)
  apply (metis cast_either.intros(1) cast_either.intros(3) cast_eq_def)
  done

lemma cast_either_ex_intros:
  "\<exists>x y. a = P x \<and> b = P y \<or>
         a = P x \<and> b as! P y \<or>
         a as! P x \<and> b = P y \<Longrightarrow>
   \<exists>x y. (a, b) as* (P x, P y)"
  by (meson cast_either.intros(1) cast_either.intros(2) cast_either_perm)
(*  using ocl_type_system.cast_either.intros by blast*)

(*** Specifics **************************************************************************)

lemma boolean_val_exists:
  "\<T> x = Boolean \<Longrightarrow> \<exists>y. x = BooleanVal y"
(*
  apply (rule exE)
  apply (erule type_of_val_eq_rev)
  using cast.simps by auto
*)
  by (cases x; simp)

lemma real_val_exists:
  "\<T> x = Real \<Longrightarrow> \<exists>y. x = RealVal y"
  by (cases x; simp)

lemma integer_val_exists:
  "\<T> x = Integer \<Longrightarrow> \<exists>y. x = IntegerVal y"
  by (cases x; simp)

lemma unlim_nat_val_exists:
  "\<T> x = UnlimitedNatural \<Longrightarrow> \<exists>y. x = UnlimNatVal y"
  by (cases x; simp)

lemma boolean_val_pair_exists:
  "\<T> x \<squnion> \<T> y = Boolean \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (BooleanVal xn, BooleanVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis boolean_val_exists less_eq_type_def type.distinct(51) type_of_val_less_rev)
  apply (metis boolean_val_exists less_eq_type_def type.distinct(51) type_of_val_less_rev)
  (*apply (metis boolean_val_exists cast_eq_def type.distinct(35) type_of_val_less_eq_rev)
  apply (metis boolean_val_exists cast_eq_def type.distinct(35) type_of_val_less_eq_rev)*)
  (*apply (metis boolean_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis boolean_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma real_val_pair_exists:
  "\<T> x \<squnion> \<T> y = Real \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (RealVal xn, RealVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis real_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  apply (metis real_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  (*apply (metis le_less real_val_exists type.distinct(43) type_of_val_less_rev)
  apply (metis le_less real_val_exists type.distinct(43) type_of_val_less_rev)*)
  (*apply (metis real_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis real_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma integer_val_pair_exists:
  "\<T> x \<squnion> \<T> y = Integer \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (IntegerVal xn, IntegerVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis integer_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  apply (metis integer_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  (*apply (metis cast_eq_def integer_val_exists type.distinct(49) type_of_val_less_eq_rev_elim)
  apply (metis cast_eq_def integer_val_exists type.distinct(49) type_of_val_less_eq_rev_elim)*)
  (*apply (metis integer_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis integer_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma unlim_nat_val_pair_exists:
  "\<T> x \<squnion> \<T> y = UnlimitedNatural \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (UnlimNatVal xn, UnlimNatVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis unlim_nat_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  apply (metis unlim_nat_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  (*apply (metis cast_eq_def type.distinct(53) type_of_val_less_eq_rev_elim unlim_nat_val_exists)
  apply (metis cast_eq_def type.distinct(53) type_of_val_less_eq_rev_elim unlim_nat_val_exists)*)
  (*apply (metis unlim_nat_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis unlim_nat_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma real_type_le_cases:
  "x \<squnion> y \<le> Real \<Longrightarrow>
   (x \<squnion> y = Real \<Longrightarrow> P) \<Longrightarrow> 
   (x \<squnion> y = Integer \<Longrightarrow> P) \<Longrightarrow>
   (x \<squnion> y = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> 
   (x \<squnion> y = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases x; cases y; simp add: less_eq_type_def less_type.simps sup_type_def)
  by blast
  (*using less_type.elims(2) by blast8*)
  (*by (cases x; cases y; simp add: less_eq_type_def sup_type_def)*)

lemma num_type_cases:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> Real \<Longrightarrow>
   OclVoid < \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis dual_order.strict_iff_order real_type_le_cases)

(*** Model ******************************************************************************)

type_synonym class_set = "cls fset"
type_synonym attrs = "cls \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f type"
(*type_synonym assoc_end = "cls \<times> role \<times> nat \<times> enat"*)
type_synonym assoc_end = "cls \<times> nat \<times> enat"
(* Плюс такого представления ещё и в том, что имена ролей уникальные *)
type_synonym assocs = "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f assoc_end"
type_synonym model = "class_set \<times> attrs \<times> assocs"

definition assoc_end_class :: "assoc_end \<Rightarrow> cls" where
  "assoc_end_class \<equiv> fst"
(*
definition assoc_end_role :: "assoc_end \<Rightarrow> role" where
  "assoc_end_role \<equiv> fst \<circ> snd"

definition assoc_end_min :: "assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd \<circ> snd"

definition assoc_end_max :: "assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd \<circ> snd"
*)
definition assoc_end_min :: "assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd"

definition assoc_end_max :: "assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd"

definition assoc_end_min_le_max :: "assoc_end \<Rightarrow> bool" where
  "assoc_end_min_le_max x \<equiv> assoc_end_min x \<le> assoc_end_max x"

definition assoc_classes :: "assoc_end list \<Rightarrow> cls fset" where
  "assoc_classes \<equiv> fset_of_list \<circ> (map assoc_end_class)"

definition associates :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls fset" where
  "associates ends \<equiv>  assoc_end_class |`| fmran ends"
(*
definition find_assocs :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs assocs cls \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of Some ends \<Rightarrow>
      cls |\<in>| associates ends) assocs"
*)

definition assoc_refer_class :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> bool" where
  "assoc_refer_class ends cls \<equiv>
    fBex (fmdom ends) (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end)"

definition find_assocs :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs assocs cls \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      assoc_refer_class ends cls) assocs"

definition participating :: "assocs \<Rightarrow> cls \<Rightarrow> assoc fset" where
  "participating assocs cls \<equiv> fmdom (find_assocs assocs cls)"
(*
term "fmran (find_assocs assocs1 cls1)"
definition find_assoc_end :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end" where
  "find_assoc_end assocs cls role \<equiv> fmran (find_assocs assocs cls)"
*)
(*
definition find_assocs2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs2 assocs cls role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls) (find_assocs assocs cls))"
*)
definition find_assocs2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs2 assocs cls role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls) (find_assocs assocs cls))"
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc" where
  "find_assoc assocs cls role \<equiv> fthe_elem (find_assocs2 assocs cls role)"
*)


definition assoc_refer_class2 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> nat" where
  "assoc_refer_class2 ends cls \<equiv>
    fcard (fmdom (fmfilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end) ends))"

definition assoc_refer_class3 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "assoc_refer_class3 ends cls \<equiv>
    fmfilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls \<noteq> assoc_end_class end) ends"

definition q :: "cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "q cls ends \<equiv> case assoc_refer_class2 ends cls
      of 0 \<Rightarrow> fmempty
       | (Suc 0) \<Rightarrow> assoc_refer_class3 ends cls
       | (Suc (Suc 0)) \<Rightarrow> ends"

(* Example *)

definition classes1 :: "cls fset" where
  "classes1 \<equiv> {|''Person'',''Car'',''Company''|}"

definition attrs1 :: "attrs" where
  "attrs1 = fmap_of_list [
    (''Person'', fmap_of_list [
      (''name'', String)]),
    (''Car'', fmap_of_list [
      (''color'', String)]),
    (''Company'', fmap_of_list [
      (''name'', String)])]"

definition assocs1 :: "assocs" where
  "assocs1 \<equiv> fmap_of_list [
    (''PersonCar'', fmap_of_list [
      (''driver'', (''Person'',1,1)),
      (''car'', (''Car'',1,3))]),
    (''Employment2'', fmap_of_list [
      (''employer'', (''Person'',0,1)),
      (''employee'', (''Person'',1,20))]),
    (''Employment'', fmap_of_list [
      (''company'', (''Company'',0,2)),
      (''employee'', (''Person'',1,\<infinity>))])]"

definition model1 :: "model" where
  "model1 \<equiv> (classes1, attrs1, assocs1)"


definition find_assocs3 :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs3 assocs cls \<equiv> fmmap (q cls) assocs"

definition find_assocs4 :: "assocs \<Rightarrow> role \<Rightarrow> assocs" where
  "find_assocs4 assocs role \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> True) assocs"

definition assoc_refer_class5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_class5 ends cls role \<equiv>
    case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
      cls = assoc_end_class end"
(*
definition assoc_refer_class5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_class5 ends cls role \<equiv>
    (map_option assoc_end_class \<circ> fmlookup ends) role = Some cls"
*)
definition assoc_refer_role5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_role5 ends role \<equiv> fmlookup ends role \<noteq> None"

definition find_assocs5 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> role \<Rightarrow> assocs" where
  "find_assocs5 assocs cls from to \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class5 ends cls from \<and> assoc_refer_role5 ends to) assocs"
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc assocs cls role \<equiv>
    fmlookup (fthe_elem (fmran (find_assocs5 assocs cls role))) role"
*)
(*
definition find_assocs4 :: "assocs \<Rightarrow> cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "find_assocs4 assocs cls \<equiv> ffold fmadd fmempty (fmran (find_assocs3 assocs cls))"
*)
value "find_assocs5 assocs1 ''Person'' ''driver'' ''car''"
value "find_assocs5 assocs1 ''Person'' ''driver'' ''car1''"
(*
value "fmadd
  (fmap_of_list [(1::nat,2::nat)])
  (fmap_of_list [(2::nat,3::nat)])"

value "ffold fmadd fmempty {|
  fmap_of_list [(1::nat,2::nat)],
  fmap_of_list [(2::nat,3::nat)]|}"
*)

term fmmap
term fmfilter
(*
definition find_assocs3 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs3 assocs cls role \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls) (fmdom (find_assocs assocs cls))"
*)

(*
definition navends :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role fset" where
  "navends ends cls \<equiv> fmfilter (\<lambda>role.
    case fmlookup ends role of Some end \<Rightarrow>
      ) ends"
*)

(*
primrec findnn :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat option" where
  "findnn _ [] _ = None"
| "findnn P (x#xs) n = (if P x then Some n else findnn P xs (n+1))"

definition findn :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "findn P xs \<equiv> findnn P xs 0"

definition find_assoc_end :: "assoc_end list \<Rightarrow> role \<Rightarrow> nat option" where
  "find_assoc_end ends role \<equiv> findn (\<lambda>x. assoc_end_role x = role) ends"
*)
(*
definition find_assoc_end :: "assoc_end list \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc_end ends role \<equiv> find (\<lambda>x. assoc_end_role x = role) ends"

definition assoc_roles_distinct :: "assoc_end list \<Rightarrow> bool" where
  "assoc_roles_distinct \<equiv> distinct \<circ> (map assoc_end_role)"

definition assoc_is_ok :: "assoc_end list \<Rightarrow> bool" where
  "assoc_is_ok assoc \<equiv> assoc_roles_distinct assoc \<and> list_all assoc_end_min_le_max assoc"
*)
definition assoc_is_ok2 :: "class_set \<Rightarrow> assoc_end \<Rightarrow> bool" where
  "assoc_is_ok2 classes end \<equiv> assoc_end_class end |\<in>| classes \<and> assoc_end_min_le_max end"

definition assoc_is_ok :: "class_set \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> bool" where
  "assoc_is_ok classes role \<equiv> fBall (fmran role) (assoc_is_ok2 classes)"

inductive model_is_ok :: "model \<Rightarrow> bool" where
  "(* Attributes defined for existing classes *)
   fmdom attrs |\<subseteq>| classes \<Longrightarrow>
   (* Associations defined for existing classes *)
   (*fBall (fmran assocs) (\<lambda>x. assoc_classes x |\<subseteq>| classes) \<Longrightarrow>*)
   (* Associations defined for existing classes and min \<le> max *)
   fBall (fmran assocs) (assoc_is_ok classes) \<Longrightarrow>
   (* TODO: Unique names in full descriptor *)
   model_is_ok (classes, attrs, assocs)"

code_pred [show_modes] model_is_ok .

(*** Data *******************************************************************************)

type_synonym objects = "oid \<rightharpoonup>\<^sub>f cls"
type_synonym attr_vals = "oid \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f val"
(*type_synonym link = "oid list"
type_synonym links = "assoc \<rightharpoonup>\<^sub>f link fset"*)
type_synonym links = "assoc \<rightharpoonup>\<^sub>f (role \<rightharpoonup>\<^sub>f oid) fset"
type_synonym data = "objects \<times> attr_vals \<times> links"
(*
definition linked_objs :: "link fset \<Rightarrow> oid \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> oid fset" where
  "linked_objs link_set obj i j \<equiv> (\<lambda>x. x!j) |`| ffilter (\<lambda>x. x!i = obj) link_set"
*)
(*
definition find_links :: "links \<Rightarrow> oid \<Rightarrow> links" where
  "find_links links obj \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup links assoc of Some link_set \<Rightarrow>
      obj |\<in>| fmran link_set) links"
*)
(*
definition find_links :: "links \<Rightarrow> oid \<Rightarrow> links" where
  "find_links links obj \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup links assoc of Some link_set \<Rightarrow>
      fBex (fmdom link_set) (\<lambda>role.
        case fmlookup link_set role of Some obj2 \<Rightarrow>
          obj = obj2)) links"
*)
(*
definition link_refer_obj :: "(role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> oid \<Rightarrow> bool" where
  "link_refer_obj link_set obj \<equiv>
    fBex (fmdom link_set) (\<lambda>role.
      fmlookup link_set role = Some obj)"

definition find_links :: "links \<Rightarrow> oid \<Rightarrow> links" where
  "find_links links obj \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup links assoc of None \<Rightarrow> False | Some link_set \<Rightarrow>
      link_refer_obj link_set obj) links"

definition find_links2 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_links2 links obj role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup links assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some obj2 \<Rightarrow>
        obj2 \<noteq> obj) (find_links links obj))"
*)
(*
definition find_link :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> assoc" where
  "find_link links obj role \<equiv> fthe_elem (find_links2 links obj role)"
*)
definition link_set_ok :: "objects \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) fset \<Rightarrow> bool" where
  "link_set_ok objects link_set \<equiv> fBall link_set (\<lambda>x. fmran x |\<subseteq>| fmdom objects)"

inductive data_is_ok :: "data \<Rightarrow> bool" where
  "(* Attribute values defined for existing objects *)
   fmdom attr_vals |\<subseteq>| fmdom objects \<Longrightarrow>
   (* Links defined for existing objects *)
   fBall (fmran links) (link_set_ok objects) \<Longrightarrow>
   data_is_ok (objects, attr_vals, links)"

code_pred [show_modes] data_is_ok .


(*
definition find_link :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> oid option" where
  "find_link links obj role \<equiv>
    fmlookup (fthe_elem (fmran (find_links5 links obj role))) role"
*)

definition objects1 :: "objects" where
  "objects1 \<equiv> fmap_of_list [
    (''Ivan'', ''Person''),
    (''Jhon'', ''Person''),
    (''Car1'', ''Car''),
    (''Car2'', ''Car''),
    (''Car3'', ''Car'')]"

definition attr_val1 :: "attr_vals" where
  "attr_val1 \<equiv> fmap_of_list [
    (''Ivan'', fmap_of_list [
      (''name'', StringVal (Just ''Ivan Ivanov''))]),
      (*(''name'', IntegerValue 1)]),*)
    (''Car1'', fmap_of_list [
      (''color'', StringVal (Just ''White''))])]"

definition links1 :: "links" where
  "links1 \<equiv> fmap_of_list [
    (''PersonCar'', {|
      fmap_of_list [
        (''driver'',''Jhon''),
        (''car'',''Car1'')],
      fmap_of_list [
        (''driver'',''Ivan''),
        (''car'',''Car1'')],
      fmap_of_list [
        (''driver'',''Ivan''),
        (''car'',''Car2'')]|}),
    (''Employment2'', {|
      fmap_of_list [
        (''employee'',''Jhon''),
        (''employer'',''Ivan'')],
      fmap_of_list [
        (''employee'',''Ivan''),
        (''employer'',''Ivan'')]|})]"

definition data1 :: "data" where
  "data1 \<equiv> (objects1, attr_val1, links1)"

definition link_refer_class5 :: "(role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> bool" where
  "link_refer_class5 link obj role \<equiv> fmlookup link role = Some obj"

definition link_refer_role5 :: "(role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> role \<Rightarrow> bool" where
  "link_refer_role5 link role \<equiv> fmlookup link role \<noteq> None"
(*
definition find_links5 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> links" where
  "find_links5 links obj role \<equiv>
    fmmap (\<lambda>link_set. ffilter (\<lambda>link.
      link_refer_role5 link role \<and> link_refer_class5 link obj role) link_set)
    (fmfilter (\<lambda>assoc.
      case fmlookup links assoc of None \<Rightarrow> False | Some link_set \<Rightarrow>
        fBex link_set (\<lambda>link.
          link_refer_role5 link role \<and> link_refer_class5 link obj role)) links)"
*)
definition remove_empty_links where
  "remove_empty_links links \<equiv> fmfilter (\<lambda>assoc.
      case fmlookup links assoc of None \<Rightarrow> False | Some link_set \<Rightarrow>
        link_set \<noteq> fempty) links"

definition find_links5 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> role \<Rightarrow> links" where
  "find_links5 links obj from to \<equiv>
    remove_empty_links
      (fmmap (\<lambda>link_set. ffilter (\<lambda>link.
        link_refer_class5 link obj from \<and> link_refer_role5 link to) link_set) links)"

value "find_assocs5 assocs1 ''Person'' ''driver'' ''car''"
value "find_links5 links1 ''Ivan'' ''driver'' ''car''"


(*** Model & Data ***********************************************************************)

definition attr_vals_is_ok2 where
  "attr_vals_is_ok2 cls_attrs vals \<equiv>
    fBall (fmdom cls_attrs |\<union>| fmdom vals) (\<lambda>prop.
      case (fmlookup cls_attrs prop, fmlookup vals prop)
        of (Some \<tau>, Some v) \<Rightarrow> \<forall>cls obj.
            type_of_val v = \<tau> \<and>
            v \<noteq> ObjectVal cls obj \<and>
            \<tau> \<noteq> ObjectType cls
         | (_, _) \<Rightarrow> False)"

definition attr_vals_is_ok where
  "attr_vals_is_ok attrs objects attr_vals \<equiv>
    fBall (fmdom objects) (\<lambda>obj.
      case (fmlookup objects obj) of Some cls \<Rightarrow>
        case (fmlookup attrs cls, fmlookup attr_vals obj)
          of (None, None) \<Rightarrow> True
           | (None, Some _) \<Rightarrow> False
           | (Some _, None) \<Rightarrow> False
           | (Some cls_attrs, Some vals) \<Rightarrow>
                attr_vals_is_ok2 cls_attrs vals)"
(*
definition link_ok :: "assoc_end list \<Rightarrow> link \<Rightarrow> objects \<Rightarrow> bool" where
  "link_ok ends link objects \<equiv> list_all2 (\<lambda>end obj.
    fmlookup objects obj = Some (assoc_end_class end)) ends link"

definition links_ok :: "assocs \<Rightarrow> links \<Rightarrow> objects \<Rightarrow> bool" where
  "links_ok assocs links objects \<equiv>
    fBall (fmdom links) (\<lambda>assoc.
      case (fmlookup links assoc) of Some link_set \<Rightarrow>
        case (fmlookup assocs assoc) of Some ends \<Rightarrow>
          fBall link_set (\<lambda>link.
            link_ok ends link objects))"
*)

definition link_obj_cls_ok :: "(oid \<rightharpoonup>\<^sub>f cls) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> bool" where
  "link_obj_cls_ok objects ends link \<equiv>
    fBall (fmdom ends |\<union>| fmdom link) (\<lambda>role.
      case (fmlookup ends role) of None \<Rightarrow> False | Some end \<Rightarrow>
        case (fmlookup link role) of None \<Rightarrow> False | Some obj \<Rightarrow>
          fmlookup objects obj = Some (assoc_end_class end))"
(*
definition link_obj_cls_ok :: "(oid \<rightharpoonup>\<^sub>f cls) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> bool" where
  "link_obj_cls_ok objects ends link \<equiv>
    fBall (fmdom ends |\<union>| fmdom link) (\<lambda>role.
      case (fmlookup ends role, fmlookup link role) of (Some end, Some obj) \<Rightarrow>
        fmlookup objects obj = Some (assoc_end_class end) | _ \<Rightarrow> False)"
*)
definition all_roles where
  "all_roles assocs \<equiv> ffUnion (fmran (fmmap fmdom assocs))"
(*
definition links_unique where
  "links_unique objects assocs links \<equiv>
    fBall (all_roles assocs) (\<lambda>role.
      fBall (fmdom objects) (\<lambda>obj.
        case (fmlookup objects obj) of None \<Rightarrow> False | Some cls \<Rightarrow>
          fcard (fmdom (find_assocs5 assocs cls role)) \<le> 1 \<and>
          fcard (fmdom (find_links5 links obj role)) \<le> 1
          (*is_singleton (fset (fmdom (find_assocs5 assocs cls role))) \<and>
          is_singleton (fset (fmdom (find_links5 links obj role)))*) ))"
*)
(* TODO: Check cardinality *)
definition links_ok :: "objects \<Rightarrow> assocs \<Rightarrow> links \<Rightarrow> bool" where
  "links_ok objects assocs links \<equiv>
    (*links_unique objects assocs links \<and>*)
    fBall (fmdom links) (\<lambda>assoc.
      case (fmlookup assocs assoc) of None \<Rightarrow> False | Some ends \<Rightarrow>
        case (fmlookup links assoc) of None \<Rightarrow> False | Some link_set \<Rightarrow> (* It can't be None *)
          fBall link_set (link_obj_cls_ok objects ends))"

value assocs1
value "find_assocs5 assocs1 ''Person'' ''employee''"
value "find_assocs5 assocs1 ''Person'' ''driver''"
value "links_ok objects1 assocs1 links1"
(*
definition assoc_refer_class7 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> nat" where
  "assoc_refer_class7 ends cls \<equiv>
    fcard (ffilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end) (fmdom ends))"
*)
(*
definition find_assocs7 :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs7 assocs cls \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        fBex (fmdom ends) (\<lambda>role.
          case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
            cls = assoc_end_class end \<and> assoc_refer_class5 ends cls role)) assocs"
*)
(*
term fmmap
definition find_assocs7 :: "assocs \<Rightarrow> cls \<Rightarrow> role list" where
  "find_assocs7 assocs cls \<equiv>
    fmmap (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> fempty | Some ends \<Rightarrow>
        case assoc_refer_class7 ends cls
          of 0 \<Rightarrow> fempty) assocs"
*)
value "find_assocs7 assocs1 ''Person''"

(*
lemma link_refer_obj_then_class:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   link_refer_obj link_set obj \<Longrightarrow>
   assoc_refer_class ends cls"
  apply (simp add: link_obj_cls_ok_def link_refer_obj_def assoc_refer_class_def)
  by (smt fBall_alt_def fBall_funion fBexCI fBexE fmdom_notD option.case_eq_if option.sel)
*)
lemma links_ok_preserv_class:
  "links_ok objects assocs links \<Longrightarrow>

   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = cls \<Longrightarrow>

   fmlookup links assoc = Some link_set \<Longrightarrow>
   link |\<in>| link_set \<Longrightarrow>
   fmlookup link role = Some obj \<Longrightarrow>
   fmlookup objects obj = Some cls2 \<Longrightarrow>

   cls = cls2"
  apply (simp add: links_ok_def)
  apply (smt fBall_alt_def fBall_funion fmdomI link_obj_cls_ok_def option.inject option.simps(5))
  done
(*
lemma links_ok_and_find_links_then_find_assocs:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmdom (find_links links obj) = assocs1 \<Longrightarrow>
   fmdom (find_assocs assocs cls) = assocs2 \<Longrightarrow>
   assocs1 |\<subseteq>| assocs2"
  apply (simp add: links_ok_def)
  apply (simp add: find_assocs_def find_links_def)
  apply (auto)
  apply (metis (no_types, lifting) fbspec fmdom_notD option.case_eq_if)
  apply (smt fBall_alt_def link_refer_obj_then_class option.case_eq_if)
  done
*)
(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   f = (\<lambda>assoc.
      case fmlookup links assoc of None \<Rightarrow> False
         | Some ends \<Rightarrow>
             case fmlookup ends role of None \<Rightarrow> False | Some obj2 \<Rightarrow> obj2 \<noteq> obj) \<Longrightarrow>
   g = (\<lambda>assoc.
         case fmlookup assocs assoc of None \<Rightarrow> False
         | Some ends \<Rightarrow>
             case fmlookup ends role of None \<Rightarrow> False
             | Some end \<Rightarrow> assoc_end_class end \<noteq> cls) \<Longrightarrow>
   f assoc \<Longrightarrow> g assoc"
*)
lemma q11:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   role |\<in>| (fmdom ends |\<union>| fmdom link_set) \<Longrightarrow>
   case fmlookup link_set role of None \<Rightarrow> False | Some obj2 \<Rightarrow> obj2 = obj \<Longrightarrow>
   case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> assoc_end_class end = cls"
  apply (simp add: link_obj_cls_ok_def)
  apply (smt fbspec funionCI option.case_eq_if option.sel)
  done

thm fbspec funionCI option.case_eq_if option.sel

lemma q12:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   (case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> assoc_end_class end \<noteq> cls) \<Longrightarrow>
   (case fmlookup link_set role of None \<Rightarrow> False | Some obj2 \<Rightarrow> obj2 \<noteq> obj)"
  apply (simp add: link_obj_cls_ok_def)
  apply (smt fBall_funion fbspec fmdom_notD option.case_eq_if option.inject)
  done
(*
lemma q:
  "ffilter P s1 = fs1 \<Longrightarrow>
   ffilter Q s2 = fs2 \<Longrightarrow>
   s1 |\<subseteq>| s2 \<Longrightarrow>
   (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow>
   fs1 |\<subseteq>| fs2"
  apply auto
  done
*)
(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   find_link links obj role = assoc1 \<Longrightarrow>
   find_assoc assocs cls role = assoc2 \<Longrightarrow>
   assoc1 = assoc2"
  apply (simp add: find_link_def find_assoc_def)
  apply (simp add: find_links2_def find_assocs2_def)
*)

lemma w13:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   link_refer_role5 link_set role \<Longrightarrow>
   assoc_refer_role5 ends role"
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: link_refer_role5_def)
  apply (simp add: assoc_refer_role5_def)
  by (metis (no_types, lifting) case_optionE fBall_alt_def fmdomI funion_iff prod_cases3)

lemma w14:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   link_refer_class5 link_set obj role \<Longrightarrow>
   assoc_refer_class5 ends cls role"
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: link_refer_class5_def)
  apply (simp add: assoc_refer_class5_def)
  apply (auto simp add: fBall_alt_def)
  by (smt case_optionE fBexI fBex_cong fBex_triv_one_point1 fmlookup_restrict_fset fmrestrict_fset_dom option.sel option.simps(4) option.simps(5))

lemma w12:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmdom (find_links5 links obj from to) |\<subseteq>| fmdom (find_assocs5 assocs cls from to)"
  apply (simp add: links_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)
  apply (auto simp add: remove_empty_links_def)
  apply (metis (no_types, lifting) case_optionE fbspec fmdomI)
  apply (smt comp_def eq_ffilter fBall_alt_def fempty_ffilter option.case_eq_if w13 w14)
  (*apply (metis (no_types, lifting) fbspec fmdomI option.case_eq_if option.collapse)
  apply (erule case_optionE; simp add: fBall_alt_def)
  apply (smt fBall_alt_def fBexE option.case_eq_if option.simps(5) w13 w14)*)
  done

(*
lemma q:
  "m1 |\<subseteq>| m2 \<Longrightarrow>
   fcard m1 \<le> 1 \<Longrightarrow>
   fcard m2 = 1 \<Longrightarrow>
   fthe_elem m1 = fthe_elem m2"

lemma w121:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fcard (fmdom (find_assocs5 assocs cls role)) \<le>
   fcard (fmdom (find_links5 links obj role))"
  apply (simp add: links_ok_def)
  apply (auto simp add: links_unique_def)
  apply (simp add: find_links5_def find_assocs5_def)
*)
(*
lemma w12:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmdom (find_links5 links obj role) = assoc1 \<Longrightarrow>
   fmdom (find_assocs5 assocs cls role) = assoc2 \<Longrightarrow>
   assoc1 = assoc2"
  apply (simp add: links_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)
  apply auto
  apply (metis (no_types, lifting) fbspec fmdomI funion_iff option.case_eq_if option.collapse)
  apply (erule case_optionE; simp add: fBall_alt_def)
  apply (smt fBall_alt_def fBexE option.case_eq_if option.simps(5) w13 w14)
  apply (metis (no_types, lifting) case_optionE fBall_funion fbspec fmlookup_dom_iff)
  apply (erule case_optionE; simp add: fBall_alt_def)
*)
lemma w15:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   fmlookup link_set role = Some obj2 \<Longrightarrow>
   fmlookup objects obj2 = Some (assoc_end_class end)"
  apply (simp add: link_obj_cls_ok_def)
  by (smt fBall_funion fbspec fmdomI option.case_eq_if option.sel)
(*
lemma w31:
  "links_ok objects assocs links \<Longrightarrow>
   fcard (fdom (find_assocs5 assocs cls role)) \<le> 1"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: find_assocs5_def)

lemma w17:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   ends |\<in>| fmran (find_assocs5 assocs cls role) \<Longrightarrow>
   link_set |\<in>| fmran (find_links5 links obj role) \<Longrightarrow>
   link_obj_cls_ok objects ends link_set"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply auto

lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls role))) = Some ends \<Longrightarrow>
   fmlookup links (fthe_elem (fmdom (find_links5 links obj role))) = Some link_set \<Longrightarrow>
   link_obj_cls_ok objects ends link_set"
*)
(*
definition link_obj_cls_ok :: "(oid \<rightharpoonup>\<^sub>f cls) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> bool" where
  "link_obj_cls_ok objects ends link_set \<equiv>
    fBall (fmdom ends |\<union>| fmdom link_set) (\<lambda>role.
      case (fmlookup ends role) of None \<Rightarrow> False | Some end \<Rightarrow>
        case (fmlookup link_set role) of None \<Rightarrow> False | Some obj \<Rightarrow>
          fmlookup objects obj = Some (assoc_end_class end))"
*)
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc assocs cls role \<equiv>
    fmlookup (fthe_elem (fmran (find_assocs5 assocs cls role))) role"
*)

definition find_assoc2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc2 assocs cls from to \<equiv>
    if fcard (fmdom (find_assocs5 assocs cls from to)) = 1 then
      case fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls from to)))
        of None \<Rightarrow> None
         | Some ends \<Rightarrow> fmlookup ends to else None"

definition find_link2 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> role \<Rightarrow> oid fset option" where
  "find_link2 links obj from to \<equiv>
    if fcard (fmdom (find_links5 links obj from to)) = 1 then
      case fmlookup (find_links5 links obj from to)
                    (fthe_elem (fmdom (find_links5 links obj from to)))
        of None \<Rightarrow> None
         | Some link_set \<Rightarrow> Some ((\<lambda>link. the (fmlookup link to)) |`| link_set) else None"

value links1
value "find_links5 links1 ''Ivan'' ''driver'' ''car''"
value "find_link2 links1 ''Ivan'' ''driver'' ''car''"

(*
definition find_assoc2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc2 assocs cls role \<equiv>
    case fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls role)))
      of None \<Rightarrow> None
       | Some ends \<Rightarrow> fmlookup ends role"

definition find_link2 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> oid fset" where
  "find_link2 links obj role \<equiv>
    case fmlookup links (fthe_elem (fmdom (find_links5 links obj role)))
      of None \<Rightarrow> fempty
       | Some link_set \<Rightarrow> (\<lambda>link. the (fmlookup link role)) |`| link_set"
*)


value "the_elem {1::nat}"
value "fthe_elem {|1::nat|}"
value "fthe_elem {|1::nat,2|}"

lemma w20:
  "fmdom m1 |\<subseteq>| fmdom m2 \<Longrightarrow>
   fmlookup m1 x \<noteq> None \<Longrightarrow>
   fmlookup m2 x \<noteq> None"
  by (meson fmdom_notD fmdom_notI fset_mp)

lemma w21:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup (find_links5 links obj from to) assoc \<noteq> None \<Longrightarrow>
   fmlookup (find_assocs5 assocs cls from to) assoc \<noteq> None"
  using w12 w20 apply auto
  by (meson fmlookup_dom_iff fset_mp)

lemma fmsubset_dom:
  "f \<subseteq>\<^sub>f g \<Longrightarrow>
   fmdom f |\<subseteq>| fmdom g"
  apply (auto simp add: fmsubset_def map_le_def)
  by (metis domI fmlookup_dom_iff)
(*
lemma q:
  "fBall link_set (link_obj_cls_ok objects ends) \<Longrightarrow>
   link_set2 |\<subseteq>| link_set \<Longrightarrow>
   fBall link_set2 (link_obj_cls_ok objects ends)"
  by blast

lemma q:
  "ends2 \<subseteq>\<^sub>f ends \<Longrightarrow>
   fmdom ends2 |\<subseteq>| fmdom ends"
  by (simp add: fmsubset_dom)
*)
lemma fBall_subset_un:
  "fBall (fmdom ends |\<union>| fmdom link) P \<Longrightarrow>
   fmdom ends2 |\<subseteq>| fmdom ends \<Longrightarrow>
   fBall (fmdom ends2 |\<union>| fmdom link) P"
  by auto

lemma w191:
  "links_ok objects assocs links \<Longrightarrow>
   assocs2 \<subseteq>\<^sub>f assocs \<Longrightarrow>
   fmdom links2 |\<subseteq>| fmdom links \<Longrightarrow>

   (\<forall>assoc. \<exists>link_set2 link_set.
      assoc |\<in>| fmdom links2 \<longrightarrow>
      fmlookup links2 assoc = Some link_set2 \<and>
      fmlookup links assoc = Some link_set \<and>
      link_set2 |\<subseteq>| link_set) \<Longrightarrow>
(*
   assoc |\<in>| fmdom links2 \<Longrightarrow>
   fmlookup links2 assoc = Some link_set2 \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   link_set2 |\<subseteq>| link_set \<Longrightarrow>
*)
   fmdom links2 |\<subseteq>| fmdom assocs2 \<Longrightarrow>
   links_ok objects assocs2 links2"
  apply (frule_tac f="assocs2" in fmsubset_dom)
  apply (simp add: links_ok_def)
  apply (simp add: fmsubset_def map_le_def)
  apply auto
  apply (frule_tac x="x" and A="fmdom links2" and B="fmdom links" in fset_mp)
  apply assumption
  apply (simp add: option.case_eq_if)
  apply auto
  apply (meson fmlookup_dom_iff fset_rev_mp)
  apply (smt domI fbspec fset_rev_mp option.case_eq_if option.sel)
  done


(*
lemma w191:
  "links_ok objects assocs links \<Longrightarrow>
   assocs2 \<subseteq>\<^sub>f assocs \<Longrightarrow>
   links2 \<subseteq>\<^sub>f links \<Longrightarrow>
   fmdom links2 |\<subseteq>| fmdom assocs2 \<Longrightarrow>
   links_ok objects assocs2 links2"
  apply (frule_tac f="assocs2" in fmsubset_dom)
  apply (frule_tac f="links2" in fmsubset_dom)
  apply (simp add: links_ok_def)
  apply (simp add: fmsubset_def map_le_def)
  apply (simp add: fBall_alt_def)
  apply auto
  apply (frule fset_mp)
  apply assumption
  apply (metis (no_types, lifting) domI fmlookup_dom_iff fset_rev_mp option.case_eq_if)
  done
*)
lemma w194:
  "links_ok objects assocs links \<Longrightarrow>
   find_assocs5 assocs cls from to \<subseteq>\<^sub>f assocs"
  by (simp add: find_assocs5_def fmpredI fmpred_filter fmsubset_alt_def)

lemma w1951:
  "links_ok objects assocs links \<Longrightarrow>
   fmdom (find_links5 links obj from to) |\<subseteq>| fmdom links"
  apply (simp add: find_links5_def remove_empty_links_def)
  by fastforce

lemma w1952:
  "links_ok objects assocs links \<Longrightarrow>
   links2 = find_links5 links obj from to \<Longrightarrow>
   assoc |\<in>| fmdom links2 \<Longrightarrow>
   fmlookup links2 assoc = Some link_set2 \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   link_set2 |\<subseteq>| link_set"
  apply (auto simp add: find_links5_def remove_empty_links_def)
  done

lemma w1953:
  "links_ok objects assocs links \<Longrightarrow>
   links2 = find_links5 links obj from to \<Longrightarrow>
   (\<forall>assoc. \<exists>link_set2 link_set.
      assoc |\<in>| fmdom links2 \<longrightarrow>
      fmlookup links2 assoc = Some link_set2 \<and>
      fmlookup links assoc = Some link_set \<and>
      link_set2 |\<subseteq>| link_set)"
  by (meson fmlookup_dom_iff fset_mp w1951 w1952)

lemma w195:
  "links_ok objects assocs links \<Longrightarrow>
   fmdom (find_links5 links obj from to) |\<subseteq>| fmdom links \<and>
   (\<forall>assoc. \<exists>link_set2 link_set.
      assoc |\<in>| fmdom (find_links5 links obj from to) \<longrightarrow>
      fmlookup (find_links5 links obj from to) assoc = Some link_set2 \<and>
      fmlookup (find_links5 links obj from to) assoc = Some link_set \<and>
      link_set2 |\<subseteq>| link_set)"
  by (meson order_refl w1951 w1953)

(*
lemma w195:
  "links_ok objects assocs links \<Longrightarrow>
   find_links5 links obj role \<subseteq>\<^sub>f links"
  by (simp add: find_links5_def fmpredI fmpred_filter fmsubset_alt_def)
*)
thm w12
lemma w19:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   assocs2 = find_assocs5 assocs cls from to \<Longrightarrow>
   links2 = find_links5 links obj from to \<Longrightarrow>
   links_ok objects assocs2 links2"
  apply (frule_tac obj=obj and cls=cls and ?from="from" and ?to="to" in w12)
  apply assumption
  apply (frule_tac cls=cls and ?from="from" and ?to="to" in w194)
  apply (frule_tac obj=obj and ?from="from" and ?to="to" in w195)
  using w191 w1953 by auto
(*  using w191 by blast*)
(*
term is_singleton

lemma w22:
  "links_ok objects assocs links \<Longrightarrow>
   fcard (fmran assocs) = 1 \<Longrightarrow>
   fcard (fmran links) = 1 \<Longrightarrow>
   link_obj_cls_ok objects
      (fthe_elem (fmran assocs))
      (fthe_elem (fmran links))"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)

lemma q:
  "s1 \<subseteq> s2 \<Longrightarrow>
   is_singleton s1 \<Longrightarrow>
   is_singleton s2 \<Longrightarrow>
   the_elem s1 = e1 \<Longrightarrow>
   the_elem s2 = e2 \<Longrightarrow>
   e1 = e2"
  by (metis insert_subset is_singleton_the_elem singletonD)

lemma q:
  "s1 |\<subseteq>| s2 \<Longrightarrow>
   fthe_elem s1 = e1 \<Longrightarrow>
   fthe_elem s2 = e2 \<Longrightarrow>
   e1 = e2"

lemma w61:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   assocs11 = fmdom (find_links5 links obj role) \<Longrightarrow>
   assocs2 = fmdom (find_assocs5 assocs cls role) \<Longrightarrow>
   assoc1 = fthe_elem assocs11 \<Longrightarrow>
   assoc2 = fthe_elem assocs2 \<Longrightarrow>
   assoc1 = assoc2"
  using w12 apply auto
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)

lemma w16:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   link_obj_cls_ok objects
      (fthe_elem (fmran (find_assocs5 assocs cls role)))
      (fthe_elem (fmran (find_links5 links obj role)))"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)
  apply auto
*)
lemma w41:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   fBall link_set (link_obj_cls_ok objects ends)"
  apply (simp add: links_ok_def)
  by (metis (no_types, lifting) fbspec fmdomI option.case_eq_if option.sel)

lemma w42:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   fmlookup link_set role = Some obj \<Longrightarrow>
   fmlookup objects obj = Some (assoc_end_class end)"
  apply (simp add: link_obj_cls_ok_def)
  by (smt fBall_alt_def fmdomI funion_iff option.case_eq_if option.sel)

lemma w43:
  "links_ok objects assocs links \<Longrightarrow>

   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links assoc = Some link_set \<Longrightarrow>

   fBall link_set (\<lambda>link.
    case fmlookup link role of None \<Rightarrow> False | Some obj \<Rightarrow>
      fmlookup objects obj = Some (assoc_end_class end))"
  apply (frule w41)
  apply (assumption)
  apply (assumption)
  apply (simp add: fBall_alt_def link_obj_cls_ok_def)
  using fmdomI by fastforce

lemma w44:
  "links_ok objects assocs links \<Longrightarrow>

   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links assoc = Some link_set \<Longrightarrow>
   objs = (\<lambda>link. the (fmlookup link role)) |`| link_set \<Longrightarrow>

   fBall objs (\<lambda>obj. fmlookup objects obj = Some (assoc_end_class end))"
  by (smt fBallI fbspec fimageE option.case_eq_if w43)

lemma assocs_eq:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   fcard (fmdom (find_assocs5 assocs cls from to)) = 1 \<Longrightarrow>
   fcard (fmdom (find_links5 links obj from to)) = 1 \<Longrightarrow>

   (fthe_elem (fmdom (find_assocs5 assocs cls from to))) =
   (fthe_elem (fmdom (find_links5 links obj from to)))"
  by (metis fcard_seteq le_numeral_extra(4) w12)
(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   fcard (fmdom (find_assocs5 assocs cls role)) = 1 \<Longrightarrow>
   fcard (fmdom (find_links5 links obj role)) = 1 \<Longrightarrow>

   (fthe_elem (fmdom (find_assocs5 assocs cls role))) =
   (fthe_elem (fmdom (find_links5 links obj role))) \<Longrightarrow>

   fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls role))) = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links (fthe_elem (fmdom (find_links5 links obj role))) = Some link_set \<Longrightarrow>
   objs = (\<lambda>link. the (fmlookup link role)) |`| link_set \<Longrightarrow>

   fBall objs (\<lambda>obj. fmlookup objects obj = Some (assoc_end_class end))"
  using w44 apply auto
*)
lemma find_assoc2_rev:
  "find_assoc2 assocs cls from to = Some end \<Longrightarrow>
   \<exists>ends.
     fcard (fmdom (find_assocs5 assocs cls from to)) = 1 \<and>
     fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls from to))) = Some ends \<and>
     fmlookup ends to = Some end"
  apply (simp add: find_assoc2_def)
  by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.exhaust_sel)

lemma find_link2_rev:
  "find_link2 links obj from to = Some objs \<Longrightarrow>
(*   objs \<noteq> fempty \<Longrightarrow>*)
   \<exists>link_set.
     fcard (fmdom (find_links5 links obj from to)) = 1 \<and>
     fmlookup (find_links5 links obj from to)
              (fthe_elem (fmdom (find_links5 links obj from to))) = Some link_set \<and>
     objs = (\<lambda>link. the (fmlookup link to)) |`| link_set"
  apply (simp add: find_link2_def)
  by (smt option.case_eq_if option.collapse option.distinct(1) option.inject)
(*  by (metis (mono_tags, lifting) option.case_eq_if option.collapse)*)
(*
lemma q:
  "fmlookup (f::assocs) (fthe_elem a) = Some x \<Longrightarrow>
   \<exists>q. a = {|q|}"
  apply (simp add: fthe_elem_def the_elem_def)

term fset
lemma q:
  "fthe_elem m1 |\<in>| fmdom assocs \<Longrightarrow>
   is_singleton (fset m1) \<Longrightarrow>
   \<exists>q. m1 = {|q|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inject is_singletonE)

lemma q:
  "m1 |\<subseteq>| m2 \<Longrightarrow>
   fcard m2 \<le> fcard m1 \<Longrightarrow>
   fthe_elem m1 = fthe_elem m2"
  using fcard_seteq apply fastforce

lemma q:
  "m1 |\<subseteq>| m2 \<Longrightarrow>
   is_singleton (fset m1) \<Longrightarrow>
   is_singleton (fset m2) \<Longrightarrow>
   fthe_elem m1 = fthe_elem m2"
  by (metis empty_iff fthe_elem.rep_eq insert_iff insert_subset is_singleton_the_elem less_eq_fset.rep_eq)

lemma q:
  "is_singleton (fset (fmdom (find_assocs5 assocs cls role)))"
  apply (simp add: find_assocs5_def)
  apply (auto)
*)

lemma w18:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   find_assoc2 assocs cls from to = Some end \<Longrightarrow>
   find_link2 links obj from to = Some objs \<Longrightarrow>
   fBall objs (\<lambda>obj. fmlookup objects obj = Some (assoc_end_class end))"
  apply (drule find_assoc2_rev)
  apply (erule exE)
  apply (erule conjE)
  apply (cases "objs = fempty")
  apply auto[1]
  apply (drule find_link2_rev)
  (*apply auto[1]
  apply (erule exE)
  apply (erule conjE)*)
  apply (frule assocs_eq)
  apply (assumption)
  apply (assumption)
  apply auto[1]
  (*by (smt fBallI fBall_alt_def fimageE fimage_cong fimage_eqI fmdomI fset_rev_mp option.sel w1953 w44)*)
  using w44 apply auto
  by (smt fBall_funion fbspec fmdomI fsubset_funion_eq option.collapse option.sel option.simps(4) w1953 w41 w42 w43)
(*  by (smt fBall_alt_def fBall_funion fmdomI fsubset_funion_eq option.collapse option.sel option.simps(4) w15 w1953 w41 w43)*)

(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   (*fmlookup objects obj = Some cls \<Longrightarrow>*)

   fmlookup assocs (find_assoc assocs cls role) = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links (find_link links obj role) = Some link_set \<Longrightarrow>
   fmlookup link_set role = Some obj2 \<Longrightarrow>
   fmlookup objects obj2 = Some cls2a \<Longrightarrow>

   cls2a = assoc_end_class end"
  apply (simp add: links_ok_def)
  apply (simp add: find_assoc_def find_assocs2_def)
  apply (simp add: find_link_def find_links2_def)
*)
(*
TODO: Количество связей правильное
*)
inductive conforms_to_model :: "model \<Rightarrow> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "model_is_ok model \<Longrightarrow>
   data_is_ok data \<Longrightarrow>
   model = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   (* Objects belong to existing classes *)
   fmran objects |\<subseteq>| classes \<Longrightarrow>
   (* Attribute values defined for existing attributes and have right types *)
   attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   (* Links defined for existing associations, have right objects and cardinality *)
   links_ok objects assocs links \<Longrightarrow>
   model \<turnstile> data"

lemma attr_vals_is_ok_then:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   attr_vals_is_ok2 cls_attrs vals"
  apply (simp add: attr_vals_is_ok_def)
  by (metis (no_types, lifting) case_prodD fBall_alt_def fmlookup_dom_iff option.simps(5))

lemma attr_vals_is_ok_then2:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  apply (simp add: attr_vals_is_ok2_def)
  by (smt fBall_funion fbspec fmdomI option.simps(5))

lemma attr_vals_is_ok_then_rev:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   \<exists>cls_attrs vals.
      fmlookup attrs cls = None \<and>
      fmlookup attr_vals obj = None \<or>
      fmlookup attrs cls = Some cls_attrs \<and>
      fmlookup attr_vals obj = Some vals"
  apply (simp add: attr_vals_is_ok_def)
  by (smt case_prod_conv fbspec fmdom_notD not_None_eq option.case_eq_if option.sel)

lemma attr_vals_is_ok_then_rev2:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
    (\<exists>cls_attrs. fmlookup attrs cls = Some cls_attrs) \<longleftrightarrow>
    (\<exists>vals. fmlookup attr_vals obj = Some vals)"
  apply (simp add: attr_vals_is_ok_def)
  by (smt case_prod_conv fbspec fmdom_notD not_None_eq option.case_eq_if option.sel)

lemma attr_vals_is_ok_then2_rev:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<or>
   fmlookup vals prop = Some v \<Longrightarrow>
   \<exists>\<tau> v.
    fmlookup cls_attrs prop = Some \<tau> \<and>
    fmlookup vals prop = Some v \<and>
    type_of_val v = \<tau>"
  apply (simp add: attr_vals_is_ok2_def)
  by (smt fBall_funion fbspec fmdom_notD fmlookup_dom_iff option.case_eq_if option.sel)

lemma model_preserv_type:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  by (meson attr_vals_is_ok_then attr_vals_is_ok_then2)

code_pred [show_modes] conforms_to_model .

(*** Environment Typing *****************************************************************)
(*
type_synonym 'a fenv = "vname \<rightharpoonup>\<^sub>f 'a"

definition fetyping :: "type fenv \<Rightarrow> val fenv \<Rightarrow> bool" (infix "\<turnstile>\<^sub>f" 50) where
  "\<Gamma> \<turnstile>\<^sub>f env \<equiv> fBall (fmdom \<Gamma> |\<union>| fmdom env) (\<lambda>x.
    case (fmlookup \<Gamma> x, fmlookup env x)
      of (Some \<tau>, Some v) \<Rightarrow> type_of_val v = \<tau>
       | (_, _) \<Rightarrow> False)"
*)
definition etyping :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> env \<equiv> \<forall>x.
    case (\<Gamma> x, env x)
      of (Some \<tau>, Some v) \<Rightarrow> type_of_val v = \<tau>
       | (_, _) \<Rightarrow> False"

lemma var_has_type_impies_has_value:
  "\<Gamma> var = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>v. env var = Some v"
  by (smt etyping_def old.prod.case option.case_eq_if option.collapse option.distinct(1))

lemma var_has_value_impies_has_type:
  "env var = Some v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>\<tau>. \<Gamma> var = Some \<tau>"
  by (smt etyping_def old.prod.case option.case_eq_if option.distinct(1) option.expand option.sel)

lemma etyping_preserv_type:
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   \<Gamma> var = Some \<tau> \<Longrightarrow>
   env var = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  apply (simp add: etyping_def)
  by (smt option.case_eq_if option.sel prod.simps(2))

(*value "[''x''\<mapsto>IntegerType] \<turnstile> [''x''\<mapsto>IntegerVal (Just 1)]"*)
(*
definition object_type_is_ok :: "model \<Rightarrow> type \<Rightarrow> bool" where
  "object_type_is_ok \<M> \<tau> \<equiv>
    \<forall>cls. \<tau> = ObjectType cls \<longrightarrow> cls |\<in>| (fst \<M>)"

definition tenv_classes_ok :: "type env \<Rightarrow> model \<Rightarrow> bool" where
  "tenv_classes_ok \<Gamma> \<M> \<equiv> \<forall>x \<tau>.
    \<Gamma> x = Some \<tau> \<longrightarrow> object_type_is_ok \<M> \<tau>"

definition object_val_is_ok :: "data \<Rightarrow> val \<Rightarrow> bool" where
  "object_val_is_ok data v \<equiv>
    \<forall>cls obj. v = ObjectVal cls obj \<longrightarrow> obj |\<in>| fmdom (fst data)"

definition env_objects_ok :: "val env \<Rightarrow> data \<Rightarrow> bool" where
  "env_objects_ok env data \<equiv> \<forall>x v.
    env x = Some v \<longrightarrow> object_val_is_ok data v"
*)

definition object_val_ok :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok \<tau> v objects \<equiv> \<forall>cls cls2 obj.
    \<tau> = ObjectType cls \<and>
    v = ObjectVal cls2 obj \<longrightarrow>
    fmlookup objects obj = Some cls"

definition object_val_ok_impl :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok_impl \<tau> v objects \<equiv>
    case (\<tau>, v)
      of (ObjectType cls, ObjectVal cls2 obj) \<Rightarrow>
           fmlookup objects obj = Some cls
       | (_, _) \<Rightarrow> True"

lemma object_val_ok_eq [code]:
  "object_val_ok \<tau> v objects = object_val_ok_impl \<tau> v objects"
  apply (simp only: object_val_ok_def object_val_ok_impl_def)
  apply (cases \<tau>; simp)
  apply (cases v; simp)
  done
(*
lemma object_val_ok_true:
  "\<forall>cls cls2 obj.
    \<tau> \<noteq> ObjectType cls \<and>
    v \<noteq> ObjectVal cls2 obj \<Longrightarrow> object_val_ok \<tau> v objects"
  by (simp add: object_val_ok_def)
*)
definition object_vals_ok :: "type env \<Rightarrow> val env \<Rightarrow> objects \<Rightarrow> bool" where
  "object_vals_ok \<Gamma> env objects \<equiv> \<forall>x.
    case (\<Gamma> x, env x) of (Some \<tau>, Some v) \<Rightarrow> object_val_ok \<tau> v objects"
(*
definition object_vals_ok :: "type env \<Rightarrow> val env \<Rightarrow> objects \<Rightarrow> bool" where
  "object_vals_ok \<Gamma> env objects \<equiv> \<forall>x. \<exists>cls obj.
    \<Gamma> x = Some (ObjectType cls) \<and>
    env x = Some (ObjectVal cls obj) \<longrightarrow>
    fmlookup objects obj = Some cls"
*)
inductive etyping2 :: "type env \<times> model \<Rightarrow> val env \<times> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   \<M> \<turnstile> data \<Longrightarrow>
   (*\<M> = (classes, attrs, assocs) \<Longrightarrow>*)
   data = (objects, attr_vals, links) \<Longrightarrow>
   object_vals_ok \<Gamma> env objects \<Longrightarrow>
   (*tenv_classes_ok \<Gamma> \<M> \<Longrightarrow>
   env_objects_ok env data \<Longrightarrow>*)
   (\<Gamma>,\<M>) \<turnstile> (env,data)"

code_pred [show_modes] etyping2 .
(*
definition etyping2 :: "type env \<times> model \<Rightarrow> val env \<times> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "etyping2 \<Gamma>_\<M> env_data \<equiv>
    case (\<Gamma>_\<M>, env_data)
      of ((\<Gamma>, (classes, attrs, assocs)), (env, (objects, attr_vals, links))) \<Rightarrow>
          \<Gamma> \<turnstile> env \<and>
          (classes, attrs, assocs) \<turnstile> (objects, attr_vals, links) \<and>
          tenv_classes_ok \<Gamma> (classes, attrs, assocs) \<and>
          env_objects_ok env (objects, attr_vals, links)"
*)
lemma etyping2_preserv_type:
  "(\<Gamma>,\<M>) \<turnstile> (env,data) \<Longrightarrow>
   \<Gamma> var = Some \<tau> \<Longrightarrow>
   env var = Some v \<Longrightarrow>
   \<T> v = \<tau>"
  using etyping2.simps etyping_preserv_type by blast

lemma etyping_preserv_type2:
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   \<T> v = \<tau> \<Longrightarrow>
   \<Gamma>(var\<mapsto>\<tau>) \<turnstile> env(var\<mapsto>v)"
  by (smt etyping_def fun_upd_apply old.prod.case option.case_eq_if option.sel option.simps(3))

(*
    \<Gamma> x = Some (ObjectType cls) \<longrightarrow> cls |\<in>| (fst \<M>)"

definition env_objects_ok :: "val env \<Rightarrow> data \<Rightarrow> bool" where
  "env_objects_ok env data \<equiv> \<forall>x. \<exists>cls obj.
    env x = Some (ObjectVal cls obj) \<longrightarrow> obj |\<in>| fmdom (fst data)"
*)
lemma object_vals_ok_ext:
  "object_vals_ok \<Gamma> env objects \<Longrightarrow>
   object_val_ok \<tau> v objects \<Longrightarrow>
   object_vals_ok (\<Gamma>(var \<mapsto> \<tau>)) (env(var \<mapsto> v)) objects"
  by (simp add: object_val_ok_def object_vals_ok_def)

lemma etyping2_preserv_type2:
  "(\<Gamma>,\<M>) \<turnstile> (env,data) \<Longrightarrow>
   \<T> v = \<tau> \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   object_val_ok \<tau> v objects \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>),\<M>) \<turnstile> (env(var\<mapsto>v),data)"
  by (simp add: etyping2.simps etyping_preserv_type2 object_vals_ok_ext)
(*  using env_objects_ok_def etyping_preserv_type2 tenv_classes_ok_def by auto*)
(*  by (smt etyping2.intros etyping2.simps etyping_def fst_conv fun_upd_apply old.prod.case option.case_eq_if option.sel option.simps(3) snd_conv)*)
(*
lemma q:
  "(\<forall>x cls obj. env x = Some (ObjectVal cls obj) \<longrightarrow> P) \<Longrightarrow>
   env x = Some (ObjectVal cls obj) \<Longrightarrow> P"
  by auto

lemma q:
  "(\<forall>x. \<exists>v. env x = Some v \<longrightarrow>
       (\<exists>cls obj.
           v = ObjectVal cls obj \<longrightarrow>
           P)) \<Longrightarrow>
   env x = Some (ObjectVal cls obj) \<Longrightarrow> P"
  apply (erule allE)
  apply (erule exE)
  apply (erule impE)
*)
lemma etyping2_preserv_class1:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   \<M> \<turnstile> data \<Longrightarrow>
   obj |\<in>| fmdom objects \<Longrightarrow>
   \<exists>cls. fmlookup objects obj = Some cls"
  apply (simp add: conforms_to_model.simps)
  by (simp add: fmlookup_dom_iff)

(*
definition object_val_ok :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok \<tau> v objects \<equiv> \<exists>cls obj.
    \<tau> = ObjectType cls \<and>
    v = ObjectVal cls obj \<longrightarrow>
    fmlookup objects obj = Some cls"
*)
(*
lemma q:
  "\<tau> = ObjectType cls \<Longrightarrow>
   v = ObjectVal cls obj \<Longrightarrow>
   object_val_ok \<tau> v objects \<Longrightarrow>
   fmlookup objects obj = Some cls"
  apply (simp add: object_val_ok_def)
*)
lemma etyping2_preserv_class:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   (\<Gamma>,\<M>) \<turnstile> (env,data) \<Longrightarrow>
   \<Gamma> x = Some (ObjectType cls) \<Longrightarrow>
   env x = Some (ObjectVal cls obj) \<Longrightarrow>
   (*obj |\<in>| fmdom objects*)
   fmlookup objects obj = Some cls"
  apply (simp add: etyping2.simps conforms_to_model.simps)
  apply (simp add: object_vals_ok_def)
  apply (metis object_val_ok_def option.simps(5))
  done

lemma attr_vals_is_ok2_then_object_val_ok:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   object_val_ok \<tau> v objects"
  apply (simp add: attr_vals_is_ok2_def)
  apply (simp add: object_val_ok_def)
  by (smt fBall_funion fbspec fmdomI option.simps(5))

lemma attr_vals_is_ok_then_object_val_ok:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   object_val_ok \<tau> v objects"
  by (meson attr_vals_is_ok2_then_object_val_ok attr_vals_is_ok_then)

*)

end

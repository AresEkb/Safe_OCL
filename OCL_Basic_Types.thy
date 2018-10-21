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

(*
  https://en.wikipedia.org/wiki/Order_theory
  https://en.wikipedia.org/wiki/Order_embedding

  https://en.wikipedia.org/wiki/Induced_subgraph
  Функтор Set создает порожденный граф, но с дополнительным свойством

  https://en.wikipedia.org/wiki/Closure_operator
  По ссылке примеры аксиом очень похоже на те которые доказывал для замыканий

  https://en.wikipedia.org/wiki/Galois_connection
  Тут про обратные функции, они тоже использовались для замыканий

  https://en.wikipedia.org/wiki/Limit-preserving_function_(order_theory)
  Многие функции сохраняют пределы
*)


(*** Basic Types ************************************************************)

(* Во многих языках перечисления упорядочены, но в OCL нет, поэтому
   используем множество, а не список
   Возможно стоит заменить fset на натуральные числа
   Достаточно даже одного чила - количество литералов
*)



datatype ('a :: ord) basic_type =
  OclAny
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType 'a
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

inductive direct_basic_subtype :: "('a :: order) basic_type \<Rightarrow> 'a basic_type \<Rightarrow> bool" ("_ \<sqsubset>\<^sub>s _" [65, 65] 65) where
  "Boolean \<sqsubset>\<^sub>s OclAny"
| "UnlimitedNatural \<sqsubset>\<^sub>s Integer"
| "Integer \<sqsubset>\<^sub>s Real"
| "Real \<sqsubset>\<^sub>s OclAny"
| "String \<sqsubset>\<^sub>s OclAny"
| "ObjectType c \<sqsubset>\<^sub>s OclAny"
| "c < d \<Longrightarrow> ObjectType c \<sqsubset>\<^sub>s ObjectType d"
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
inductive_cases direct_basic_subtype_x_ObjectType[elim!]: "\<tau> \<sqsubset>\<^sub>s ObjectType c"
inductive_cases direct_basic_subtype_ObjectType_x[elim!]: "ObjectType c \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_OclAny[elim!]: "\<tau> \<sqsubset>\<^sub>s OclAny"
inductive_cases direct_basic_subtype_OclAny_x[elim!]: "OclAny \<sqsubset>\<^sub>s \<sigma>"
inductive_cases direct_basic_subtype_x_Enum[elim!]: "\<tau> \<sqsubset>\<^sub>s Enum literals"
inductive_cases direct_basic_subtype_Enum_x[elim!]: "Enum literals \<sqsubset>\<^sub>s \<sigma>"

code_pred [show_modes] direct_basic_subtype .

(*** Order for Basic Types **************************************************)

instantiation basic_type :: (order) order
begin

definition "less_basic_type \<equiv> direct_basic_subtype\<^sup>+\<^sup>+"

definition "less_eq_basic_type \<equiv> direct_basic_subtype\<^sup>*\<^sup>*"

(*** Left Introduction Rules ************************************************)

lemma subtype_Boolean_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> Boolean < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_UnlimitedNatural_x_intro [intro]:
  "\<sigma> = Integer \<Longrightarrow> UnlimitedNatural < \<sigma>"
  "\<sigma> = Real \<Longrightarrow> UnlimitedNatural < \<sigma>"
  "\<sigma> = OclAny \<Longrightarrow> UnlimitedNatural < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros(2) apply auto[1]
  apply (meson direct_basic_subtype.intros(2) direct_basic_subtype.intros(3) tranclp.r_into_trancl tranclp_trans)
  by (metis direct_basic_subtype.intros(2) direct_basic_subtype.intros(3) direct_basic_subtype.intros(4) tranclp.simps)

lemma subtype_Integer_x_intro [intro]:
  "\<sigma> = Real \<Longrightarrow> Integer < \<sigma>"
  "\<sigma> = OclAny \<Longrightarrow> Integer < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros(3) apply auto[1]
  by (meson direct_basic_subtype.intros(3) direct_basic_subtype.intros(4) tranclp.r_into_trancl tranclp_trans)

lemma subtype_Real_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> Real < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_String_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> String < \<sigma>"
  unfolding less_basic_type_def
  using direct_basic_subtype.intros by auto

lemma subtype_ObjectType_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> ObjectType c < \<sigma>"
  "\<sigma> = ObjectType d \<Longrightarrow> c < d \<Longrightarrow> ObjectType c < \<sigma>"
  unfolding less_basic_type_def
  apply (simp add: direct_basic_subtype.intros(6) tranclp.r_into_trancl)
  by (simp add: direct_basic_subtype.intros(7) tranclp.r_into_trancl)

lemma subtype_Enum_x_intro [intro]:
  "\<sigma> = OclAny \<Longrightarrow> Enum literals < \<sigma>"
  unfolding less_basic_type_def
  by (simp add: direct_basic_subtype.intros(8) tranclp.r_into_trancl)

(*** Left Elimination Rules *************************************************)

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
  apply auto[1]
  by (metis (mono_tags) direct_basic_subtype_Integer_x less_basic_type_def subtype_Real_x)

lemma subtype_UnlimitedNatural_x [elim!]:
  "UnlimitedNatural < \<sigma> \<Longrightarrow>
   (\<sigma> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (erule converse_tranclpE)
  apply auto[1]
  by (metis (mono_tags) direct_basic_subtype_UnlimitedNatural_x less_basic_type_def subtype_Integer_x)

lemma subtype_String_x [elim!]:
  "String < \<sigma> \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (drule tranclpD)
  using converse_rtranclpE by fastforce

lemma subtype_ObjectType_x' [elim!]:
  "ObjectType c \<le> \<sigma> \<Longrightarrow>
   (\<And>d. \<sigma> = ObjectType d \<Longrightarrow> c \<le> d \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  apply (induct rule: rtranclp_induct)
  apply simp
  using le_less_trans less_le_not_le by blast

lemma subtype_ObjectType_x [elim!]:
  "ObjectType c < \<sigma> \<Longrightarrow>
   (\<And>d. \<sigma> = ObjectType d \<Longrightarrow> c < d \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (induct rule: tranclp_induct)
  apply auto[1]
  using dual_order.strict_implies_order dual_order.strict_trans2 by blast

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

(*** Right Elimination Rules ************************************************)

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
  by (metis (no_types, lifting) direct_basic_subtype_x_Integer direct_basic_subtype_x_UnlimitedNatural tranclp.simps)

lemma subtype_x_Real [elim!]:
  "\<tau> < Real \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (erule tranclp.cases)
  apply auto[1]
  by (metis (mono_tags) direct_basic_subtype_x_Real less_basic_type_def subtype_x_Integer)

lemma subtype_x_String [elim!]:
  "\<tau> < String \<Longrightarrow> False"
  unfolding less_basic_type_def
  using tranclp.cases by fastforce

lemma subtype_x_ObjectType' [elim!]:
  "\<tau> \<le> ObjectType d \<Longrightarrow>
   (\<And>c. \<tau> = ObjectType c \<Longrightarrow> c \<le> d \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_basic_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  using dual_order.order_iff_strict by fastforce

lemma subtype_x_ObjectType [elim!]:
  "\<tau> < ObjectType d \<Longrightarrow>
   (\<And>c. \<tau> = ObjectType c \<Longrightarrow> c < d \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_basic_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  using less_trans by blast

lemma subtype_x_Enum [elim!]:
  "\<tau> < Enum literals \<Longrightarrow> False"
  unfolding less_basic_type_def
  using tranclp.cases by fastforce

(*** Properties *************************************************************)

lemma basic_subtype_acyclic':
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: "'a basic_type"
  by (cases \<tau>; auto)

lemma tranclp_less_basic_type:
  "(\<tau>, \<sigma>) \<in> {(\<tau>, \<sigma>). \<tau> \<sqsubset>\<^sub>s \<sigma>}\<^sup>+ \<longleftrightarrow> \<tau> < \<sigma>"
  by (simp add: tranclp_unfold less_basic_type_def)

lemma basic_subtype_acyclic:
  "acyclicP direct_basic_subtype"
  apply (rule acyclicI)
  apply (auto)
  using OCL_Basic_Types.basic_subtype_acyclic' OCL_Basic_Types.tranclp_less_basic_type by auto

lemma direct_basic_subtype_antisym:
  "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>s \<tau> \<Longrightarrow>
   False"
  by (metis (mono_tags) OCL_Basic_Types.basic_subtype_acyclic' less_basic_type_def tranclp.r_into_trancl tranclp_into_tranclp2)
  
lemma direct_basic_subtype_not_trans:
  "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset>\<^sub>s \<rho> \<Longrightarrow>
   \<not> \<rho> \<sqsubset>\<^sub>s \<tau>"
  by (erule direct_basic_subtype.cases; auto)

(*lemma direct_basic_subtype_det:
  "direct_basic_subtype \<tau> \<sigma> \<Longrightarrow>
   direct_basic_subtype \<tau> \<rho> \<Longrightarrow>
   \<sigma> = \<rho>"
  using direct_basic_subtype.simps by auto*)

lemma less_le_not_le_basic_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a basic_type"
  unfolding less_basic_type_def less_eq_basic_type_def
  apply (rule iffI; auto)
  apply (metis (mono_tags, lifting) less_basic_type_def basic_subtype_acyclic' tranclp_rtranclp_tranclp)
  by (drule rtranclpD; auto)

lemma order_refl_basic_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a basic_type"
  by (simp add: less_eq_basic_type_def)

lemma order_trans_basic_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a basic_type"
  by (auto simp add: less_eq_basic_type_def)

lemma antisym_basic_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a basic_type"
  by (metis (mono_tags, lifting) less_eq_basic_type_def less_le_not_le_basic_type less_basic_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_basic_type)
  apply (simp)
  using order_trans_basic_type apply blast
  by (simp add: antisym_basic_type)

end

(*** Upper Semilattice for Basic Types **************************************)

instantiation basic_type :: (semilattice_sup) semilattice_sup
begin

fun sup_basic_type where
  "ObjectType c \<squnion> ObjectType d = ObjectType (c \<squnion> d)"
| "ObjectType c \<squnion> _ = OclAny"
| "\<tau> \<squnion> \<sigma> = (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"

lemma sup_ge1_ObjectType:
  "ObjectType c \<le> ObjectType c \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: direct_basic_subtype.simps less_eq_basic_type_def r_into_rtranclp)
  by (metis Nitpick.rtranclp_unfold direct_basic_subtype.intros(7) le_less r_into_rtranclp sup.cobounded1)

lemma sup_ge1_basic_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a basic_type"
  apply (induct \<tau>)
  using dual_order.order_iff_strict less_eq_basic_type_def sup_ge1_ObjectType by auto

(*  apply (auto simp: less_eq_basic_type_def sup_basic_type_def)
  apply (induct \<tau>)
  apply (simp_all add: direct_basic_subtype.intros r_into_rtranclp)
  apply (metis less_basic_type_def subtype_Integer_x_intro(2) tranclp_into_rtranclp)
  by (metis less_basic_type_def subtype_UnlimitedNatural_x_intro(3) tranclp_into_rtranclp)*)

lemma sup_commut_basic_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a basic_type"
  by (induct \<tau>; induct \<sigma>; auto simp add: sup.commute)

lemma subtype_OclAny_x_intro' [intro]:
  "\<sigma> = OclAny \<Longrightarrow> direct_basic_subtype\<^sup>*\<^sup>* OclAny \<sigma>"
  by simp

lemma sup_least_basic_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a basic_type"
  apply (auto simp: less_eq_basic_type_def)
  apply (induct \<rho> arbitrary: \<tau> \<sigma>)
  apply (metis (mono_tags, hide_lams) less_eq_basic_type_def less_le_not_le subtype_OclAny_x sup_basic_type.simps(9) sup_commut_basic_type sup_ge1_basic_type)
  apply (metis dual_order.order_iff_strict less_eq_basic_type_def subtype_x_Boolean sup_basic_type.simps(24))
  apply (smt dual_order.order_iff_strict less_eq_basic_type_def subtype_UnlimitedNatural_x_intro(1) subtype_x_Real sup_basic_type.simps(32) sup_basic_type.simps(33) sup_basic_type.simps(34) sup_basic_type.simps(40) sup_basic_type.simps(41) sup_basic_type.simps(48) sup_commut_basic_type)
  apply (smt dual_order.order_iff_strict less_eq_basic_type_def rtranclp_idemp subtype_x_Integer sup_basic_type.simps(40) sup_basic_type.simps(41) sup_basic_type.simps(48) sup_commut_basic_type)
  apply (metis direct_basic_subtype_x_UnlimitedNatural less_eq_basic_type_def rtranclp.simps sup_basic_type.simps(48))
  apply (metis direct_basic_subtype_x_String less_eq_basic_type_def rtranclp.simps sup_basic_type.simps(56))
  apply (smt Nitpick.rtranclp_unfold direct_basic_subtype.intros(7) less_eq_basic_type_def r_into_rtranclp subtype_x_ObjectType' sup.commute sup.orderE sup.strict_order_iff sup_basic_type.simps(1) sup_left_commute)
  by (metis direct_basic_subtype_x_Enum eq_iff rtranclp.simps sup_basic_type.simps(15))

instance
  apply intro_classes
  apply (simp add: sup_ge1_basic_type)
  apply (simp add: sup_commut_basic_type sup_ge1_basic_type)
  by (simp add: sup_least_basic_type)

end

(*** Minimal Basic Types ****************************************************)

definition "is_min_basic_type \<tau> \<equiv> \<nexists>\<sigma>. \<sigma> \<sqsubset>\<^sub>s \<tau>"
(*
lemma is_min_basic_type_code [code]:
  "is_min_basic_type \<tau> \<longleftrightarrow>
   \<tau> = Boolean \<or> \<tau> = UnlimitedNatural \<or> \<tau> = String \<or>
   (case \<tau> of ObjectType _ \<Rightarrow> True | _ \<Rightarrow> False) \<or>
   (case \<tau> of Enum _ \<Rightarrow> True | _ \<Rightarrow> False)"
  apply (simp add: is_min_basic_type_def)
  apply (rule iffI)
  apply (cases \<tau>; simp add: direct_basic_subtype.simps)
  apply auto[1]
(*  using direct_basic_subtype.simps by force*)
*)
lemma Boolean_is_min [simp]:
  "is_min_basic_type Boolean"
  by (auto simp add: is_min_basic_type_def)

lemma UnlimitedNatural_is_min [simp]:
  "is_min_basic_type UnlimitedNatural"
  by (auto simp add: is_min_basic_type_def)

lemma String_is_min [simp]:
  "is_min_basic_type String"
  by (auto simp add: is_min_basic_type_def)
(*
lemma ObjectType_is_min [simp]:
  "is_min_basic_type (ObjectType cls)"
  by (auto simp add: is_min_basic_type_def)
*)
lemma Enum_is_min [simp]:
  "is_min_basic_type (Enum literals)"
  by (auto simp add: is_min_basic_type_def)

(*** Code Setup for Basic Types *********************************************)

fun basic_subtype_fun :: "'a::order basic_type \<Rightarrow> 'a basic_type \<Rightarrow> bool" where
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
| "basic_subtype_fun (ObjectType c) (ObjectType d) = (c < d)"
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

datatype classes1 = ClassA | ClassB | Object

instantiation classes1 :: semilattice_sup
begin

inductive subclass1 where
  "subclass1 ClassA Object"
| "subclass1 ClassB Object"

code_pred [show_modes] subclass1 .

definition "less_classes1 \<equiv> subclass1"

definition "(c::classes1) \<le> d \<equiv> c = d \<or> c < d"

fun sup_classes1 where
  "ClassA \<squnion> ClassA = ClassA"
| "ClassA \<squnion> _ = Object"
| "ClassB \<squnion> ClassB = ClassB"
| "ClassB \<squnion> _ = Object"
| "Object \<squnion> _ = Object"

lemma sup_ge1_classes1:
  "c \<le> c \<squnion> d"
  for c d :: classes1
  by (smt classes1.distinct(1) classes1.distinct(3) less_classes1_def less_eq_classes1_def subclass1.intros(1) subclass1.intros(2) sup_classes1.elims)

instance
  apply intro_classes
  using less_classes1_def less_eq_classes1_def subclass1.simps apply auto[1]
  apply (simp add: less_eq_classes1_def)
  using less_classes1_def subclass1.simps less_eq_classes1_def apply auto[1]
  using less_classes1_def subclass1.simps less_eq_classes1_def apply auto[1]
  apply (simp add: sup_ge1_classes1)
  apply (smt less_classes1_def less_eq_classes1_def subclass1.intros(1) subclass1.intros(2) sup_classes1.elims sup_classes1.simps(3) sup_classes1.simps(5))
  by (smt less_classes1_def subclass1.simps less_eq_classes1_def sup_classes1.simps(1) sup_classes1.simps(4) sup_ge1_classes1)

end

term "Integer::classes1 basic_type"

value "(Integer::classes1 basic_type) \<sqsubset>\<^sub>s Real"
value "basic_subtype_fun (Integer::classes1 basic_type) Real"
value "basic_subtype_fun (Integer::classes1 basic_type) OclAny"
value "basic_subtype_fun (Boolean::classes1 basic_type) Integer"
(*
value "direct_basic_subtype\<^sup>+\<^sup>+ Integer Real"
value "direct_basic_subtype\<^sup>*\<^sup>* Integer Real"
values "{x. direct_basic_subtype\<^sup>*\<^sup>* Integer Real}"
values "{x. direct_basic_subtype\<^sup>*\<^sup>* Integer x}"
values "{x. Integer < x}"
*)
value "(UnlimitedNatural::classes1 basic_type) < Real"
value "(UnlimitedNatural::classes1 basic_type) \<le> Real"
value "(Real::classes1 basic_type) < Real"
value "(Real::classes1 basic_type) \<le> Real"

end

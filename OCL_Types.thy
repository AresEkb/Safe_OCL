theory OCL_Types
  imports
    Main
    Transitive_Closure_Ext
    Tuple
    OCL_Basic_Types
    (*"~~/src/HOL/Library/Finite_Map"*)
begin

(*
  Тут много определений и теорем для систем типов:
  http://gallium.inria.fr/~remy/mpri/cours1.pdf

  Перечитать:
  https://en.wikipedia.org/wiki/Subtyping
  Особенно (про кортежи, наверное это относитя к остальным - коллекции, Req, Opt):
  https://en.wikipedia.org/wiki/Structural_type_system

  https://en.wikipedia.org/wiki/Subtyping#Width_and_depth_subtyping
  https://en.wikipedia.org/wiki/Subtyping#Relationship_with_inheritance
*)

(* В разделе 8.2 спецификации OCL:
   Note that in contrast with invalid, null is a valid value and as such can be owned by collections.
   Какой-то бред. Получается для коллекций нужно делать отдельные простые типы, не допускающие ошибки?
   Или достаточно сделать ещё правило валидации для коллекций дополнительно к проверке типа элементов?

   Кортежи нужны в основном для операций с out параметрами
*)

notation
  sup (infixl "\<squnion>" 65)

(*type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)*)

(*** Types ******************************************************************)

(* OclState не реализуем. В A.2.6 написано, что он похож на перечисление
   В спецификации кортежи определяются в одном разделе с коллекциями.
   Также они не могут быть опциональными. И ещё они OclAny не является их супертипом
   По-этому описываем их тут, а не в базовых типах

   MessageType и TemplateParameterType не реализуем

   Приложение A информативное, по-этому если там что-то неправильно,
   это видимо можно игнорировать, но отметить в статье
 *)

datatype (plugins del: "size") 'a type =
  SupType
| OclInvalid
| OclVoid
| Required "'a basic_type" ("_[1]" [1000] 1000)
| Optional "'a basic_type" ("_[?]" [1000] 1000)
| Collection "'a type"
| Set "'a type"
| OrderedSet "'a type"
| Bag "'a type"
| Sequence "'a type"
| Tuple "(nat, 'a type) fmap"


(* Иерархия типов описана в A.2.7 Type Hierarchy *)

(*
   В будущем нужно будет определить отдельный тип для непустых списков,
   чтобы использовать его для Tuple, но сейчас это может усложнить доказательство теорем:
   https://stackoverflow.com/questions/45995633/how-to-define-a-data-type-with-constraints
 *)

inductive direct_subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" ("_ \<sqsubset> _" [65, 65] 65) where
  "OclInvalid \<sqsubset> OclVoid"
| "OclInvalid \<sqsubset> Required \<sigma>"
| "OclVoid \<sqsubset> Optional \<sigma>"
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
| "OclInvalid \<sqsubset> Tuple \<pi>"
| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> SupType"

(* OclVoid не может быть подтипом для Tuple при используемом подходе,
   потому что у кортежей при спуске по иерархии типов элементов становится всё больше.
   Это интересная проблема, нужно обязательно написать о ней в статье
   А, вот, SupType - это как раз наоборот не проблема и он нужен для полиморфизма

   Множественное наследование сейчас есть и без кортережей: void, optional, collection
   Кортежи в этом отношении ничего не усложняют
   Сложность только в том, что у кортежа несколько параметров
   И эта множественность должна учитываться в одном правиле, а не разных как для других типов

   Для простоты вместо fmap можно использовать список
   По сути просто заменяем имена свойств натуральными числами
 *)

declare direct_subtype.intros [intro]

inductive_cases direct_subtype_x_OclInvalid[elim]: "\<tau> \<sqsubset> OclInvalid"
inductive_cases direct_subtype_OclInvalid_x[elim!]: "OclInvalid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_OclVoid[elim]: "\<tau> \<sqsubset> OclVoid"
inductive_cases direct_subtype_OclVoid_x[elim!]: "OclVoid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Required[elim]: "\<tau> \<sqsubset> \<sigma>[1]"
inductive_cases direct_subtype_Required_x[elim]: "\<tau>[1] \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Optional[elim!]: "\<tau> \<sqsubset> \<sigma>[?]"
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
inductive_cases direct_subtype_x_Tuple[elim]: "\<tau> \<sqsubset> Tuple \<pi>"
inductive_cases direct_subtype_Tuple_x[elim]: "Tuple \<pi> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_SupType[elim]: "\<tau> \<sqsubset> SupType"
inductive_cases direct_subtype_SupType_x[elim]: "SupType \<sqsubset> \<sigma>"

lemma direct_subtype_antisym:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset> \<tau> \<Longrightarrow>
   False"
  apply (induct rule: direct_subtype.induct)
  using direct_basic_subtype_asym apply auto
  apply (erule direct_subtype_x_Tuple; auto)
  apply (rule_tac ?f="direct_subtype" and ?xm="\<pi>" and ?ym="\<pi>'" in strict_subtuple_antisym; simp)
  done

instantiation type :: (order) order
begin

definition "less_type \<equiv> direct_subtype\<^sup>+\<^sup>+"

definition "less_eq_type \<equiv> direct_subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

lemma subtype_OclInvalid_x_intro [intro]:
  "OclInvalid \<le> \<sigma>"
  unfolding less_eq_type_def
proof (induct \<sigma>)
  case SupType
  thus ?case
    by (metis (mono_tags) direct_subtype.intros(1) direct_subtype.intros(20)
          direct_subtype.intros(3) rtranclp.simps) 
next
  case OclInvalid show ?case by simp 
next
  case OclVoid show ?case by (rule r_into_rtranclp; auto)
next
  case (Required x) show ?case by (rule r_into_rtranclp; auto)
next
  case (Optional x) show ?case
    by (meson direct_subtype.intros(1) direct_subtype.intros(3)
          r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
next
  case (Collection \<sigma>) show ?case
    apply (rule_tac ?b="Set \<sigma>" in rtranclp.rtrancl_into_rtrancl)
    apply (rule_tac ?b="Set OclInvalid" in converse_rtranclp_into_rtranclp, auto)
    apply (rule_tac ?R="direct_subtype" and ?f="Set" in fun_preserve_morphism_composition;
           auto simp add: Collection.hyps)
    done
next
  case (Set \<sigma>)
  thus ?case
    apply (rule_tac ?b="Set OclInvalid" in converse_rtranclp_into_rtranclp, auto)
    apply (rule_tac ?R="direct_subtype" and ?f="Set" in fun_preserve_morphism_composition; auto)
    done
next
  case (OrderedSet \<sigma>)
  thus ?case
    apply (rule_tac ?b="OrderedSet OclInvalid" in converse_rtranclp_into_rtranclp, auto)
    apply (rule_tac ?R="direct_subtype" and ?f="OrderedSet" in fun_preserve_morphism_composition; auto)
    done
next
  case (Bag \<sigma>)
  thus ?case
    apply (rule_tac ?b="Bag OclInvalid" in converse_rtranclp_into_rtranclp, auto)
    apply (rule_tac ?R="direct_subtype" and ?f="Bag" in fun_preserve_morphism_composition; auto)
    done
next
  case (Sequence \<sigma>)
  thus ?case
    apply (rule_tac ?b="Sequence OclInvalid" in converse_rtranclp_into_rtranclp, auto)
    apply (rule_tac ?R="direct_subtype" and ?f="Sequence" in fun_preserve_morphism_composition; auto)
    done
next
  case (Tuple x) show ?case by (rule r_into_rtranclp; auto)
qed

lemma subtype_x_Required_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply auto
  by (rule fun_preserve_morphism_composition[of direct_basic_subtype]; auto)

lemma subtype_x_Optional_intro [intro]:
  "\<tau> = OclVoid \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply auto
  apply (rule fun_preserve''; auto)
  apply (rule fun_preserve_morphism_composition[of direct_basic_subtype]; auto)
  done

lemma subtype_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  unfolding less_eq_type_def
  apply simp
  by (rule fun_preserve_morphism_composition[of direct_subtype]; auto)

lemma subtype_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  unfolding less_eq_type_def
  apply simp
  by (rule fun_preserve_morphism_composition[of direct_subtype]; auto)

lemma subtype_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  unfolding less_eq_type_def
  apply simp
  by (rule fun_preserve_morphism_composition[of direct_subtype]; auto)

lemma subtype_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  unfolding less_eq_type_def
  apply simp
  by (rule fun_preserve_morphism_composition[of direct_subtype]; auto)

lemma subtype_x_Collection_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  unfolding less_type_def less_eq_type_def
  apply simp_all
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve_morphism_composition[of direct_subtype]; auto)
  done

lemma subtype_x_Tuple_intro [intro]:
  "\<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> \<tau> \<le> Tuple \<xi>"
  unfolding less_eq_type_def
  apply (drule subtuple_rtrancl_to_trancl)
  apply (drule subtuple_to_trancl, simp)
  by (smt direct_subtype.intros(23) fun_preserve_morphism_composition' tranclp_into_rtranclp2)

lemma subtype_x_SupType_intro [intro]:
  "\<tau> \<noteq> SupType \<Longrightarrow> \<tau> \<le> SupType"
  unfolding less_eq_type_def
proof (induct \<tau>)
  case SupType
  thus ?case by auto
next
  case OclInvalid
  thus ?case
    by (metis (mono_tags) OCL_Types.subtype_OclInvalid_x_intro less_eq_type_def)
next
  case OclVoid
  thus ?case
    by (meson direct_subtype.intros(20) direct_subtype.intros(3)
          rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
next
case (Required x)
  thus ?case
    apply (rule_tac ?y="OclAny[1]" in rtranclp_trans)
    apply (metis (mono_tags) less_eq_type_def subtype_x_OclAny_intro subtype_x_Required_intro)
    by (meson converse_rtranclp_into_rtranclp direct_subtype.intros(20) direct_subtype.intros(6) r_into_rtranclp)
next
  case (Optional x)
  thus ?case
    apply (rule_tac ?y="OclAny[?]" in rtranclp_trans)
    apply (metis (mono_tags) less_eq_type_def subtype_x_OclAny_intro subtype_x_Optional_intro(3))
    by (simp add: direct_subtype.intros(20) r_into_rtranclp)
next
  case (Collection \<tau>)
  have "direct_subtype\<^sup>+\<^sup>+ (Collection SupType) SupType"
    by (simp add: direct_subtype.intros(21) less_type_def tranclp.r_into_trancl)
  thus ?case
    by (metis (mono_tags) Collection.hyps Nitpick.rtranclp_unfold less_eq_type_def
              less_type_def subtype_x_Collection_intro(5) tranclp_trans)
next
  case (Set \<tau>)
  have "direct_subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis (mono_tags) Set.hyps less_eq_type_def rtranclp.rtrancl_refl subtype_x_Collection_intro(5))
  also have "direct_subtype\<^sup>+\<^sup>+ (Set \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    apply (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
    apply (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
    done
next
  case (OrderedSet \<tau>)
  have "direct_subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis (mono_tags) OrderedSet.hyps less_eq_type_def rtranclp.rtrancl_refl subtype_x_Collection_intro(5))
  also have "direct_subtype\<^sup>+\<^sup>+ (OrderedSet \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    apply (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
    apply (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
    done
next
  case (Bag \<tau>)
  have "direct_subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis (mono_tags) Bag.hyps less_eq_type_def rtranclp.rtrancl_refl subtype_x_Collection_intro(5))
  also have "direct_subtype\<^sup>+\<^sup>+ (Bag \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    apply (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
    apply (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
    done
next
case (Sequence \<tau>)
  have "direct_subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis (mono_tags) Sequence.hyps less_eq_type_def rtranclp.rtrancl_refl subtype_x_Collection_intro(5))
  also have "direct_subtype\<^sup>+\<^sup>+ (Sequence \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    apply (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
    apply (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
    done
next
  case (Tuple x)
  thus ?case
    by (simp add: direct_subtype.intros(24) r_into_rtranclp)
qed

(*** Functors ***************************************************************)

lemma Required_functor:
  "functor_under_rel direct_basic_subtype direct_subtype Required"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Required rangeI tranclp.simps)

lemma subtype_OclVoid_x [elim]:
  "OclVoid < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: tranclp_induct; blast)

lemma Optional_functor:
  "functor_under_rel direct_basic_subtype direct_subtype Optional"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  apply (metis direct_subtype.intros(3) direct_subtype_x_OclInvalid direct_subtype_x_OclVoid tranclp.cases)
  by (metis (mono_tags) OCL_Types.subtype_OclVoid_x direct_subtype.intros(3) less_type_def tranclp_into_tranclp2 type.distinct(5) type.distinct(55))

lemma Set_functor:
  "functor_under_rel direct_subtype direct_subtype Set"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Set rangeI tranclp.cases)

lemma OrderedSet_functor:
  "functor_under_rel direct_subtype direct_subtype OrderedSet"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_OrderedSet rangeI tranclp.cases)

lemma Bag_functor:
  "functor_under_rel direct_subtype direct_subtype Bag"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Bag rangeI tranclp.cases)

lemma Sequence_functor:
  "functor_under_rel direct_subtype direct_subtype Sequence"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Sequence rangeI tranclp.cases)

lemma subtype_Collection_x [elim]:
  "Collection \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)[1]
  by (metis direct_subtype_Collection_x direct_subtype_SupType_x tranclp.trancl_into_trancl)

lemma Collection_functor:
  "functor_under_rel direct_subtype direct_subtype Collection"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis (mono_tags) OCL_Types.subtype_Collection_x direct_subtype_SupType_x less_type_def rangeI)

lemma Tuple_functor:
  "functor_under_rel (strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>)) direct_subtype Tuple"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  apply (metis (no_types, lifting) direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.cases)
  apply (meson injI type.inject(8))
  done

(* TODO: Посмотреть нужна ли где-то "натуральность": *)

lemma subtype_Set_x' [elim]:
  "Set \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)
  by (erule direct_subtype.cases; auto; meson rtranclp.rtrancl_into_rtrancl)
(*
lemma Required_Optional_natural:
  "natural_under_rel direct_basic_subtype direct_subtype Required Optional"
  apply (auto simp add: natural_under_rel_def Required_functor Optional_functor direct_subtype.intros(6))
  apply (metis (mono_tags) OCL_Types.subtype_OclVoid_x direct_subtype.intros(3) less_type_def rtranclp_into_tranclp2 tranclp_into_rtranclp type.distinct(55) type.distinct(6))
  apply (metis (mono_tags) OCL_Types.subtype_x_Required' less_type_def type.distinct(25) type.distinct(55))
  by (metis (mono_tags) OCL_Types.subtype_x_Optional''' direct_subtype_Required_x direct_subtype_x_OclInvalid direct_subtype_x_OclVoid less_eq_type_def tranclp.simps tranclp_into_rtranclp)
*)
lemma Set_Collection_natural:
  "natural_under_rel direct_subtype direct_subtype Set Collection"
  apply (auto simp add: natural_under_rel_def Set_functor Collection_functor)
  apply (metis (mono_tags) OCL_Types.subtype_Collection_x less_type_def type.simps(20) type.simps(90))
  by (metis (mono_tags) OCL_Types.subtype_Set_x' direct_subtype_SupType_x less_eq_type_def tranclpD tranclp_into_rtranclp)

(*** Elimination Rules ******************************************************)

lemma subtype_x_OclInvalid' [elim]:
  "\<tau> \<le> OclInvalid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (metis direct_subtype_x_OclInvalid rtranclp.cases)

lemma subtype_x_OclInvalid [elim]:
  "\<tau> < OclInvalid \<Longrightarrow> P"
  unfolding less_type_def
  by (metis direct_subtype_x_OclInvalid tranclp.cases)

lemma subtype_x_OclVoid' [elim]:
  "\<tau> \<le> OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (metis (mono_tags, lifting) direct_subtype_x_OclVoid less_eq_type_def rtranclp.cases subtype_x_OclInvalid')

lemma subtype_x_OclVoid [elim]:
  "\<tau> < OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (metis (mono_tags, lifting) direct_subtype_x_OclVoid less_type_def subtype_x_OclInvalid tranclp.simps)

lemma subtype_x_Required'':
  "\<tau> < \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  by blast

lemma subtype_x_Required [elim]:
  "\<tau> < \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_basic_type_def
  by (metis (mono_tags) Required_functor less_type_def subtype_x_Required'' tranclp_fun_preserve_gen_1a)

lemma subtype_x_Required' [elim]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (metis converse_rtranclp_into_rtranclp direct_subtype_x_OclInvalid direct_subtype_x_Required)

lemma subtype_x_Optional' [elim]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (erule direct_subtype.cases; auto simp add: converse_rtranclp_into_rtranclp less_eq_basic_type_def)

lemma subtype_x_Optional [elim]:
  "\<tau> < \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis direct_subtype_x_Optional eq_refl less_basic_type_def tranclp.r_into_trancl)
  apply (erule direct_subtype.cases; auto)
  apply (simp add: converse_rtranclp_into_rtranclp less_eq_basic_type_def)
  by (simp add: less_basic_type_def tranclp_into_tranclp2)

lemma subtype_x_Set' [elim]:
  "\<tau> \<le> Set \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (metis converse_rtranclp_into_rtranclp direct_subtype_x_OclInvalid direct_subtype_x_Set)

lemma subtype_x_Set [elim]:
  "\<tau> < Set \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply blast
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Set tranclp_into_tranclp2)

lemma subtype_x_OrderedSet' [elim]:
  "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (metis converse_rtranclp_into_rtranclp direct_subtype_x_OclInvalid direct_subtype_x_OrderedSet)

lemma subtype_x_OrderedSet [elim]:
  "\<tau> < OrderedSet \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply blast
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_OrderedSet tranclp_into_tranclp2)

lemma subtype_x_Bag' [elim]:
  "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (metis converse_rtranclp_into_rtranclp direct_subtype_x_OclInvalid direct_subtype_x_Bag)

lemma subtype_x_Bag [elim]:
  "\<tau> < Bag \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply blast
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Bag tranclp_into_tranclp2)

lemma subtype_x_Sequence' [elim]:
  "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (metis converse_rtranclp_into_rtranclp direct_subtype_x_OclInvalid direct_subtype_x_Sequence)

lemma subtype_x_Sequence [elim]:
  "\<tau> < Sequence \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply blast
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Sequence tranclp_into_tranclp2)

lemma subtype_x_Collection' [elim]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (erule direct_subtype.cases; auto simp add: converse_rtranclp_into_rtranclp)

lemma subtype_x_Collection [elim]:
  "\<tau> < Collection \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis (mono_tags) Nitpick.rtranclp_unfold direct_subtype_x_Collection less_eq_type_def tranclp.r_into_trancl)
  by (erule direct_subtype.cases; auto simp add: converse_rtranclp_into_rtranclp
            less_eq_type_def tranclp_into_tranclp2 tranclp_into_rtranclp)



lemma rtranclp_into_rtranclp2 [simp]:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>*\<^sup>* = P\<^sup>*\<^sup>*"
  by (intro ext; auto simp add: Nitpick.rtranclp_unfold eq_trancl)

lemma rtrancl_to_subtuple:
  "(subtuple r)\<^sup>*\<^sup>* xm ym \<Longrightarrow>
   subtuple r\<^sup>*\<^sup>* xm ym"
  apply (induct rule: rtranclp_induct)
  apply (simp add: fmap.rel_refl_strong fmrel_to_subtuple)
  apply (rule fmrel_on_fset_trans; auto)
  done

thm rtranclp_fun_preserve_gen_1a

lemma direct_subtype_preserve_Tuple2:
  "direct_subtype\<^sup>*\<^sup>* (Tuple x) (Tuple y) \<Longrightarrow>
   (\<lambda>x y. Tuple x \<sqsubset> Tuple y)\<^sup>*\<^sup>* x y"
  apply (rule rtranclp_fun_preserve_gen_1a, auto)
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  apply (metis direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.cases)
  apply (meson injI type.inject(8))
  done

lemma Tuple_implies_TupleE2:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow> (\<And>\<pi>. \<tau> = Tuple \<pi> \<or> \<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (induct rule: converse_rtranclp_induct; auto)


lemma subtype_Tuple_into_strict_subtuple:
  assumes "direct_subtype\<^sup>+\<^sup>+ (Tuple \<pi>) (Tuple \<xi>)"
    and "acyclic_on (fmran' \<pi>) direct_subtype"
    shows "strict_subtuple direct_subtype\<^sup>*\<^sup>* \<pi> \<xi>"
proof -
  have "(strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ \<pi> \<xi>"
    apply (insert assms(1))
    by (rule tranclp_fun_preserve_gen_1a; auto simp add: Tuple_functor)
  from this assms(2)
  have "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ \<pi> \<xi>"
    apply (induct rule: tranclp_induct)
    apply (metis (mono_tags, lifting) strict_subtuple_mono tranclp.r_into_trancl)
    using strict_subtuple_trans by blast
  then show ?thesis
    by (simp add: tranclp_into_rtranclp2)
qed

lemma subtype_Tuple_into_subtuple:
  assumes "direct_subtype\<^sup>*\<^sup>* (Tuple \<pi>) (Tuple \<xi>)"
    shows "subtuple direct_subtype\<^sup>*\<^sup>* \<pi> \<xi>"
proof -
  have "(subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>*\<^sup>* \<pi> \<xi>"
    apply (insert assms)
    apply (drule direct_subtype_preserve_Tuple2)
    by (smt direct_subtype_x_Tuple mono_rtranclp type.inject(8) type.simps(46))
  then have "subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>*\<^sup>* \<pi> \<xi>"
    by (rule rtrancl_to_subtuple)
  thus ?thesis
    by (simp)
qed

lemma subtype_x_Tuple' [elim]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply (simp add: rtrancl_to_subtuple)
  by (metis (mono_tags) OCL_Types.Tuple_implies_TupleE2 converse_rtranclp_into_rtranclp
        less_eq_type_def subtype_Tuple_into_subtuple)

lemma subtype_x_Tuple2:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   acyclic_on (fmran' \<xi>) direct_subtype \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_eq_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis direct_subtype_x_Tuple r_into_rtranclp subtype_Tuple_into_subtuple)
  by (metis (no_types, lifting) direct_subtype_x_OclInvalid direct_subtype_x_Tuple
      subtype_Tuple_into_strict_subtuple subtype_Tuple_into_subtuple tranclp_into_rtranclp
      tranclp_into_tranclp2)






lemma subtype_x_SupType [elim]:
  "\<tau> < SupType \<Longrightarrow> (\<tau> \<noteq> SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (mono_tags) direct_subtype_SupType_x less_type_def tranclpD)

(*** Properties *************************************************************)

lemma subtype_irrefl:
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: "'a type"
  apply (induct \<tau>, auto)
  by (metis (mono_tags) less_type_def subtype_Tuple_into_strict_subtuple)

lemma direct_subtype_acyclic:
  "acyclicP direct_subtype"
  apply (rule acyclicI)
  apply (auto simp add: trancl_def)
  by (metis (mono_tags) OCL_Types.subtype_irrefl less_type_def)

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type"
  apply (rule iffI; auto simp add: less_type_def less_eq_type_def)
  apply (metis (mono_tags) subtype_irrefl less_type_def tranclp_rtranclp_tranclp)
  by (metis rtranclpD)

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type"
  by (simp add: less_eq_type_def)

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  by (auto simp add: less_eq_type_def)

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  by (metis (mono_tags, lifting) less_eq_type_def less_le_not_le_type less_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  done

end

(* Мы доказали ацикличность, теперь из этих теорем можно убрать
   лишние предусловия: *)

lemma subtype_x_Tuple [elim]:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis less_type_def subtype_irrefl subtype_x_Tuple2)

(*
lemma subtype_x_Tuple' [elim]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply (simp add: fmrel_on_fset_fmrel_restrict fmap.rel_refl)
  by (metis (no_types, lifting) direct_subtype_x_OclInvalid
        direct_subtype_x_Tuple dual_order.strict_iff_order less_type_def
        rtranclp_into_tranclp2 subtype_Tuple_Tuple''')
*)


instantiation type :: (type) size 
begin

primrec size_type :: "'a type \<Rightarrow> nat" where
  "size_type SupType = 0"
| "size_type OclInvalid = 0"
| "size_type OclVoid = 0"
| "size_type (Required _) = 0"
| "size_type (Optional _) = 0"
| "size_type (Collection x) = Suc (size_type x)"
| "size_type (Set x) = Suc (size_type x)"
| "size_type (OrderedSet x) = Suc (size_type x)"
| "size_type (Bag x) = Suc (size_type x)"
| "size_type (Sequence x) = Suc (size_type x)"
| "size_type (Tuple xs) = Suc (ffold tcf 0 (fset_of_fmap (fmmap size_type xs)))"

instance ..

end

lemma measure_cond [intro]:
  "k |\<in>| fmdom x \<Longrightarrow>
   size (the (fmlookup x k)) < size (Tuple x)"
  using elem_le_ffold by auto

instantiation type :: (semilattice_sup) semilattice_sup
begin

function sup_type where
  "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "OclVoid \<squnion> \<sigma> = (case \<sigma>
    of OclVoid \<Rightarrow> OclVoid
     | OclInvalid \<Rightarrow> OclVoid
     | Required \<rho> \<Rightarrow> Optional \<rho>
     | Optional \<rho> \<Rightarrow> Optional \<rho>
     | _ \<Rightarrow> SupType)"
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
| "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
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
| "Tuple \<pi> \<squnion> \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> Tuple (fmmerge' (\<squnion>) \<pi> \<xi>)
     | OclInvalid \<Rightarrow> Tuple \<pi>
     | _ \<Rightarrow> SupType)"
| "SupType \<squnion> \<sigma> = SupType"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(xs, ys). size ys)")
  using measure_cond apply auto
  done

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case SupType show ?case by simp
  case OclInvalid show ?case by auto 
  case OclVoid show ?case by (induct \<sigma>; auto)
  case (Required x) show ?case by (induct \<sigma>; auto simp add: subtype_x_Optional_intro(2) subtype_x_Required_intro)
  case (Optional x) show ?case by (induct \<sigma>; auto)
  case (Collection \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Set \<tau>) thus ?case by (induct \<sigma>; auto)
  case (OrderedSet \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Bag \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Sequence \<tau>) thus ?case by (induct \<sigma>; auto)
next
  case (Tuple \<pi>)
  also have Tuple_less_eq_sup:
    "(\<And>\<tau> \<sigma>. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
     Tuple \<pi> \<le> Tuple \<pi> \<squnion> \<sigma>"
    by (cases \<sigma>, auto)
  ultimately show ?case by (cases \<sigma>, auto)
qed

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case SupType show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case OclInvalid show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case OclVoid show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case (Required \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Optional \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Collection \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Set \<tau>) thus ?case by (cases \<sigma>; simp)
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Bag \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Tuple \<pi>) thus ?case
    apply (cases \<sigma>; simp add: less_eq_type_def)
    using fmmerge_commut by blast
qed

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
proof (induct \<rho> arbitrary: \<tau> \<sigma>)
  case SupType show ?case using eq_refl by auto
next
  case OclInvalid thus ?case by auto
next
  case OclVoid show ?case
    apply (insert OclVoid)
    by (erule subtype_x_OclVoid'; erule subtype_x_OclVoid'; auto)
next
  case (Required x) show ?case
    apply (insert Required)
    by (erule subtype_x_Required'; erule subtype_x_Required'; auto)
next
  case (Optional x) show ?case
    apply (insert Optional)
    apply (erule subtype_x_Optional'; erule subtype_x_Optional'; auto)
    using le_sup_iff by blast
next
  case (Collection \<rho>) show ?case
    apply (insert Collection)
    by (erule subtype_x_Collection'; erule subtype_x_Collection'; auto)
next
  case (Set \<rho>) show ?case
    apply (insert Set)
    by (erule subtype_x_Set'; erule subtype_x_Set'; auto)
next
  case (OrderedSet \<rho>) show ?case
    apply (insert OrderedSet)
    by (erule subtype_x_OrderedSet'; erule subtype_x_OrderedSet'; auto)
next
  case (Bag \<rho>) show ?case
    apply (insert Bag)
    by (erule subtype_x_Bag'; erule subtype_x_Bag'; auto)
next
  case (Sequence \<rho>) thus ?case
    apply (insert Sequence)
    by (erule subtype_x_Sequence'; erule subtype_x_Sequence'; auto)
next
  case (Tuple \<pi>) show ?case
    apply (insert Tuple)
    apply (erule subtype_x_Tuple'; erule subtype_x_Tuple'; auto)
    apply (rule_tac ?\<pi>="(fmmerge (\<squnion>) \<pi>' \<pi>'')" in subtype_x_Tuple_intro;
           simp add: fmrel_on_fset_fmmerge1)
    done
qed

instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end


(*
fun subtype_fun :: "type \<Rightarrow> type \<Rightarrow> bool" where
  "subtype_fun OclInvalid \<sigma> = (\<sigma> \<noteq> OclInvalid)"
| "subtype_fun OclVoid (Optional \<sigma>) = True"
| "subtype_fun OclVoid SupType = True"
| "subtype_fun OclVoid _ = False"
| "subtype_fun (Required \<tau>) (Required \<sigma>) = basic_subtype_fun \<tau> \<sigma>"
| "subtype_fun (Required \<tau>) (Optional \<sigma>) = (\<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Required \<tau>) SupType = True"
| "subtype_fun (Required \<tau>) _ = False"
| "subtype_fun (Optional \<tau>) (Optional \<sigma>) = basic_subtype_fun \<tau> \<sigma>"
| "subtype_fun (Optional \<tau>) SupType = True"
| "subtype_fun (Optional \<tau>) _ = False"
| "subtype_fun (Set \<tau>) (Set \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Set \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Set \<tau>) SupType = True"
| "subtype_fun (Set \<tau>) _ = False"
| "subtype_fun (OrderedSet \<tau>) (OrderedSet \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (OrderedSet \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (OrderedSet \<tau>) SupType = True"
| "subtype_fun (OrderedSet \<tau>) _ = False"
| "subtype_fun (Bag \<tau>) (Bag \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Bag \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Bag \<tau>) SupType = True"
| "subtype_fun (Bag \<tau>) _ = False"
| "subtype_fun (Sequence \<tau>) (Sequence \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Sequence \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Sequence \<tau>) SupType = True"
| "subtype_fun (Sequence \<tau>) _ = False"
| "subtype_fun (Collection \<tau>) (Collection \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Collection \<tau>) SupType = True"
| "subtype_fun (Collection \<tau>) _ = False"
| "subtype_fun SupType _ = False"


lemma less_type_code [code_abbrev, simp]:
  "subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  apply (rule iffI)
  apply (induct rule: subtype_fun.induct; auto)
  apply (induct \<tau> arbitrary: \<sigma>)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (erule subtype_Required_x; auto)
  using less_eq_basic_type_code less_basic_type_code apply auto[1]
  apply (erule subtype_Optional_x; simp)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  done

lemma less_eq_type_code [code_abbrev]:
  "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
  using le_less by auto


value "Optional OclAny \<sqsubset> SupType"
value "Collection (Optional OclAny) \<sqsubset> SupType"
value "Collection (Optional OclAny) < SupType"
value "Collection (Collection (Optional OclAny)) \<sqsubset> SupType"
value "Collection (Collection (Optional OclAny)) < SupType"
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
*)
end

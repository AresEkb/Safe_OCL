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
  apply (rule_tac ?f="direct_subtype" and ?xs="\<pi>" and ?ys="\<pi>'" in strict_subtuple_antisym; simp)
  done

instantiation type :: (order) order
begin

definition "less_type \<equiv> direct_subtype\<^sup>+\<^sup>+"

definition "less_eq_type \<equiv> direct_subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

lemma subtype_OclInvalid_x_intro' [intro]:
  "OclInvalid \<le> \<sigma>"
  unfolding less_eq_type_def
  apply (induct \<sigma>)
  apply (metis direct_subtype.intros(1) direct_subtype.intros(20) direct_subtype.intros(3) rtranclp.simps)
  apply simp
  apply auto[1]
  apply auto[1]
  apply (metis direct_subtype.intros(1) direct_subtype.intros(3) tranclp.simps tranclp_into_rtranclp)
  apply (rule_tac ?b="Set \<sigma>" in rtranclp.rtrancl_into_rtrancl)
  apply (metis (no_types, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(11) direct_subtype.intros(7) fun_preserve_morphism_composition)
  apply (simp add: direct_subtype.intros(16))
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(11) direct_subtype.intros(7) fun_preserve_morphism_composition)
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(12) direct_subtype.intros(8) fun_preserve_morphism_composition)
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(13) direct_subtype.intros(9) fun_preserve_morphism_composition)
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(14) direct_subtype.intros(10) fun_preserve_morphism_composition)
  by (simp add: direct_subtype.intros(22) r_into_rtranclp)

lemma subtype_OclInvalid_x_intro [intro]:
  "\<sigma> \<noteq> OclInvalid \<Longrightarrow> OclInvalid < \<sigma>"
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_OclInvalid_x_intro')


lemma subtype_x_OclInvalid_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> OclInvalid"
  unfolding less_eq_type_def
  by auto

lemma subtype_x_Required_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply auto
  by (rule fun_preserve_morphism_composition; auto)

lemma subtype_x_Optional_intro' [intro]:
  "\<tau> = OclVoid \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply auto
  apply (simp add: direct_subtype.intros(6) rtranclp_into_tranclp1 tranclp_into_rtranclp)
  by (rule fun_preserve_morphism_composition; auto)

lemma subtype_x_Set_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  apply (auto)
  unfolding less_eq_type_def
  by (rule fun_preserve_morphism_composition; auto)

lemma subtype_x_OrderedSet_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  apply (auto)
  unfolding less_eq_type_def
  by (rule fun_preserve_morphism_composition; auto)

lemma subtype_x_Bag_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  apply (auto)
  unfolding less_eq_type_def
  by (rule fun_preserve_morphism_composition[of direct_subtype]; auto)

lemma subtype_x_Sequence_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  apply (auto)
  unfolding less_eq_type_def
  by (rule fun_preserve_morphism_composition[of direct_subtype]; auto)

lemma fun_preserve:
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow>
   S\<^sup>+\<^sup>+ (f x) (g y)"
  apply (rule_tac ?b="f y" in rtranclp_into_tranclp1)
  apply (rule fun_preserve_morphism_composition[of R]; auto)
  by (simp)

lemma fun_preserve':
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (g y)"
  by (metis fun_preserve_morphism_composition rtranclp.rtrancl_into_rtrancl)
(*
lemma subtype_x_Collection_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  apply auto
  unfolding less_type_def less_eq_type_def
  apply (rule fun_preserve; auto)
  apply (rule fun_preserve; auto)
  apply (rule fun_preserve; auto)
  apply (rule fun_preserve; auto)
  apply (rule fun_preserve_morphism_composition'[of direct_subtype]; auto)
  done
*)
lemma subtype_x_Collection_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  apply auto
  unfolding less_type_def less_eq_type_def
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve'; auto)
  apply (rule fun_preserve_morphism_composition[of direct_subtype]; auto)
  done

lemma subtype_x_SupType_intro [intro]:
  "\<tau> \<noteq> SupType \<Longrightarrow> \<tau> < SupType"
  apply (induct \<tau>)
  apply auto[1]
  apply auto[1]
  apply auto[1]

  apply (simp add: less_type_def)
  apply (rule_tac ?y="OclAny[?]" in rtranclp_tranclp_tranclp)
  apply (simp add: direct_subtype.intros(3) r_into_rtranclp)
  apply (simp add: direct_subtype.intros(20) tranclp.r_into_trancl)

  apply (simp add: less_type_def)
  apply (rule_tac ?y="OclAny[1]" in rtranclp_tranclp_tranclp)
  apply (metis (mono_tags) less_eq_type_def subtype_x_OclAny_intro subtype_x_Required_intro'(2))
  apply (meson direct_subtype.intros(20) direct_subtype.intros(6) tranclp.r_into_trancl tranclp_into_tranclp2)

  apply (simp add: less_type_def)
  apply (rule_tac ?b="OclAny[?]" in rtranclp_into_tranclp1)
  apply (metis (mono_tags) less_eq_type_def subtype_x_OclAny_intro subtype_x_Optional_intro'(3))
  apply (simp add: direct_subtype.intros(20))

  apply (simp add: less_type_def tranclp_into_rtranclp)
  apply (smt direct_subtype.intros(15) direct_subtype.intros(21) fun_preserve_morphism_composition' tranclp.r_into_trancl tranclp.trancl_into_trancl)

  apply (simp add: less_type_def)
  apply (rule_tac ?b="Collection \<tau>" in tranclp_into_tranclp2)
  apply auto[1]
  apply (smt direct_subtype.intros(15) direct_subtype.intros(21) fun_preserve_morphism_composition' tranclp.r_into_trancl tranclp.trancl_into_trancl)

  apply (simp add: less_type_def)
  apply (rule_tac ?b="Collection \<tau>" in tranclp_into_tranclp2)
  apply auto[1]
  apply (smt direct_subtype.intros(15) direct_subtype.intros(21) fun_preserve_morphism_composition' tranclp.r_into_trancl tranclp.trancl_into_trancl)

  apply (simp add: less_type_def)
  apply (rule_tac ?b="Collection \<tau>" in tranclp_into_tranclp2)
  apply auto[1]
  apply (smt direct_subtype.intros(15) direct_subtype.intros(21) fun_preserve_morphism_composition' tranclp.r_into_trancl tranclp.trancl_into_trancl)

  apply (simp add: less_type_def)
  apply (rule_tac ?b="Collection \<tau>" in tranclp_into_tranclp2)
  apply auto[1]
  apply (smt direct_subtype.intros(15) direct_subtype.intros(21) fun_preserve_morphism_composition' tranclp.r_into_trancl tranclp.trancl_into_trancl)

  by (simp add: direct_subtype.intros(24) less_type_def tranclp.r_into_trancl)

lemma subtype_x_SupType_intro' [intro]:
  "\<tau> \<le> SupType"
  by (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def less_type_def subtype_x_SupType_intro)

(*** Elimination Rules ******************************************************)

lemma subtype_OclInvalid_x [elim]:
  "OclInvalid < \<sigma> \<Longrightarrow>
   (\<sigma> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Tuple \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: tranclp_induct; blast)

lemma subtype_OclVoid_x' [elim]:
  "OclVoid \<le> \<sigma> \<Longrightarrow>
   (\<sigma> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (induct rule: rtranclp_induct; blast)

lemma subtype_OclVoid_x [elim]:
  "OclVoid < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: tranclp_induct; blast)

lemma subtype_Collection_x [elim]:
  "Collection \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)[1]
  by (metis direct_subtype_Collection_x direct_subtype_SupType_x tranclp.trancl_into_trancl)

lemma subtype_Set_x' [elim]:
  "Set \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)
  by (erule direct_subtype.cases; auto; meson rtranclp.rtrancl_into_rtrancl)

lemma direct_subtype_preserve_Tuple:
  "direct_subtype\<^sup>+\<^sup>+ (Tuple x) (Tuple y) \<Longrightarrow>
   (\<lambda>x y. Tuple x \<sqsubset> Tuple y)\<^sup>+\<^sup>+ x y"
  apply (rule tranclp_fun_preserve_gen_1)
  apply (simp add: inj_def)
  unfolding rel_limited_under_def
  apply auto[1]
  apply (metis (mono_tags, lifting) direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.simps)
  by simp

(* Это что-то типа монотонности? *)
lemma Tuple_implies_Tuple:
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow> \<exists>\<xi>. \<sigma> = Tuple \<xi> \<or> \<sigma> = SupType"
  unfolding less_eq_type_def
  by (induct rule: rtranclp_induct; auto)

lemma Tuple_implies_TupleE:
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow> (\<And>\<xi>. \<sigma> = Tuple \<xi> \<or> \<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (induct rule: rtranclp_induct; auto)

lemma subtype_Tuple_x'':
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases \<sigma>)
  apply (metis (mono_tags))
  apply (metis (mono_tags) direct_subtype_x_OclInvalid less_eq_type_def rtranclp.simps type.distinct(37))
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  using Tuple_implies_Tuple apply fastforce
  by simp

lemma subtype_x_Required':
  "\<tau> < \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  by blast


lemma subtype_x_OclInvalid' [elim]:
  "\<tau> \<le> OclInvalid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (metis direct_subtype_x_OclInvalid rtranclp.cases)

lemma subtype_x_OclInvalid [elim]:
  "\<tau> < OclInvalid \<Longrightarrow> False"
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

lemma subtype_x_Optional''' [elim]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (erule direct_subtype.cases; auto simp add: converse_rtranclp_into_rtranclp less_eq_basic_type_def)

lemma Tuple_functor:
  "functor_under_rel (strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>)) direct_subtype Tuple"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  apply (metis (no_types, lifting) direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.cases)
  apply (meson injI type.inject(8))
  done

lemma subtype_Tuple_Tuple:
  "direct_subtype\<^sup>+\<^sup>+ (Tuple \<pi>) (Tuple \<xi>) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ \<pi> \<xi>"
  using Tuple_functor tranclp_fun_preserve_gen_1a by fastforce

lemma subtype_Tuple_Tuple':
  "(strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ \<pi> \<xi> \<Longrightarrow>
   acyclic_in direct_subtype (fmran' \<pi>) \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ \<pi> \<xi>"
  apply (induct rule: tranclp_induct)
  apply (metis (mono_tags, lifting) strict_subtuple_mono tranclp.r_into_trancl)
  using strict_subtuple_trans3 by blast

lemma subtype_Tuple_Tuple'':
  "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ \<pi> \<xi> \<Longrightarrow>
   strict_subtuple direct_subtype\<^sup>*\<^sup>* \<pi> \<xi>"
  unfolding tranclp_into_rtranclp2
  by simp

lemma subtype_Tuple_Tuple''':
  "direct_subtype\<^sup>+\<^sup>+ (Tuple \<pi>) (Tuple \<xi>) \<Longrightarrow>
   acyclic_in direct_subtype (fmran' \<pi>) \<Longrightarrow>
   strict_subtuple direct_subtype\<^sup>*\<^sup>* \<pi> \<xi>"
  by (metis (mono_tags, lifting) subtype_Tuple_Tuple subtype_Tuple_Tuple' subtype_Tuple_Tuple'')

lemma Required_functor:
  "functor_under_rel direct_basic_subtype direct_subtype Required"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Required rangeI tranclp.simps)

lemma Optional_functor:
  "functor_under_rel direct_basic_subtype direct_subtype Optional"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  apply (metis direct_subtype.intros(3) direct_subtype_x_OclInvalid direct_subtype_x_OclVoid tranclp.cases)
  by (metis (mono_tags) OCL_Types.subtype_x_Required' less_type_def type.distinct(25) type.distinct(55))

lemma Required_Optional_natural:
  "natural_under_rel direct_basic_subtype direct_subtype Required Optional"
  apply (auto simp add: natural_under_rel_def Required_functor Optional_functor direct_subtype.intros(6))
  apply (metis (mono_tags) OCL_Types.subtype_x_Required' less_type_def type.distinct(25) type.distinct(55))
  by (metis (mono_tags) OCL_Types.subtype_x_Optional''' direct_subtype_Required_x direct_subtype_x_OclInvalid direct_subtype_x_OclVoid less_eq_type_def tranclp.simps tranclp_into_rtranclp)

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

lemma Collection_functor:
  "functor_under_rel direct_subtype direct_subtype Collection"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis (mono_tags) OCL_Types.subtype_Collection_x direct_subtype_SupType_x less_type_def rangeI)

lemma Set_Collection_natural:
  "natural_under_rel direct_subtype direct_subtype Set Collection"
  apply (auto simp add: natural_under_rel_def Set_functor Collection_functor)
  apply (metis (mono_tags) OCL_Types.subtype_Collection_x less_type_def type.simps(20) type.simps(90))
  by (metis (mono_tags) OCL_Types.subtype_Set_x' direct_subtype_SupType_x less_eq_type_def tranclpD tranclp_into_rtranclp)


lemma subtype_x_Required'' [elim]:
  "\<tau> < \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_basic_type_def
  by (metis (mono_tags) Required_functor less_type_def subtype_x_Required' tranclp_fun_preserve_gen_1a)

lemma subtype_x_Required''' [elim]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply (induct rule: converse_rtranclp_induct)
  apply simp
  by (metis converse_rtranclp_into_rtranclp direct_subtype_x_OclInvalid direct_subtype_x_Required)

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

lemma subtype_Tuple_x':
  "Tuple \<pi> < \<sigma> \<Longrightarrow>
   acyclic_in direct_subtype (fmran' \<pi>) \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_eq_type_def
  apply (induct rule: tranclp_induct)
  apply (metis (no_types, lifting) direct_subtype_Tuple_x subtype_Tuple_Tuple''' tranclp.r_into_trancl)
  by (metis (no_types, lifting) direct_subtype_SupType_x direct_subtype_Tuple_x subtype_Tuple_Tuple''' tranclp.trancl_into_trancl)

lemma subtype_Tuple_x''':
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow>
   acyclic_in direct_subtype (fmran' \<pi>) \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (simp add: fmap.rel_refl)
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclp_into_tranclp1 subtype_Tuple_x')

lemma Tuple_implies_Tuple':
  "Tuple \<pi> < \<sigma> \<Longrightarrow> \<exists>\<xi>. \<sigma> = Tuple \<xi> \<or> \<sigma> = SupType"
  unfolding less_eq_type_def
  by (metis (mono_tags) OCL_Types.subtype_Tuple_x'' less_eq_type_def less_type_def tranclp_into_rtranclp)

lemma Tuple_implies_TupleE':
  "Tuple \<pi> < \<sigma> \<Longrightarrow> (\<And>\<xi>. \<sigma> = Tuple \<xi> \<or> \<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  using Tuple_implies_Tuple' by auto

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

lemma subtype_x_SupType [elim]:
  "\<tau> < SupType \<Longrightarrow> (\<tau> \<noteq> SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (mono_tags) direct_subtype_SupType_x less_type_def tranclpD)

(*** Properties *************************************************************)

lemma subtype_irrefl:
  "(\<tau> :: 'a type) < \<tau> \<Longrightarrow> False"
  apply (induct \<tau>, auto)
  by (metis (mono_tags) less_type_def subtype_Tuple_Tuple''')

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



abbreviation "tcf \<equiv> (\<lambda> v::(nat \<times> nat). (\<lambda> r::nat. snd v + r))"

interpretation tcf: comp_fun_commute tcf
proof 
  fix x y
  show "tcf y \<circ> tcf x = tcf x \<circ> tcf y"
  proof -
    fix z
    have "(tcf y \<circ> tcf x) z = snd y + snd x + z" by auto
    also have "(tcf x \<circ> tcf y) z = snd y + snd x + z" by auto
    ultimately have "(tcf y \<circ> tcf x) z = (tcf x \<circ> tcf y) z" by auto
    then show "(tcf y \<circ> tcf x) = (tcf x \<circ> tcf y)" by auto
  qed
qed

instantiation type :: (type) size 
begin

(*
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
*)

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

lemma ffold_rec_exp:
  assumes "k |\<in>| fmdom x"
    and "ky = (k, the (fmlookup (fmmap f x) k))"
  shows "ffold tcf 0 (fset_of_fmap (fmmap f x)) = 
        tcf ky (ffold tcf 0 ((fset_of_fmap (fmmap f x)) |-| {|ky|}))"
  using assms tcf.ffold_rec by auto

lemma elem_le_ffold:
  "k |\<in>| fmdom x \<Longrightarrow>
   f (the (fmlookup x k)) < Suc (ffold tcf 0 (fset_of_fmap (fmmap f x)))"
  by (subst ffold_rec_exp, auto)

lemma measure_cond [intro]:
  "k |\<in>| fmdom x \<Longrightarrow>
   size (the (fmlookup x k)) < size (Tuple x)"
  using elem_le_ffold by auto


instantiation type :: (semilattice_sup) semilattice_sup
begin

abbreviation
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else OclInvalid)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"

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
    of Tuple \<xi> \<Rightarrow> Tuple (supc (\<squnion>) \<pi> \<xi>)
     | OclInvalid \<Rightarrow> Tuple \<pi>
     | _ \<Rightarrow> SupType)"
| "SupType \<squnion> \<sigma> = SupType"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(xs, ys). size ys)")
  using measure_cond apply auto
  done

lemma OclVoid_less_eq_sup:
  "OclVoid \<le> OclVoid \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Required_less_eq_sup:
  "Required \<tau> \<le> Required \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; auto)
  by (simp add: subtype_x_Optional_intro'(2) subtype_x_Required_intro'(2))

lemma Optional_less_eq_sup:
  "Optional \<tau> \<le> Optional \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Set_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Set \<tau> \<le> Set \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma OrderedSet_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   OrderedSet \<tau> \<le> OrderedSet \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Bag_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Bag \<tau> \<le> Bag \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Sequence_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Sequence \<tau> \<le> Sequence \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Collection_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)
(*
lemma subtype_Tuple_x''':
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow>
   acyclic_in direct_subtype (fmran' \<pi>) \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (simp add: fmap.rel_refl)
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclp_into_tranclp1 subtype_Tuple_x')
*)
lemma subtype_x_Tuple_intro' [intro]:
  "\<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> \<tau> \<le> Tuple \<xi>"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply auto
  sorry

(*
abbreviation
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else OclInvalid)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
*)

lemma fmrestrict_fset_ffilter:
  "fmrestrict_fset (ffilter (\<lambda>k. k |\<in>| fmdom \<xi>) (fmdom \<pi>)) \<pi> =
   fmfilter (\<lambda>k. k |\<in>| fmdom \<xi>) \<pi>"
  by (metis ffmember_filter fmdom_notD fmfilter_alt_defs(5) fmfilter_cong option.distinct(1))

lemma fmran_fmmap_keys:
  "fmran (fmmap_keys (\<lambda>k x. g x y) xs) = (\<lambda>x. g x y) |`| fmran xs"
  sorry

lemma rel_fset_fmran_fmmap_keys:
  "(\<And>x y. x |\<in>| fmran xs \<Longrightarrow> f x (g x y)) \<Longrightarrow>
   rel_fset f (fmran xs) (fmran (fmmap_keys (\<lambda>k x. g x y) xs))"
  sorry

lemma fmrel_fmmap_keys:
  "(\<And>x y. x |\<in>| fmran xs \<Longrightarrow> f x (g x y)) \<Longrightarrow>
   fmrel f xs (fmmap_keys (\<lambda>k x. g x y) xs)"
  sorry

term fmrel_on_fset

lemma q:
  "(\<And>\<tau> \<sigma>. \<tau> |\<in>| fmran \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   fmrel (\<le>) \<pi> (fmmap_keys (\<lambda>k x. x \<squnion> y) \<pi>)"
  by (rule fmrel_fmmap_keys; auto)


lemma q:
  "(\<And>\<tau> \<sigma>. \<tau> |\<in>| fmran \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   fmrel (\<le>)
     (fmrestrict_fset
       (ffilter (\<lambda>k. k |\<in>| fmdom \<xi>) (fmdom \<pi>)) \<pi>)
     (fmmap_keys
       (\<lambda>k x. if (k |\<in>| fmdom \<xi>) then x \<squnion> the (fmlookup \<xi> k) else OclInvalid)
       (fmfilter (\<lambda>k. k |\<in>| fmdom \<xi>) \<pi>))"
  apply (rule fmrel_fmmap_keys)


lemma q:
  "fmrel (\<le>)
     (fmrestrict_fset
       (ffilter (\<lambda>k. k |\<in>| fmdom \<xi>) (fmdom \<pi>)) \<pi>)
     (supc (\<squnion>) \<pi> \<xi>)"


lemma q:
  "(\<And>\<tau> \<sigma>. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Tuple \<pi> \<le> Tuple (supc (\<squnion>) \<pi> \<xi>)"
  apply (rule subtype_x_Tuple_intro')
  apply auto[1]
  apply auto[1]

lemma Tuple_less_eq_sup:
  "(\<And>\<tau> \<sigma>. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Tuple \<pi> \<le> Tuple \<pi> \<squnion> \<sigma>"
  apply (cases \<sigma>)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  sorry

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  apply (induct \<tau> arbitrary: \<sigma>)
  apply simp
  apply (simp add: subtype_OclInvalid_x_intro')
  using OclVoid_less_eq_sup apply auto[1]
  using Required_less_eq_sup apply auto[1]
  using Optional_less_eq_sup apply auto[1]
  using Collection_less_eq_sup apply auto[1]
  using Set_less_eq_sup apply auto[1]
  using OrderedSet_less_eq_sup apply auto[1]
  using Bag_less_eq_sup apply auto[1]
  using Sequence_less_eq_sup apply auto[1]
  using Tuple_less_eq_sup apply auto[1]
  done

lemma OclVoid_sup_commut:
  "OclVoid \<squnion> \<sigma> = \<sigma> \<squnion> OclVoid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma OclInvalid_sup_commut:
  "OclInvalid \<squnion> \<sigma> = \<sigma> \<squnion> OclInvalid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma Required_sup_commut:
  "Required \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Required \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma Optional_sup_commut:
  "Optional \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Optional \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma Set_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Set \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Set \<tau>"
  by (cases \<sigma>; simp)

lemma OrderedSet_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   OrderedSet \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> OrderedSet \<tau>"
  by (cases \<sigma>; simp)

lemma Bag_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Bag \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Bag \<tau>"
  by (cases \<sigma>; simp)

lemma Sequence_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Sequence \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Sequence \<tau>"
  by (cases \<sigma>; simp)

lemma Collection_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Collection \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Collection \<tau>"
  by (cases \<sigma>; simp)

lemma Sup_sup_commut:
  "SupType \<squnion> \<sigma> = \<sigma> \<squnion> SupType"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma Tuple_sup_commut:
  "(\<And>xa \<sigma>. xa \<in> fmran' x \<Longrightarrow> xa \<squnion> \<sigma> = \<sigma> \<squnion> xa) \<Longrightarrow>
   Tuple x \<squnion> \<sigma> = \<sigma> \<squnion> Tuple x"
  apply (cases \<sigma>; simp add: less_eq_type_def)
  sorry

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a type"
  apply (induct \<tau> arbitrary: \<sigma>)
  using Sup_sup_commut apply auto[1]
  using OclInvalid_sup_commut apply auto[1]
  using OclVoid_sup_commut apply auto[1]
  using Required_sup_commut apply auto[1]
  using Optional_sup_commut apply auto[1]
  using Collection_sup_commut apply auto[1]
  using Set_sup_commut apply auto[1]
  using OrderedSet_sup_commut apply auto[1]
  using Bag_sup_commut apply auto[1]
  using Sequence_sup_commut apply auto[1]
  using Tuple_sup_commut apply auto[1]
  done

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  apply (induct \<rho> arbitrary: \<tau> \<sigma>)
  apply (simp add: subtype_x_SupType_intro')
  apply fastforce
  apply (erule subtype_x_OclVoid'; erule subtype_x_OclVoid'; auto)
  apply (erule subtype_x_Required'''; erule subtype_x_Required'''; auto)
  apply (erule subtype_x_Optional'''; erule subtype_x_Optional'''; auto)
  using le_sup_iff apply blast
  apply (erule subtype_x_Collection'; erule subtype_x_Collection'; auto)
  apply (erule subtype_x_Set'; erule subtype_x_Set'; auto)
  apply (erule subtype_x_OrderedSet'; erule subtype_x_OrderedSet'; auto)
  apply (erule subtype_x_Bag'; erule subtype_x_Bag'; auto)
  apply (erule subtype_x_Sequence'; erule subtype_x_Sequence'; auto)
  sorry

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

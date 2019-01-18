(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>OCL Types\<close>
theory OCL_Types
  imports OCL_Basic_Types Tuple
begin

(*** Types ******************************************************************)

section \<open>Definition of Types and a Subtype Relation\<close>

text \<open>
  Tuples should have a string key.\<close>

datatype (plugins del: "size") 'a type =
  OclInvalid
| OclVoid
| Required "'a basic_type" ("_[1]" [1000] 1000)
| Optional "'a basic_type" ("_[?]" [1000] 1000)
| Set "'a type"
| OrderedSet "'a type"
| Bag "'a type"
| Sequence "'a type"
| Collection "'a type"
| Tuple "literal \<rightharpoonup>\<^sub>f 'a type"
| SupType

instantiation type :: (type) size
begin

primrec size_type :: "'a type \<Rightarrow> nat" where
  "size_type OclInvalid = 0"
| "size_type OclVoid = 0"
| "size_type (Required _) = 0"
| "size_type (Optional _) = 0"
| "size_type (Set x) = Suc (size_type x)"
| "size_type (OrderedSet x) = Suc (size_type x)"
| "size_type (Bag x) = Suc (size_type x)"
| "size_type (Sequence x) = Suc (size_type x)"
| "size_type (Collection x) = Suc (size_type x)"
| "size_type (Tuple xs) = Suc (ffold tcf 0 (fset_of_fmap (fmmap size_type xs)))"
| "size_type SupType = 0"

instance ..

end

inductive subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" ("_ \<sqsubset> _" [65, 65] 65) where
  "OclInvalid \<sqsubset> OclVoid"
| "OclInvalid \<sqsubset> \<sigma>[1]"
| "OclVoid \<sqsubset> \<sigma>[?]"
| "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<tau>[1] \<sqsubset> \<sigma>[1]"
| "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<tau>[?] \<sqsubset> \<sigma>[?]"
| "\<tau>[1] \<sqsubset> \<tau>[?]"
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
| "OclInvalid \<sqsubset> Tuple \<xi>"
| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> SupType"

declare subtype.intros [intro!]

inductive_cases subtype_x_OclInvalid [elim!]: "\<tau> \<sqsubset> OclInvalid"
inductive_cases subtype_x_OclVoid [elim!]: "\<tau> \<sqsubset> OclVoid"
inductive_cases subtype_x_Required [elim!]: "\<tau> \<sqsubset> \<sigma>[1]"
inductive_cases subtype_x_Optional [elim!]: "\<tau> \<sqsubset> \<sigma>[?]"
inductive_cases subtype_x_Set [elim!]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases subtype_x_OrderedSet [elim!]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases subtype_x_Bag [elim!]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases subtype_x_Sequence [elim!]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases subtype_x_Collection [elim!]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases subtype_x_Tuple [elim!]: "\<tau> \<sqsubset> Tuple \<pi>"
inductive_cases subtype_x_SupType [elim!]: "\<tau> \<sqsubset> SupType"

inductive_cases subtype_Collection_x [elim!]: "Collection \<tau> \<sqsubset> \<sigma>"
inductive_cases subtype_SupType_x [elim!]: "SupType \<sqsubset> \<sigma>"

lemma subtype_antisym:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset> \<tau> \<Longrightarrow>
   False"
  apply (induct rule: subtype.induct)
  using basic_subtype_asym apply auto
  by (rule_tac ?f="subtype" and ?xm="\<pi>" and ?ym="\<pi>'" in strict_subtuple_antisym; simp)

(*** Constructors Bijectivity on Transitive Closures ************************)

section \<open>Constructors Bijectivity on Transitive Closures\<close>

lemma Required_bij_on_trancl [simp]:
  "bij_on_trancl subtype Required"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma not_subtype_Optional_Required:
  "subtype\<^sup>+\<^sup>+ \<tau>[?] \<sigma> \<Longrightarrow> \<sigma> = \<rho>[1] \<Longrightarrow> P"
  apply (induct arbitrary: \<rho> rule: tranclp_induct, auto)
  using tranclp.cases by fastforce

lemma Optional_bij_on_trancl [simp]:
  "bij_on_trancl subtype Optional"
  apply (auto simp add: inj_def)
  apply (metis subtype.intros(3) subtype_x_OclInvalid
               subtype_x_OclVoid tranclp.cases)
  using not_subtype_Optional_Required by blast

lemma Set_bij_on_trancl [simp]:
  "bij_on_trancl subtype Set"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma OrderedSet_bij_on_trancl [simp]:
  "bij_on_trancl subtype OrderedSet"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Bag_bij_on_trancl [simp]:
  "bij_on_trancl subtype Bag"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Sequence_bij_on_trancl [simp]:
  "bij_on_trancl subtype Sequence"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma subtype_tranclp_Collection_x:
  "subtype\<^sup>+\<^sup>+ (Collection \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> subtype\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct, auto)
  by (metis subtype_Collection_x subtype_SupType_x
            tranclp.trancl_into_trancl)

lemma Collection_bij_on_trancl [simp]:
  "bij_on_trancl subtype Collection"
  apply (auto simp add: inj_def)
  using subtype_tranclp_Collection_x by auto

lemma Tuple_bij_on_trancl [simp]:
  "bij_on_trancl subtype Tuple"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

(*** Partial Order of Types *************************************************)

section \<open>Partial Order of Types\<close>

instantiation type :: (order) order
begin

definition "(<) \<equiv> subtype\<^sup>+\<^sup>+"

definition "(\<le>) \<equiv> subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

subsection \<open>Introduction Rules\<close>

lemma type_less_eq_OclInvalid_x_intro [intro]:
  "OclInvalid \<le> \<sigma>"
  unfolding less_eq_type_def
proof (induct \<sigma>)
  case OclInvalid show ?case by simp 
next
  case OclVoid show ?case by (rule r_into_rtranclp; auto)
next
  case (Required x) show ?case by (rule r_into_rtranclp; auto)
next
  case (Optional x) show ?case
    by (meson subtype.intros(1) subtype.intros(3)
          r_into_rtranclp rtranclp.rtrancl_into_rtrancl)
next
  case (Set \<sigma>) thus ?case
    by (rule_tac ?b="Set OclInvalid" in converse_rtranclp_into_rtranclp, auto)
       (rule_tac ?R="subtype" and ?f="Set" in preserve_rtranclp; auto)
next
  case (OrderedSet \<sigma>) thus ?case
    by (rule_tac ?b="OrderedSet OclInvalid" in converse_rtranclp_into_rtranclp, auto)
       (rule_tac ?R="subtype" and ?f="OrderedSet" in preserve_rtranclp; auto)
next
  case (Bag \<sigma>) thus ?case
    by (rule_tac ?b="Bag OclInvalid" in converse_rtranclp_into_rtranclp, auto)
       (rule_tac ?R="subtype" and ?f="Bag" in preserve_rtranclp; auto)
next
  case (Sequence \<sigma>) thus ?case
    by (rule_tac ?b="Sequence OclInvalid" in converse_rtranclp_into_rtranclp, auto)
       (rule_tac ?R="subtype" and ?f="Sequence" in preserve_rtranclp; auto)
next
  case (Collection \<sigma>) show ?case
    apply (rule_tac ?b="Set \<sigma>" in rtranclp.rtrancl_into_rtrancl)
    apply (rule_tac ?b="Set OclInvalid" in converse_rtranclp_into_rtranclp, auto)
    apply (rule_tac ?R="subtype" and ?f="Set" in preserve_rtranclp;
           auto simp add: Collection.hyps)
    done
next
  case (Tuple x) show ?case by (rule r_into_rtranclp; auto)
next
  case SupType thus ?case
    by (metis (mono_tags) subtype.intros(1) subtype.intros(20)
          subtype.intros(3) rtranclp.simps) 
qed

lemma type_less_eq_x_Required_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  unfolding less_eq_type_def less_eq_basic_type_def
  by (simp) (rule preserve_rtranclp; auto)

lemma type_less_eq_x_Optional_intro [intro]:
  "\<tau> = OclVoid \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  unfolding less_eq_type_def less_eq_basic_type_def
  apply auto
  apply (rule rtranclp.rtrancl_into_rtrancl; auto)
  apply (rule preserve_rtranclp[of basic_subtype]; auto)
  done

lemma type_less_eq_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  unfolding less_eq_type_def
  by (simp) (rule preserve_rtranclp; auto)

lemma type_less_eq_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  unfolding less_eq_type_def
  by (simp) (rule preserve_rtranclp; auto)

lemma type_less_eq_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  unfolding less_eq_type_def
  by (simp) (rule preserve_rtranclp; auto)

lemma type_less_eq_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  unfolding less_eq_type_def
  by (simp) (rule preserve_rtranclp; auto)

lemma type_less_eq_x_Collection_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  unfolding less_type_def less_eq_type_def
  apply simp_all
  apply (rule preserve_rtranclp'; auto)
  apply (rule preserve_rtranclp'; auto)
  apply (rule preserve_rtranclp'; auto)
  apply (rule preserve_rtranclp'; auto)
  apply (rule preserve_rtranclp[of subtype]; auto)
  done

lemma fun_or_eq_refl [intro]:
  "reflp (\<lambda>x y. x = y \<or> f x y)"
  by (simp add: reflpI)

lemma type_less_eq_x_Tuple_intro [intro]:
  assumes "\<tau> = Tuple \<pi>"
      and "subtuple (\<le>) \<pi> \<xi>"
    shows "\<tau> \<le> Tuple \<xi>"
proof -
  have "subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>)\<^sup>*\<^sup>* \<pi> \<xi>"
    using assms(2) less_eq_type_def by auto
  hence "subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>)\<^sup>+\<^sup>+ \<pi> \<xi>"
    by auto
  hence "(subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by (simp) (rule subtuple_to_trancl; auto)
  hence "(subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>))\<^sup>*\<^sup>* \<pi> \<xi>"
    by simp
  thus ?thesis
    unfolding less_eq_type_def
    using assms(1) apply simp
    by (smt subtype.intros(23) preserve_rtranclp rtranclp_eq_rtranclp)
qed

lemma type_less_eq_x_SupType_intro [intro]:
  "\<tau> \<noteq> SupType \<Longrightarrow> \<tau> \<le> SupType"
  unfolding less_eq_type_def
proof (induct \<tau>)
  case OclInvalid thus ?case
    by (metis (mono_tags) OCL_Types.type_less_eq_OclInvalid_x_intro less_eq_type_def)
next
  case OclVoid thus ?case
    by (meson subtype.intros(20) subtype.intros(3)
          rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl)
next
  case (Required x) thus ?case
    apply (rule_tac ?y="OclAny[1]" in rtranclp_trans)
    apply (metis (mono_tags) less_eq_type_def type_less_eq_x_OclAny_intro
                             type_less_eq_x_Required_intro)
    by (meson converse_rtranclp_into_rtranclp subtype.intros(20)
              subtype.intros(6) r_into_rtranclp)
next
  case (Optional x) thus ?case
    apply (rule_tac ?y="OclAny[?]" in rtranclp_trans)
    apply (metis (mono_tags) less_eq_type_def type_less_eq_x_OclAny_intro
                             type_less_eq_x_Optional_intro(3))
    by (simp add: subtype.intros(20) r_into_rtranclp)
next
  case (Set \<tau>)
  hence "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis Nitpick.rtranclp_unfold preserve_rtranclp subtype.intros(15))
  moreover have "subtype\<^sup>+\<^sup>+ (Set \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    by (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
       (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
next
  case (OrderedSet \<tau>)
  hence "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis Nitpick.rtranclp_unfold preserve_rtranclp subtype.intros(15))
  moreover have "subtype\<^sup>+\<^sup>+ (OrderedSet \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    by (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
       (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
next
  case (Bag \<tau>)
  hence "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis Nitpick.rtranclp_unfold preserve_rtranclp subtype.intros(15))
  moreover have "subtype\<^sup>+\<^sup>+ (Bag \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    by (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
       (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
next
case (Sequence \<tau>)
  hence "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection SupType)"
    by (metis Nitpick.rtranclp_unfold preserve_rtranclp subtype.intros(15))
  moreover have "subtype\<^sup>+\<^sup>+ (Sequence \<tau>) (Collection \<tau>)" by auto
  ultimately show ?case
    by (rule_tac ?y="Collection \<tau>" in rtranclp_trans, simp)
       (rule_tac ?b="Collection SupType" in rtranclp.rtrancl_into_rtrancl; auto)
next
  case (Collection \<tau>)
  have "subtype\<^sup>+\<^sup>+ (Collection SupType) SupType"
    by (simp add: subtype.intros(21) less_type_def tranclp.r_into_trancl)
  with Collection.hyps show ?case
    by (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def
              less_type_def type_less_eq_x_Collection_intro(5) tranclp_trans)
next
  case (Tuple x)
  thus ?case
    by (simp add: subtype.intros(24) r_into_rtranclp)
next
  case SupType
  thus ?case by auto
qed

(*** Strict Elimination Rules ***********************************************)

subsection \<open>Strict Elimination Rules\<close>

lemma type_less_x_OclInvalid [elim!]:
  "\<tau> < OclInvalid \<Longrightarrow> P"
  unfolding less_type_def
  by (metis subtype_x_OclInvalid tranclp.cases)

lemma type_less_x_OclVoid [elim!]:
  "\<tau> < OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (metis (mono_tags, lifting) subtype_x_OclVoid
        less_type_def type_less_x_OclInvalid tranclp.simps)

lemma type_less_x_Required [elim!]:
  assumes "\<tau> < \<sigma>[1]"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OclInvalid \<or> \<tau> = \<rho>[1]"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[1] < \<sigma>[1] \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_basic_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

(*
lemma type_less_x_Optional [elim!]:
  assumes "\<tau> < \<sigma>[?]"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where
    "\<tau> = OclInvalid \<or> \<tau> = OclVoid \<or> \<tau> = \<rho>[1] \<or> \<tau> = \<rho>[?]"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[1] < \<sigma>[?] \<Longrightarrow> \<tau> \<le> \<sigma>"
    unfolding less_type_def less_eq_basic_type_def
    apply (drule tranclpD, auto)
    apply (erule subtype.cases, auto)
    sorry
  moreover have "\<And>\<tau> \<sigma>. \<tau>[?] < \<sigma>[?] \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_basic_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
*)
lemma type_less_x_Optional [elim!]:
  "\<tau> < \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis subtype_x_Optional eq_refl less_basic_type_def tranclp.r_into_trancl)
  apply (erule subtype.cases; auto)
  apply (simp add: converse_rtranclp_into_rtranclp less_eq_basic_type_def)
  by (simp add: less_basic_type_def tranclp_into_tranclp2)

lemma type_less_x_Set [elim!]:
  assumes "\<tau> < Set \<sigma>"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OclInvalid \<or> \<tau> = Set \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Set \<tau> < Set \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OrderedSet [elim!]:
  assumes "\<tau> < OrderedSet \<sigma>"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OclInvalid \<or> \<tau> = OrderedSet \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. OrderedSet \<tau> < OrderedSet \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Bag [elim!]:
  assumes "\<tau> < Bag \<sigma>"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OclInvalid \<or> \<tau> = Bag \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Bag \<tau> < Bag \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Sequence [elim!]:
  assumes "\<tau> < Sequence \<sigma>"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OclInvalid \<or> \<tau> = Sequence \<rho>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Sequence \<tau> < Sequence \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Collection [elim!]:
  "\<tau> < Collection \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply (metis (mono_tags) Nitpick.rtranclp_unfold
          subtype_x_Collection less_eq_type_def tranclp.r_into_trancl)
  by (erule subtype.cases;
      auto simp add: converse_rtranclp_into_rtranclp less_eq_type_def
                     tranclp_into_tranclp2 tranclp_into_rtranclp)

text \<open>
  We'll be able to remove the acyclicity assumption only after
  we prove that the subtype relation is acyclic.\<close>

lemma type_less_x_Tuple':
  assumes "\<tau> < Tuple \<xi>"
      and "acyclicP_on (fmran' \<xi>) subtype"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<pi> where "\<tau> = OclInvalid \<or> \<tau> = Tuple \<pi>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover from assms(2) have
    "\<And>\<pi>. Tuple \<pi> < Tuple \<xi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi>"
    unfolding less_type_def less_eq_type_def
    by (rule_tac ?f="Tuple" in strict_subtuple_rtranclp_intro; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_SupType [elim!]:
  "\<tau> < SupType \<Longrightarrow> (\<tau> \<noteq> SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (drule tranclpD, auto)

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma subtype_irrefl:
  "\<tau> < \<tau> \<Longrightarrow> False"
  for \<tau> :: "'a type"
  apply (induct \<tau>, auto)
  apply (erule type_less_x_Tuple', auto)
  unfolding less_type_def tranclp_unfold
  by auto

lemma subtype_acyclic:
  "acyclicP subtype"
  apply (rule acyclicI)
  apply (simp add: trancl_def)
  by (metis (mono_tags) OCL_Types.less_type_def OCL_Types.subtype_irrefl)

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
  by (metis (mono_tags, lifting) less_eq_type_def
      less_le_not_le_type less_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  done

end

(*** Non-strict Elimination Rules *******************************************)

subsection \<open>Non-strict Elimination Rules\<close>

lemma type_less_eq_x_OclInvalid [elim!]:
  "\<tau> \<le> OclInvalid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_OclVoid [elim!]:
  "\<tau> \<le> OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Required [elim!]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Optional [elim!]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq, auto)

lemma type_less_eq_x_Set [elim!]:
   "\<tau> \<le> Set \<sigma> \<Longrightarrow>
    (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_OrderedSet [elim!]:
   "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
    (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
    (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Bag [elim!]:
   "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
    (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Sequence [elim!]:
   "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
    (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Collection [elim!]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_x_Tuple [elim!]:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (erule type_less_x_Tuple')
  by (meson acyclic_def subtype_acyclic)

lemma type_less_eq_x_Tuple [elim!]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule le_imp_less_or_eq, auto)
  by (simp add: fmap.rel_refl fmrel_to_subtuple)

(*** Upper Semilattice of Types *********************************************)

section \<open>Upper Semilattice of Types\<close>

instantiation type :: (semilattice_sup) semilattice_sup
begin

fun sup_type where
  "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "OclVoid \<squnion> \<sigma> = (case \<sigma>
    of OclVoid \<Rightarrow> OclVoid
     | OclInvalid \<Rightarrow> OclVoid
     | \<rho>[1] \<Rightarrow> \<rho>[?]
     | \<rho>[?] \<Rightarrow> \<rho>[?]
     | _ \<Rightarrow> SupType)"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> \<tau>[1]
     | OclVoid \<Rightarrow> \<tau>[?]
     | \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[1]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> \<tau>[?]
     | OclVoid \<Rightarrow> \<tau>[?]
     | \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> SupType)"
| "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> Set \<tau>
     | Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> OrderedSet \<tau>
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> Bag \<tau>
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> Sequence \<tau>
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> Collection \<tau>
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Tuple \<pi> \<squnion> \<sigma> = (case \<sigma>
    of OclInvalid \<Rightarrow> Tuple \<pi>
     | Tuple \<xi> \<Rightarrow> Tuple (fmmerge_fun (\<squnion>) \<pi> \<xi>)
     | _ \<Rightarrow> SupType)"
| "SupType \<squnion> \<sigma> = SupType"

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case OclInvalid show ?case by auto 
  case OclVoid show ?case by (induct \<sigma>; auto)
  case (Required x) show ?case by (induct \<sigma>; auto simp add:
        type_less_eq_x_Optional_intro(2) type_less_eq_x_Required_intro)
  case (Optional x) show ?case by (induct \<sigma>; auto)
  case (Set \<tau>) thus ?case by (induct \<sigma>; auto)
  case (OrderedSet \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Bag \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Sequence \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Collection \<tau>) thus ?case by (induct \<sigma>; auto)
next
  case (Tuple \<pi>)
  also have Tuple_less_eq_sup:
    "(\<And>\<tau> \<sigma>. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
     Tuple \<pi> \<le> Tuple \<pi> \<squnion> \<sigma>"
    by (cases \<sigma>, auto)
  ultimately show ?case by (cases \<sigma>, auto)
next
  case SupType show ?case by simp
qed

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case OclInvalid show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case OclVoid show ?case by (cases \<sigma>; simp add: less_eq_type_def)
  case (Required \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Optional \<tau>) show ?case by (cases \<sigma>; simp add: sup_commute)
  case (Set \<tau>) thus ?case by (cases \<sigma>; simp)
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Bag \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; simp)
  case (Collection \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Tuple \<pi>) thus ?case
    apply (cases \<sigma>; simp add: less_eq_type_def)
    using fmmerge_commut by blast
next
  case SupType show ?case by (cases \<sigma>; simp add: less_eq_type_def)
qed

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
proof (induct \<rho> arbitrary: \<tau> \<sigma>)
  case OclInvalid thus ?case by auto
next
  case OclVoid show ?case
    apply (insert OclVoid)
    by (erule type_less_eq_x_OclVoid; erule type_less_eq_x_OclVoid; auto)
next
  case (Required x) show ?case
    apply (insert Required)
    by (erule type_less_eq_x_Required; erule type_less_eq_x_Required; auto)
next
  case (Optional x) show ?case
    apply (insert Optional)
    apply (erule type_less_eq_x_Optional; erule type_less_eq_x_Optional; auto)
    using le_sup_iff by blast
next
  case (Set \<rho>) show ?case
    apply (insert Set)
    by (erule type_less_eq_x_Set; erule type_less_eq_x_Set; auto)
next
  case (OrderedSet \<rho>) show ?case
    apply (insert OrderedSet)
    by (erule type_less_eq_x_OrderedSet; erule type_less_eq_x_OrderedSet; auto)
next
  case (Bag \<rho>) show ?case
    apply (insert Bag)
    by (erule type_less_eq_x_Bag; erule type_less_eq_x_Bag; auto)
next
  case (Sequence \<rho>) thus ?case
    apply (insert Sequence)
    by (erule type_less_eq_x_Sequence; erule type_less_eq_x_Sequence; auto)
next
  case (Collection \<rho>) show ?case
    apply (insert Collection)
    by (erule type_less_eq_x_Collection; erule type_less_eq_x_Collection; auto)
next
  case (Tuple \<pi>) show ?case
    apply (insert Tuple)
    apply (erule type_less_eq_x_Tuple; erule type_less_eq_x_Tuple; auto)
    by (rule_tac ?\<pi>="(fmmerge (\<squnion>) \<pi>' \<pi>'')" in type_less_eq_x_Tuple_intro;
        simp add: fmrel_on_fset_fmmerge1)
next
  case SupType show ?case using eq_refl by auto
qed

instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end

(*** Helper Relations *******************************************************)

section \<open>Helper Relations\<close>

abbreviation simeq_type ("(_/ \<simeq> _)"  [51, 51] 50) where
  "\<tau> \<simeq> \<sigma> \<equiv> \<tau> = \<sigma>[1] \<or> \<tau> = \<sigma>[?]"

abbreviation simeq_between_type ("(_/ \<simeq> _\<midarrow>_)"  [51, 51, 51] 50) where
  "\<tau> \<simeq> \<sigma>\<midarrow>\<rho> \<equiv> \<sigma>[1] \<le> \<tau> \<and> \<tau> \<le> \<rho>[?]"

inductive class_of where
  "class_of (ObjectType cls)[1] cls"
| "class_of (ObjectType cls)[?] cls"

inductive element_type where
  "element_type (Set \<tau>) \<tau>"
| "element_type (OrderedSet \<tau>) \<tau>"
| "element_type (Bag \<tau>) \<tau>"
| "element_type (Sequence \<tau>) \<tau>"
| "element_type (Collection \<tau>) \<tau>"

inductive update_element_type where
  "update_element_type (Set _) \<tau> (Set \<tau>)"
| "update_element_type (OrderedSet _) \<tau> (OrderedSet \<tau>)"
| "update_element_type (Bag _) \<tau> (Bag \<tau>)"
| "update_element_type (Sequence _) \<tau> (Sequence \<tau>)"
| "update_element_type (Collection _) \<tau> (Collection \<tau>)"

inductive to_unique_collection where
  "to_unique_collection (Set \<tau>) (Set \<tau>)"
| "to_unique_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection (Bag \<tau>) (Set \<tau>)"
| "to_unique_collection (Sequence \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection (Collection \<tau>) (Set \<tau>)"

inductive to_nonunique_collection where
  "to_nonunique_collection (Set \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (OrderedSet \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection (Bag \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Sequence \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection (Collection \<tau>) (Bag \<tau>)"

inductive to_ordered_collection where
  "to_ordered_collection (Set \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (Bag \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Sequence \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Collection \<tau>) (Sequence \<tau>)"

fun to_single_type where
  "to_single_type OclInvalid = OclInvalid"
| "to_single_type OclVoid = OclVoid"
| "to_single_type \<tau>[1] = \<tau>[1]"
| "to_single_type \<tau>[?] = \<tau>[?]"
| "to_single_type (Set \<tau>) = to_single_type \<tau>"
| "to_single_type (OrderedSet \<tau>) = to_single_type \<tau>"
| "to_single_type (Bag \<tau>) = to_single_type \<tau>"
| "to_single_type (Sequence \<tau>) = to_single_type \<tau>"
| "to_single_type (Collection \<tau>) = to_single_type \<tau>"
| "to_single_type (Tuple \<pi>) = Tuple \<pi>"
| "to_single_type SupType = SupType"

fun to_optional_type where
  "to_optional_type OclInvalid = OclVoid"
| "to_optional_type OclVoid = OclVoid"
| "to_optional_type \<tau>[1] = \<tau>[?]"
| "to_optional_type \<tau>[?] = \<tau>[?]"
| "to_optional_type (Set \<tau>) = Set (to_optional_type \<tau>)"
| "to_optional_type (OrderedSet \<tau>) = OrderedSet (to_optional_type \<tau>)"
| "to_optional_type (Bag \<tau>) = Bag (to_optional_type \<tau>)"
| "to_optional_type (Sequence \<tau>) = Sequence (to_optional_type \<tau>)"
| "to_optional_type (Collection \<tau>) = Collection (to_optional_type \<tau>)"
| "to_optional_type (Tuple \<pi>) = Tuple (fmmap to_optional_type \<pi>)"
| "to_optional_type SupType = SupType"

inductive strict_subcollection where
  "\<sigma> < \<tau> \<Longrightarrow>
   strict_subcollection (Set \<tau>) \<sigma> (Set \<sigma>)"
| "\<sigma> < \<tau> \<Longrightarrow>
   strict_subcollection (OrderedSet \<tau>) \<sigma> (OrderedSet \<sigma>)"
| "\<sigma> < \<tau> \<Longrightarrow>
   strict_subcollection (Bag \<tau>) \<sigma> (Bag \<sigma>)"
| "\<sigma> < \<tau> \<Longrightarrow>
   strict_subcollection (Sequence \<tau>) \<sigma> (Sequence \<sigma>)"
| "\<sigma> < \<tau> \<Longrightarrow>
   strict_subcollection (Collection \<tau>) \<sigma> (Collection \<sigma>)"

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred subtype .

function subtype_fun :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" where
  "subtype_fun OclInvalid \<sigma> = (\<sigma> \<noteq> OclInvalid)"
| "subtype_fun OclVoid \<sigma> = (case \<sigma>
    of _[?] \<Rightarrow> True
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Required \<tau>) \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Optional \<tau>) \<sigma> = (case \<sigma>
    of \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Set \<tau>) \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (OrderedSet \<tau>) \<sigma> = (case \<sigma>
    of OrderedSet \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Bag \<tau>) \<sigma> = (case \<sigma>
    of Bag \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Sequence \<tau>) \<sigma> = (case \<sigma>
    of Sequence \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Collection \<tau>) \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Tuple \<pi>) \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> strict_subtuple_fun (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>
     | SupType \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun SupType _ = False"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(xs, ys). size ys)";
      auto simp add: elem_le_ffold' fmran'I)

lemma less_eq_type_code [code_abbrev, simp]:
  "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
proof
  show "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>"
  proof (induct \<sigma> arbitrary: \<tau>)
    case OclInvalid thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case OclVoid thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (Required x) thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (Optional x) thus ?case
      apply (auto)
      by (erule subtype_fun.elims;
          auto simp add: type_less_eq_x_Optional_intro(2)
                         type_less_eq_x_Required_intro)
  next
    case (Set \<sigma>) thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (OrderedSet \<sigma>) thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (Bag \<sigma>) thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (Sequence \<sigma>) thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (Collection \<sigma>) thus ?case
      by (auto) (erule subtype_fun.elims;
                 auto simp add: type_less_eq_x_Collection_intro)
  next
    case (Tuple x) thus ?case
      apply (auto)
      apply (erule subtype_fun.elims; auto)
      by (metis (mono_tags, lifting) subtuple_mono type_less_eq_x_Tuple_intro)
  next
    case SupType thus ?case
      by auto
  qed
  show "\<tau> \<le> \<sigma> \<Longrightarrow> \<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>"
  proof (induct \<sigma> arbitrary: \<tau>)
    case OclInvalid thus ?case by auto
  next
    case OclVoid thus ?case by auto
  next
    case (Required x) thus ?case
      apply (insert Required)
      by (erule type_less_eq_x_Required; auto simp add: dual_order.order_iff_strict)
  next
    case (Optional x) thus ?case
      apply (insert Optional)
      by (erule type_less_eq_x_Optional; auto simp add: dual_order.order_iff_strict)
  next
    case (Set \<sigma>) thus ?case
      apply (insert Set)
      by (erule type_less_eq_x_Set, auto)
  next
    case (OrderedSet \<sigma>) thus ?case
      apply (insert OrderedSet)
      by (erule type_less_eq_x_OrderedSet, auto)
  next
    case (Bag \<sigma>) thus ?case
      apply (insert Bag)
      by (erule type_less_eq_x_Bag, auto)
  next
    case (Sequence \<sigma>) thus ?case
      apply (insert Sequence)
      by (erule type_less_eq_x_Sequence, auto)
  next
    case (Collection \<sigma>) thus ?case
      apply (insert Collection)
      by (erule type_less_eq_x_Collection, auto)
  next
    case (Tuple x) thus ?case
      apply (insert Tuple)
      apply (erule type_less_eq_x_Tuple; auto)
      by (smt subtuple_mono)
  next
    case SupType thus ?case by (cases \<tau>, auto)
  qed
qed

lemma subtype_fun_irrefl:
  "\<not> subtype_fun \<tau> \<tau>"
  by (induct \<tau>, auto)

lemma less_type_code [code_abbrev, simp]:
  "subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  unfolding less_le
  apply auto
  using less_eq_type_code apply blast
  apply (erule subtype_fun.elims; auto simp add: subtype_fun_irrefl)
  using less_eq_type_code by blast

(*** Test Cases *************************************************************)

section \<open>Test Cases\<close>

subsection \<open>Positive Cases\<close>

value "Integer[?] < (SupType :: classes1 type)"
value "Collection Real[?] < (SupType :: classes1 type)"
value "Set (Collection Boolean[1]) < (SupType :: classes1 type)"
value "Set (Bag Boolean[1]) < Set (Collection Boolean[?] :: classes1 type)"
value "Tuple (fmap_of_list [(STR ''1'', Boolean[1] :: classes1 type), (STR ''2'', Integer[1])]) <
       Tuple (fmap_of_list [(STR ''1'', Boolean[?] :: classes1 type)])"

value "Integer[1] \<squnion> Real[?] :: classes1 type" \<comment> \<open>Real[?]\<close>
value "Set Integer[1] \<squnion> Set (Real[1] :: classes1 type)" \<comment> \<open>Set Real[1]\<close>
value "Set Integer[1] \<squnion> Bag (Boolean[?] :: classes1 type)" \<comment> \<open>Collection OclAny[?]\<close>
value "Set Integer[1] \<squnion> Real[1] :: classes1 type" \<comment> \<open>SupType\<close>

subsection \<open>Negative Cases\<close>

value "OrderedSet Boolean[1] < Set (Boolean[1] :: classes1 type)"

end

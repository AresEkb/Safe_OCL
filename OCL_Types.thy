(*  Title:       Safe OCL
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Types\<close>
theory OCL_Types
  imports OCL_Basic_Types Errorable Tuple
begin

(*** Types ******************************************************************)

section \<open>Definition of Types and a Subtype Relation\<close>

type_synonym telem = String.literal

datatype (plugins del: "size") 'a type =
  Required "'a basic_type" ("_[1]" [1000] 1000)
| Optional "'a basic_type" ("_[?]" [1000] 1000)
| Set "'a type"
| OrderedSet "'a type"
| Bag "'a type"
| Sequence "'a type"
| Collection "'a type"
| Tuple "telem \<rightharpoonup>\<^sub>f 'a type"
| OclSuper

text \<open>
  We define the @{term OclInvalid} type separately, because we
  do not need types like @{term "Set(OclInvalid)"} in the theory.
  An @{term "OclVoid[1]"} type is not equal to @{term OclInvalid}.
  For example, @{term "Set(OclVoid[1])"} is a valid type of the
  following expression:

\<^verbatim>\<open>Set{null}->excluding(null)\<close>\<close>

definition "OclInvalid :: 'a type\<^sub>\<bottom> \<equiv> \<bottom>"

instantiation type :: (type) size
begin

primrec size_type :: "'a type \<Rightarrow> nat" where
  "size_type (Required _) = 0"
| "size_type (Optional _) = 0"
| "size_type (Set x) = Suc (size_type x)"
| "size_type (OrderedSet x) = Suc (size_type x)"
| "size_type (Bag x) = Suc (size_type x)"
| "size_type (Sequence x) = Suc (size_type x)"
| "size_type (Collection x) = Suc (size_type x)"
| "size_type (Tuple xs) = Suc (ffold tcf 0 (fset_of_fmap (fmmap size_type xs)))"
| "size_type OclSuper = 0"

instance ..

end

inductive subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" ("_ \<sqsubset> _" [65, 65] 65) where
  "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<tau>[1] \<sqsubset> \<sigma>[1]"
| "\<tau> \<sqsubset>\<^sub>B \<sigma> \<Longrightarrow> \<tau>[?] \<sqsubset> \<sigma>[?]"
| "\<tau>[1] \<sqsubset> \<tau>[?]"
| "OclAny[?] \<sqsubset> OclSuper"

| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"
| "Collection OclSuper \<sqsubset> OclSuper"

| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> OclSuper"

declare subtype.intros [intro!]

inductive_cases subtype_x_Required [elim!]: "\<tau> \<sqsubset> \<sigma>[1]"
inductive_cases subtype_x_Optional [elim!]: "\<tau> \<sqsubset> \<sigma>[?]"
inductive_cases subtype_x_Set [elim!]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases subtype_x_OrderedSet [elim!]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases subtype_x_Bag [elim!]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases subtype_x_Sequence [elim!]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases subtype_x_Collection [elim!]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases subtype_x_Tuple [elim!]: "\<tau> \<sqsubset> Tuple \<pi>"
inductive_cases subtype_x_OclSuper [elim!]: "\<tau> \<sqsubset> OclSuper"

inductive_cases subtype_Collection_x [elim!]: "Collection \<tau> \<sqsubset> \<sigma>"
inductive_cases subtype_OclSuper_x [elim!]: "OclSuper \<sqsubset> \<sigma>"

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
  by (auto simp add: inj_def)

lemma not_subtype_Optional_Required:
  "subtype\<^sup>+\<^sup>+ \<tau>[?] \<sigma> \<Longrightarrow> \<sigma> = \<rho>[1] \<Longrightarrow> P"
  by (induct arbitrary: \<rho> rule: tranclp_induct; auto)

lemma Optional_bij_on_trancl [simp]:
  "bij_on_trancl subtype Optional"
  apply (auto simp add: inj_def)
  using not_subtype_Optional_Required by blast

lemma Set_bij_on_trancl [simp]:
  "bij_on_trancl subtype Set"
  by (auto simp add: inj_def)

lemma OrderedSet_bij_on_trancl [simp]:
  "bij_on_trancl subtype OrderedSet"
  by (auto simp add: inj_def)

lemma Bag_bij_on_trancl [simp]:
  "bij_on_trancl subtype Bag"
  by (auto simp add: inj_def)

lemma Sequence_bij_on_trancl [simp]:
  "bij_on_trancl subtype Sequence"
  by (auto simp add: inj_def)

lemma subtype_tranclp_Collection_x:
  "subtype\<^sup>+\<^sup>+ (Collection \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> subtype\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclSuper \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct, auto)
  by (metis subtype_Collection_x subtype_OclSuper_x
            tranclp.trancl_into_trancl)

lemma Collection_bij_on_trancl [simp]:
  "bij_on_trancl subtype Collection"
  apply (auto simp add: inj_def)
  using subtype_tranclp_Collection_x by auto

lemma Tuple_bij_on_trancl [simp]:
  "bij_on_trancl subtype Tuple"
  by (auto simp add: inj_def)

(*** Partial Order of Types *************************************************)

section \<open>Partial Order of Types\<close>

instantiation type :: (order) order
begin

definition "(<) \<equiv> subtype\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

subsection \<open>Introduction Rules\<close>

lemma type_less_eq_x_Required_intro [intro]:
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  unfolding less_eq_type_def less_eq_basic_type_def
  by (simp) (rule preserve_rtranclp; auto)

lemma type_less_eq_x_Optional_intro [intro]:
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
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>))\<^sup>*\<^sup>* \<pi> \<xi>"
    by (smt mono_rtranclp rtranclp_eq_rtranclp)
  thus ?thesis
    unfolding less_eq_type_def
    using assms(1) apply simp
    by (rule preserve_rtranclp[of "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>)"]; auto)
qed

lemma type_less_eq_x_OclSuper_intro [intro]:
  "\<tau> \<le> OclSuper"
  unfolding less_eq_type_def
proof (induct \<tau>)
  case (Required x)
  have "subtype\<^sup>*\<^sup>* x[1] OclAny[1]" using less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* OclAny[1] OclAny[?]" by auto
  also have "subtype\<^sup>*\<^sup>* OclAny[?] OclSuper" by auto
  finally show ?case by auto
next
  case (Optional x)
  have "subtype\<^sup>*\<^sup>* x[?] OclAny[?]" using less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* OclAny[?] OclSuper" by auto
  finally show ?case by auto
next
  case (Set \<tau>)
  have "subtype\<^sup>*\<^sup>* (Set \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    using Set.hyps less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (OrderedSet \<tau>)
  have "subtype\<^sup>*\<^sup>* (OrderedSet \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    using OrderedSet.hyps less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Bag \<tau>)
  have "subtype\<^sup>*\<^sup>* (Bag \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    using Bag.hyps less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Sequence \<tau>)
  have "subtype\<^sup>*\<^sup>* (Sequence \<tau>) (Collection \<tau>)" by auto
  also have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    using Sequence.hyps less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Collection \<tau>)
  have "subtype\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclSuper)"
    using Collection.hyps less_eq_type_def by auto
  also have "subtype\<^sup>*\<^sup>* (Collection OclSuper) OclSuper" by auto
  finally show ?case by auto
next
  case (Tuple x) thus ?case by auto
next
  case OclSuper thus ?case by auto
qed

(*** Strict Elimination Rules ***********************************************)

subsection \<open>Strict Elimination Rules\<close>

lemma type_less_x_OclVoid [elim!]:
  "\<tau> < OclVoid \<Longrightarrow> P"
  unfolding less_type_def
  using tranclp.cases by fastforce

lemma type_less_x_Required [elim!]:
  assumes "\<tau> < \<sigma>[1]"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = \<rho>[1]"
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
      and "\<tau> = OclVoid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where
    "\<tau> = OclVoid \<or> \<tau> = \<rho>[1] \<or> \<tau> = \<rho>[?]"
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
      and "\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Set \<rho>"
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
      and "\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OrderedSet \<rho>"
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
      and "\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Bag \<rho>"
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
      and "\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Sequence \<rho>"
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
      and "\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<pi> where "\<tau> = Tuple \<pi>"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover from assms(2) have
    "\<And>\<pi>. Tuple \<pi> < Tuple \<xi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi>"
    unfolding less_type_def less_eq_type_def
    by (rule_tac ?f="Tuple" in strict_subtuple_rtranclp_intro; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OclSuper [elim!]:
  "\<tau> < OclSuper \<Longrightarrow> (\<tau> \<noteq> OclSuper \<Longrightarrow> P) \<Longrightarrow> P"
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
proof
  show "\<tau> < \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
    apply (auto simp add: less_type_def less_eq_type_def)
    by (metis (mono_tags) subtype_irrefl less_type_def tranclp_rtranclp_tranclp)
  show "\<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> < \<sigma>"
    apply (auto simp add: less_type_def less_eq_type_def)
    by (metis rtranclpD)
qed

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type"
  unfolding less_eq_type_def by simp

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  unfolding less_eq_type_def by simp

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  unfolding less_eq_type_def less_type_def
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

lemma type_less_eq_x_Required [elim!]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Optional [elim!]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq, auto)

lemma type_less_eq_x_Set [elim!]:
   "\<tau> \<le> Set \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_OrderedSet [elim!]:
   "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Bag [elim!]:
   "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Sequence [elim!]:
   "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
    (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Collection [elim!]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_x_Tuple [elim!]:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (erule type_less_x_Tuple')
  by (meson acyclic_def subtype_acyclic)

lemma type_less_eq_x_Tuple [elim!]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule le_imp_less_or_eq, auto)
  by (simp add: fmap.rel_refl fmrel_to_subtuple)

(*** Upper Semilattice of Types *********************************************)

section \<open>Upper Semilattice of Types\<close>

instantiation type :: (semilattice_sup) semilattice_sup
begin

fun sup_type where
  "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[1]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> OclSuper)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | \<rho>[?] \<Rightarrow> (\<tau> \<squnion> \<rho>)[?]
     | _ \<Rightarrow> OclSuper)"
| "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> OclSuper)"
| "Tuple \<pi> \<squnion> \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> Tuple (fmmerge_fun (\<squnion>) \<pi> \<xi>)
     | _ \<Rightarrow> OclSuper)"
| "OclSuper \<squnion> \<sigma> = OclSuper"

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
  case (Required x) show ?case by (induct \<sigma>;
    auto simp add: type_less_eq_x_Optional_intro(2) type_less_eq_x_Required_intro)
  case (Optional x) show ?case by (induct \<sigma>; auto)
  case (Set \<tau>) thus ?case by (induct \<sigma>; auto)
  case (OrderedSet \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Bag \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Sequence \<tau>) thus ?case by (induct \<sigma>; auto)
  case (Collection \<tau>) thus ?case by (induct \<sigma>; auto)
next
  case (Tuple \<pi>)
  moreover have Tuple_less_eq_sup:
    "(\<And>\<tau> \<sigma>. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
     Tuple \<pi> \<le> Tuple \<pi> \<squnion> \<sigma>"
    by (cases \<sigma>, auto)
  ultimately show ?case by (cases \<sigma>, auto)
next
  case OclSuper show ?case by simp
qed

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof (induct \<tau> arbitrary: \<sigma>)
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
  case OclSuper show ?case by (cases \<sigma>; simp add: less_eq_type_def)
qed

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
proof (induct \<rho> arbitrary: \<tau> \<sigma>)
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
  case OclSuper show ?case using eq_refl by auto
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
  "class_of \<langle>\<C>\<rangle>\<^sub>\<T>[1] \<C>"
| "class_of \<langle>\<C>\<rangle>\<^sub>\<T>[?] \<C>"

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
  "to_single_type \<tau>[1] = \<tau>[1]"
| "to_single_type \<tau>[?] = \<tau>[?]"
| "to_single_type (Set \<tau>) = to_single_type \<tau>"
| "to_single_type (OrderedSet \<tau>) = to_single_type \<tau>"
| "to_single_type (Bag \<tau>) = to_single_type \<tau>"
| "to_single_type (Sequence \<tau>) = to_single_type \<tau>"
| "to_single_type (Collection \<tau>) = to_single_type \<tau>"
| "to_single_type (Tuple \<pi>) = Tuple \<pi>"
| "to_single_type OclSuper = OclSuper"

fun to_required_type where
  "to_required_type \<tau>[1] = \<tau>[1]"
| "to_required_type \<tau>[?] = \<tau>[1]"
| "to_required_type (Set \<tau>) = Set (to_required_type \<tau>)"
| "to_required_type (OrderedSet \<tau>) = OrderedSet (to_required_type \<tau>)"
| "to_required_type (Bag \<tau>) = Bag (to_required_type \<tau>)"
| "to_required_type (Sequence \<tau>) = Sequence (to_required_type \<tau>)"
| "to_required_type (Collection \<tau>) = Collection (to_required_type \<tau>)"
| "to_required_type (Tuple \<pi>) = Tuple (fmmap to_required_type \<pi>)"
| "to_required_type OclSuper = OclSuper"

fun to_optional_type where
  "to_optional_type \<tau>[1] = \<tau>[?]"
| "to_optional_type \<tau>[?] = \<tau>[?]"
| "to_optional_type (Set \<tau>) = Set (to_optional_type \<tau>)"
| "to_optional_type (OrderedSet \<tau>) = OrderedSet (to_optional_type \<tau>)"
| "to_optional_type (Bag \<tau>) = Bag (to_optional_type \<tau>)"
| "to_optional_type (Sequence \<tau>) = Sequence (to_optional_type \<tau>)"
| "to_optional_type (Collection \<tau>) = Collection (to_optional_type \<tau>)"
| "to_optional_type (Tuple \<pi>) = Tuple (fmmap to_optional_type \<pi>)"
| "to_optional_type OclSuper = OclSuper"

(*** Properties of Helper Relations *****************************************)

section \<open>Properties of Helper Relations\<close>

lemma class_of_det:
  "class_of \<tau> \<C> \<Longrightarrow>
   class_of \<tau> \<D> \<Longrightarrow> \<C> = \<D>"
  by (induct rule: class_of.induct; simp add: class_of.simps)

lemma element_type_det:
  "element_type \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   element_type \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: element_type.induct; simp add: element_type.simps)

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: update_element_type.induct; simp add: update_element_type.simps)

lemma to_unique_collection_det:
  "to_unique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_unique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_unique_collection.induct; simp add: to_unique_collection.simps)

lemma to_nonunique_collection_det:
  "to_nonunique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_nonunique_collection.induct; simp add: to_nonunique_collection.simps)

lemma to_ordered_collection_det:
  "to_ordered_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_ordered_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_ordered_collection.induct; simp add: to_ordered_collection.simps)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred subtype .

function subtype_fun :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" where
  "subtype_fun (Required \<tau>) \<sigma> = (case \<sigma>
    of \<rho>[1] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Optional \<tau>) \<sigma> = (case \<sigma>
    of \<rho>[?] \<Rightarrow> basic_subtype_fun \<tau> \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Set \<tau>) \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (OrderedSet \<tau>) \<sigma> = (case \<sigma>
    of OrderedSet \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Bag \<tau>) \<sigma> = (case \<sigma>
    of Bag \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Sequence \<tau>) \<sigma> = (case \<sigma>
    of Sequence \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Collection \<tau>) \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun (Tuple \<pi>) \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> strict_subtuple_fun (\<lambda>\<tau> \<sigma>. subtype_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>
     | OclSuper \<Rightarrow> True
     | _ \<Rightarrow> False)"
| "subtype_fun OclSuper _ = False"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(xs, ys). size ys)";
      auto simp add: elem_le_ffold' fmran'I)

lemma less_eq_type_code [code_abbrev, simp]:
  "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
proof
  show "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>"
  proof (induct \<sigma> arbitrary: \<tau>)
    case (Required x) thus ?case
      by (auto) (erule subtype_fun.elims; auto)
  next
    case (Optional x) thus ?case
      apply (auto)
      apply (erule subtype_fun.elims, auto)
      using dual_order.order_iff_strict by auto
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
    case OclSuper thus ?case
      by auto
  qed
  show "\<tau> \<le> \<sigma> \<Longrightarrow> \<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>"
  proof (induct \<sigma> arbitrary: \<tau>)
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
    case OclSuper thus ?case by (cases \<tau>, auto)
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

code_pred class_of .
code_pred element_type .
code_pred update_element_type .
code_pred to_unique_collection .
code_pred to_nonunique_collection .
code_pred to_ordered_collection .

end

(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
theory Transitive_Closure_Ext_Old
  imports Main "Transitive_Closure_Ext"
begin

definition "surj_on_trancl' R f \<equiv> (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"

definition "bij_on_trancl' R f \<equiv> inj f \<and> surj_on_trancl' R f"

definition "functor_under_rel R S f \<equiv>
  (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y) \<and> bij_on_trancl' S f"

definition natural_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "natural_under_rel R S f g \<equiv>
    functor_under_rel R S f \<and>
    functor_under_rel R S g \<and>
    (\<forall>x. S (f x) (g x)) \<and>
    (\<forall>x y. S (f x) (g y) \<longrightarrow> x \<noteq> y \<longrightarrow> R x y) \<and>
    (\<forall>x y. \<not> S\<^sup>+\<^sup>+ (g x) (f y)) \<and>
    (\<forall>x y z. S\<^sup>+\<^sup>+ (f x) y \<longrightarrow> S\<^sup>+\<^sup>+ y (g z) \<longrightarrow> (\<exists>u. y = f u \<or> y = g u))"

(* I guess after some improvements the following lemma could generalize current lemmas *)

lemma tranclp_fun_preserve1b:
  fixes f :: "'a \<Rightarrow> 'b"
    and g :: "'a \<Rightarrow> 'b"
    and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x y :: 'a
  assumes as_nat: "natural_under_rel R S f g"
      and as_x: "x \<noteq> y"
      and prem: "S\<^sup>+\<^sup>+ (f x) (g y)"
    shows "R\<^sup>+\<^sup>+ x y"
proof -
  obtain f' where f': "f' = the_inv_into UNIV f" by auto
  obtain g' where g': "g' = the_inv_into UNIV g" by auto
  obtain f'' where f'': "f'' = restrict f' (range f)" by auto
  obtain g'' where g'': "g'' = restrict g' (range g)" by auto
  obtain FR where FR: "FR = range f" by auto
  obtain GR where GR: "GR = range g" by auto
  obtain P where P: "P = (\<lambda>x y.
     (x \<in> FR \<and> y \<in> FR \<longrightarrow> R\<^sup>+\<^sup>+ (f'' x) (f'' y)) \<and>
     (x \<in> FR \<and> y \<in> GR \<longrightarrow> (f'' x) \<noteq> (g'' y) \<longrightarrow> R\<^sup>+\<^sup>+ (f'' x) (g'' y)) \<and>
     (x \<in> GR \<and> y \<in> FR \<longrightarrow> False) \<and>
     (x \<in> GR \<and> y \<in> GR \<longrightarrow> R\<^sup>+\<^sup>+ (g'' x) (g'' y)))" by auto
  from prem have major: "S\<^sup>+\<^sup>+ (f x) (g y)" by blast
  from as_nat have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
    apply (unfold P f' f'' g' g'' FR GR natural_under_rel_def functor_under_rel_def)
    apply (intro conjI)
    apply (simp_all add: bij_on_trancl'_def f_the_inv_into_f tranclp.r_into_trancl)
    apply blast
    done
(*    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    apply (rule conjI)
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    apply (rule conjI)
    apply blast
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    done*)
  from as_nat have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    apply (unfold f'' f' g'' g' P FR GR natural_under_rel_def functor_under_rel_def
            bij_on_trancl'_def surj_on_trancl'_def)
    apply (intro conjI)
    apply (elim conjE)
    apply (simp_all)

    sorry
(*    apply (metis (full_types) f_the_inv_into_f restrict_apply' reflect_tranclp_fun_preserve_gen_1a tranclp_trans)
    apply (rule conjI)
    apply (smt f_the_inv_into_f functor_under_rel_def rangeI tranclp_trans)
    apply (rule conjI)
    apply (metis rangeE tranclp_trans)
    apply (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    done*)
  from major cases_1 cases_2 have inv_conc: "P (f x) (g y)"
    apply (rule_tac ?x="f x" and ?y="g y" and ?r="S" in tranclp_trans_induct)
    apply (simp)
    apply blast
    by blast
  with as_nat as_x show ?thesis
    apply (simp add: P f' f'' g' g'' the_inv_f_f natural_under_rel_def)
    by (simp add: FR GR)
qed

lemma rtranclp_fun_preserve1b:
  "natural_under_rel R S f g \<Longrightarrow>
   S\<^sup>+\<^sup>+ (f x) (g y) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
  apply auto
  by (meson tranclp_fun_preserve1b)

lemma rtranclp_fun_preserve1b':
  "natural_under_rel R S f g \<Longrightarrow>
   f x \<noteq> g y \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (g y) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
  apply auto
  by (meson tranclp_fun_preserve1b)

(*
abbreviation "surj_on_trancl' R f g \<equiv>
  (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (g z) \<longrightarrow> y \<in> range f \<or> y \<in> range g)"

abbreviation "bij_on_trancl' R f g \<equiv> inj f \<and> inj g \<and> surj_on_trancl' R f g"

lemma q:
  "(\<And>x y. S (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   (\<And>x y. S (g x) (g y) \<Longrightarrow> R x y) \<Longrightarrow>
   (\<And>x y z. S\<^sup>+\<^sup>+ (f x) y \<Longrightarrow> S y (g z) \<Longrightarrow> y \<in> range f \<or> y \<in> range g) \<Longrightarrow>
   (\<And>x y. \<not> S\<^sup>+\<^sup>+ (g x) (f y)) \<Longrightarrow>
   bij_on_trancl S f \<Longrightarrow>
   bij_on_trancl S g \<Longrightarrow>
   S\<^sup>+\<^sup>+ (f x) (g y) \<Longrightarrow> R\<^sup>+\<^sup>+ x y"
  apply (rule reflect_tranclp[of S g])
  apply auto[1]
  apply auto[1]

lemma reflect_rtranclp':
  "(\<And>x y. S (g x) (g y) \<Longrightarrow> R x y) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   bij_on_trancl S f \<Longrightarrow>
   bij_on_trancl S g \<Longrightarrow>
   bij_on_trancl' S f g \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (g y) \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  apply (rule reflect_rtranclp[of S g])
  apply auto[1]
  apply auto[1]
(*  by (meson converse_rtranclp_into_rtranclp)*)

  thm converse_rtranclp_into_rtranclp

lemma reflect_rtranclp':
  "(\<And>x y. S (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   bij_on_trancl S g \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (g y) \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
*)
(*
lemma type_less_eq_x_Collection [elim]:
  assumes "\<tau> \<le> Collection \<sigma>"
      and "\<tau> = OclInvalid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  have "\<tau> \<le> Collection \<sigma>" by (simp add: assms(1))
  then obtain \<rho> where "\<tau> = OclInvalid \<or> \<tau> = Collection \<rho> \<or>
      \<tau> = Set \<rho> \<or> \<tau> = OrderedSet \<rho> \<or> \<tau> = Bag \<rho> \<or> \<tau> = Sequence \<rho>"
    unfolding less_eq_type_def
    by (induct rule: converse_rtranclp_induct; auto)
  from assms show ?thesis
    unfolding less_eq_type_def
    apply (erule subtype.cases)

  moreover have "\<And>\<tau> \<sigma>. Set \<tau> \<le> Collection \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>"
    unfolding less_eq_type_def
    apply (rule reflect_rtranclp, auto)
(*  moreover have "\<And>\<tau> \<sigma>. Collection \<tau> \<le> Collection \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>"
    unfolding less_eq_type_def
    by (rule reflect_rtranclp; auto)
  ultimately show ?thesis
    using assms by auto*)
qed
*)

end
theory Transitive_Closure_Ext_Old
  imports Main "Transitive_Closure_Ext"
begin

abbreviation "functor_under_rel R S f \<equiv>
  (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y) \<and> bij_on_trancl S f"

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
    apply (unfold P f' f'' g' g'' FR GR natural_under_rel_def)
    apply (rule conjI)
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    apply (rule conjI)
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    apply (rule conjI)
    apply blast
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    done
  from as_nat have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    apply (unfold f'' f' g'' g' P FR GR natural_under_rel_def)
    apply (rule conjI)
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

(* We don't use lists at now. But the following lemmas could be useful in future *)

lemma list_all2_rtrancl1:
  "(list_all2 P)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys"
  apply (induct rule: rtranclp_induct)
  apply (simp add: list.rel_refl)
  by (smt list_all2_trans rtranclp.rtrancl_into_rtrancl)

lemma list_all2_trancl1:
  "(list_all2 P)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 P\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (simp add: list.rel_mono_strong)
  by (smt list_all2_trans tranclp.trancl_into_trancl)

lemma list_all2_rtrancl2:
  assumes as_r: "(\<forall>x. P x x)" 
  shows "(list_all2 P\<^sup>*\<^sup>* ) xs ys \<Longrightarrow> (list_all2 P)\<^sup>*\<^sup>* xs ys"
proof(induction rule: list_all2_induct)
  case Nil then show ?case by simp
next
  case (Cons x xs y ys) show ?case
  proof -
    from as_r obtain zs where 
      lp_xs_zs: "(list_all2 P) xs zs" and lp_pp_xs_zs: "(list_all2 P)\<^sup>+\<^sup>+ zs ys"
      by (metis Cons.IH Nitpick.rtranclp_unfold list_all2_refl 
         tranclp.r_into_trancl)
    from Cons.hyps(1) have x_xs_y_zs: "(list_all2 P)\<^sup>*\<^sup>* (x#xs) (y#zs)"
    proof(induction rule: rtranclp_induct)
      case base then show ?case using as_r lp_xs_zs by blast
    next
      case (step y z) then show ?case 
        using as_r by (metis list.simps(11) list_all2_same rtranclp.simps)
    qed
    from lp_pp_xs_zs have "(list_all2 P)\<^sup>*\<^sup>* (y#zs) (y#ys)"
    proof(induction rule: tranclp_induct)
      case (base y) then show ?case using as_r by blast
    next
      case (step y z) then show ?case 
        using as_r by (simp add: rtranclp.rtrancl_into_rtrancl)
    qed
    with x_xs_y_zs show ?thesis by force
  qed
qed

lemma list_all2_trancl2:
  assumes as_r: "(\<forall>x. P x x)" 
  shows "(list_all2 P\<^sup>+\<^sup>+) xs ys \<Longrightarrow> (list_all2 P)\<^sup>+\<^sup>+ xs ys"
proof(induction rule: list_all2_induct)
  case Nil then show ?case
    by (simp add: tranclp.r_into_trancl)
next
  case (Cons x xs y ys) show ?case
  proof -
    from as_r obtain zs where 
      lp_xs_zs: "(list_all2 P) xs zs" and lp_pp_xs_zs: "(list_all2 P)\<^sup>+\<^sup>+ zs ys"
      using Cons.IH list_all2_refl by blast
    from Cons.hyps(1) have x_xs_y_zs: "(list_all2 P)\<^sup>+\<^sup>+ (x#xs) (y#zs)"
    proof(induction rule: tranclp_induct)
      case base then show ?case using as_r lp_xs_zs by blast
    next
      case (step y z) then show ?case
        using as_r by (metis list.rel_inject(2) list_all2_same tranclp.trancl_into_trancl)
    qed
    from lp_pp_xs_zs have "(list_all2 P)\<^sup>+\<^sup>+ (y#zs) (y#ys)"
    proof(induction rule: tranclp_induct)
      case (base y) then show ?case using as_r by blast
    next
      case (step y z) then show ?case
        using as_r
        by (metis list.rel_inject(2) tranclp.simps)
    qed
    with x_xs_y_zs show ?thesis by force
  qed
qed

end
theory Transitive_Closure_Ext
  imports
    Main
    "HOL-Library.FuncSet"
begin

abbreviation "acyclic_on xs R \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

lemma acyclic_alt:
  "acyclicP R \<Longrightarrow> R\<^sup>*\<^sup>* x y \<Longrightarrow> \<not> R y x"
  apply (auto simp add: acyclic_def Enum.rtranclp_rtrancl_eq)
  by (metis case_prodI mem_Collect_eq rtrancl_into_trancl2)
(*
definition rel_limited_under :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "rel_limited_under R A =
   (\<forall>x y z. R\<^sup>+\<^sup>+ x y \<longrightarrow> R y z \<longrightarrow> x \<in> A \<longrightarrow> z \<in> A \<longrightarrow> y \<in> A)"
*)

(*
 Похоже на это, но у меня более слабое условие
 https://proofwiki.org/wiki/Definition:Closed_Relation
 https://proofwiki.org/wiki/Definition:Transitive_with_Respect_to_a_Relation
 https://proofwiki.org/wiki/Definition:Closure_(Abstract_Algebra)/Algebraic_Structure
*)

definition rel_limited_under :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rel_limited_under R f =
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"

definition rel_limited_under'' :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rel_limited_under'' R f =
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R\<^sup>+\<^sup>+ y (f z) \<longrightarrow> y \<in> range f)"

lemma q:
  "R\<^sup>+\<^sup>+ y z \<Longrightarrow> R\<^sup>+\<^sup>+ x y \<Longrightarrow>
   (\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P y) \<Longrightarrow> P y"
  apply (erule tranclp_induct, auto)
  done

term "R\<inverse>\<inverse>"
(*
lemma q:
  assumes "(\<And>y. R\<^sup>+\<^sup>+ (f x) y \<Longrightarrow> R y (f z) \<Longrightarrow> y \<in> range f)"
      and "inj f"
      and "(\<forall>x y. S (f x) (f y) \<longrightarrow> R x y)"
  shows "R\<^sup>+\<^sup>+ (f x) y \<Longrightarrow>
   R\<^sup>+\<^sup>+ y (f z) \<Longrightarrow> y \<in> range f"
proof -
  obtain ya where "R\<^sup>+\<^sup>+ (f x) ya" and "R\<^sup>+\<^sup>+ ya (f z)" and "ya \<in> range f" apply auto


lemma q:
  "rel_limited_under R f \<Longrightarrow> rel_limited_under'' R f"
  unfolding rel_limited_under_def rel_limited_under''_def
  apply auto
proof -
  obtain ya where "R\<inverse>\<inverse> ya (f z)"
  apply (erule_tac ?x="f x" in q, auto)
*)
(*
definition rel_limited_under' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "rel_limited_under' R A =
   (\<forall>x y z. R\<^sup>+\<^sup>+ x y \<longrightarrow> R y z \<longrightarrow> x \<in> A \<longrightarrow> z \<in> A \<longrightarrow> y \<in> A)"

lemma q:
  "rel_limited_under R f = rel_limited_under' R (range f)"
  unfolding rel_limited_under_def rel_limited_under'_def
  by auto
*)
definition functor_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "functor_under_rel R S f \<equiv>
    rel_limited_under S f \<and>
    inj f \<and>
    (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y)"

lemma fun_preserve_morphism_composition':
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
      and "R\<^sup>+\<^sup>+ x y"
    shows "S\<^sup>+\<^sup>+ (f x) (f y)"
proof -
  obtain P where P: "P = (\<lambda>x y. S\<^sup>+\<^sup>+ (f x) (f y))" by auto
  obtain r where r: "r = (\<lambda>x y. S (f x) (f y))" by auto
  have major: "r\<^sup>+\<^sup>+ x y" by (insert assms r; erule tranclp_trans_induct; auto)
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y" by simp
  from P have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z" by auto
  from major cases_1 cases_2 have "P x y" by (rule tranclp_trans_induct, auto)
  with P show ?thesis by simp
qed

lemma fun_preserve_morphism_composition:
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (f y)"
  unfolding Nitpick.rtranclp_unfold
  by (metis fun_preserve_morphism_composition')

lemma tranclpD2:
  "R\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists>z. R\<^sup>*\<^sup>* x z \<and> R z y"
  by (metis rtranclp.rtrancl_refl tranclp.cases tranclp_into_rtranclp)
(*
lemma q12:
  assumes "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y)"
      and "R\<^sup>+\<^sup>+ x y"
      and "R\<^sup>+\<^sup>+ y z"
      and "P x"
      and "P z"
    shows "P y"
proof -
  obtain Q where "Q = P x \<longrightarrow> P z \<longrightarrow> P y" by auto
  obtain ya where "R\<^sup>+\<^sup>+ y ya" and "R ya z"
    apply (insert assms(3))
    apply (erule tranclp_induct)


lemma q12:
  assumes "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y)"
      and "R\<^sup>+\<^sup>+ x y"
      and "R\<^sup>+\<^sup>+ y z"
      and "P x"
      and "P z"
    shows "P y"
proof -
  have "P x \<longrightarrow> P z \<longrightarrow> P y"
    apply (insert assms)
  obtain ya where ""
*)

lemma q11:
  "R\<^sup>+\<^sup>+ y z \<Longrightarrow> R\<^sup>+\<^sup>+ x y \<Longrightarrow>
   (\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> (P x \<Longrightarrow> P z \<Longrightarrow> P y)) \<Longrightarrow>
   (P x \<longrightarrow> P z \<longrightarrow> P y)"
  apply (erule tranclp_induct, auto)
  by (meson tranclp_trans)

lemma q12:
  "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow>
   R\<^sup>+\<^sup>+ x y \<Longrightarrow> R\<^sup>+\<^sup>+ y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y"
  by (smt q11)

lemma tranclp_fun_preserve_gen_1a:
  assumes as_f: "functor_under_rel R S f"
      and prem: "S\<^sup>+\<^sup>+ (f x) (f y)"
  shows "R\<^sup>+\<^sup>+ x y"
proof -
  obtain B where B: "B = range f" by auto
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g B" by auto
  obtain P where P: "P = (\<lambda>x y. x \<in> B \<longrightarrow> y \<in> B \<longrightarrow> R\<^sup>+\<^sup>+ (gr x) (gr y))" by auto
  from prem have major: "S\<^sup>+\<^sup>+ (f x) (f y)" by blast
  from as_f have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
    unfolding B P g gr
    by (simp add: f_the_inv_into_f functor_under_rel_def tranclp.r_into_trancl)
  from as_f have "(\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> x \<in> B \<Longrightarrow> z \<in> B \<Longrightarrow> y \<in> B)"
    unfolding functor_under_rel_def rel_limited_under_def
    by (rule_tac ?z="z" in q12, auto simp add: B)
  with P have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding B
    by auto
  from major cases_1 cases_2 have "P (f x) (f y)"
    by (rule tranclp_trans_induct, auto)
  with P B as_f g gr show ?thesis
    by (simp add: functor_under_rel_def the_inv_f_f)
qed

lemma rtranclp_fun_preserve_gen_1a:
  "functor_under_rel R S f \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (f y) \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
  by (meson functor_under_rel_def inj_def tranclp_fun_preserve_gen_1a)


definition natural_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "natural_under_rel R S f g \<equiv>
    functor_under_rel R S f \<and>
    functor_under_rel R S g \<and>
    (\<forall>x. S (f x) (g x)) \<and>
    (\<forall>x y. S (f x) (g y) \<longrightarrow> x \<noteq> y \<longrightarrow> R x y) \<and>
    (\<forall>x y. \<not> S\<^sup>+\<^sup>+ (g x) (f y)) \<and>
    (\<forall>x y z. S\<^sup>+\<^sup>+ (f x) y \<longrightarrow> S\<^sup>+\<^sup>+ y (g z) \<longrightarrow> (\<exists>u. y = f u \<or> y = g u))"

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
    apply (unfold f'' f' g'' g' P FR GR natural_under_rel_def functor_under_rel_def)
    apply (rule conjI)
    apply (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    apply (rule conjI)
    apply (smt f_the_inv_into_f functor_under_rel_def rangeI tranclp_trans)
    apply (rule conjI)
    apply (metis rangeE tranclp_trans)
    apply (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    done
  from major cases_1 cases_2 have inv_conc: "P (f x) (g y)"
    apply (rule_tac ?x="f x" and ?y="g y" and ?r="S" in tranclp_trans_induct)
    apply (simp)
    apply blast
    by blast
  with as_nat as_x show ?thesis
    apply (simp add: P f' f'' g' g'' the_inv_f_f natural_under_rel_def functor_under_rel_def)
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
*)
lemma eq_trancl:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ x y =
   (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) x y"
  apply auto
  apply (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclpD rtranclp_idemp)
  apply (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl tranclp_into_rtranclp)
  done
(*
lemma tranclp_into_rtranclp2:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ x y = (\<lambda>x y. P x y)\<^sup>*\<^sup>* x y"
  apply auto
  apply (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclp_idemp tranclp_into_rtranclp) 
  apply (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl)
  done
*)
lemma tranclp_into_rtranclp2:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ = (\<lambda>x y. P x y)\<^sup>*\<^sup>*"
  apply (rule ext)
  apply (rule ext)
  apply auto
  apply (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclp_idemp tranclp_into_rtranclp) 
  apply (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl)
  done

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

lemma fun_preserve'':
  "(\<And>y. R (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x (f y) \<Longrightarrow>
   R\<^sup>*\<^sup>* x (g y)"
  by (simp add: rtranclp.rtrancl_into_rtrancl)

end
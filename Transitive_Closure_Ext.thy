theory Transitive_Closure_Ext
  imports Main "HOL-Library.FuncSet"
begin

(*** Base Properties ********************************************************)

abbreviation surj_on_trancl :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "surj_on_trancl R f \<equiv>
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"

abbreviation bij_on_trancl :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "bij_on_trancl R f \<equiv> inj f \<and> surj_on_trancl R f"

(*** Base Lemmas ************************************************************)

lemma tranclp_eq_rtranclp [simp]:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ = P\<^sup>*\<^sup>*"
  apply (intro ext; auto)
  apply (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclp_idemp tranclp_into_rtranclp)
  apply (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl)
  done

lemma rtranclp_eq_rtranclp [simp]:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>*\<^sup>* = P\<^sup>*\<^sup>*"
  by (metis reflclp_idemp reflclp_tranclp tranclp_eq_rtranclp)

lemma tranclp_tranclp_to_tranclp_r:
  assumes "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y)"
      and "R\<^sup>+\<^sup>+ x y"
      and "R\<^sup>+\<^sup>+ y z"
      and "P x"
      and "P z"
    shows "P y"
proof -
  have "(\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> P x \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow>
        R\<^sup>+\<^sup>+ y z \<Longrightarrow> R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x \<longrightarrow> P z \<longrightarrow> P y"
    apply (erule tranclp_induct, auto)
    by (meson tranclp_trans)
  thus ?thesis
    using assms by auto
qed

(*** Transitive Closure Preservation & Reflection ***************************)

lemma preserve_tranclp:
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

lemma preserve_rtranclp:
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (f y)"
  unfolding Nitpick.rtranclp_unfold
  by (metis preserve_tranclp)

lemma preserve_rtranclp':
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (g y)"
  by (metis preserve_rtranclp rtranclp.rtrancl_into_rtrancl)

lemma reflect_tranclp:
  assumes refl_f: "\<And>x y. S (f x) (f y) \<Longrightarrow> R x y"
      and bij_f: "bij_on_trancl S f"
      and prem: "S\<^sup>+\<^sup>+ (f x) (f y)"
  shows "R\<^sup>+\<^sup>+ x y"
proof -
  obtain B where B: "B = range f" by auto
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g B" by auto
  obtain P where P: "P = (\<lambda>x y. x \<in> B \<longrightarrow> y \<in> B \<longrightarrow> R\<^sup>+\<^sup>+ (gr x) (gr y))" by auto
  from prem have major: "S\<^sup>+\<^sup>+ (f x) (f y)" by blast
  from refl_f bij_f have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
    unfolding B P g gr
    by (simp add: f_the_inv_into_f tranclp.r_into_trancl)
  from refl_f bij_f have "(\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> x \<in> B \<Longrightarrow> z \<in> B \<Longrightarrow> y \<in> B)"
    unfolding B
    by (rule_tac ?z="z" in tranclp_tranclp_to_tranclp_r, auto, blast)
  with P have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding B
    by auto
  from major cases_1 cases_2 have "P (f x) (f y)"
    by (rule tranclp_trans_induct, auto)
  with P B g gr refl_f bij_f show ?thesis
    by (simp add: the_inv_f_f)
qed

lemma reflect_rtranclp:
  "(\<And>x y. S (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   bij_on_trancl S f \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (f y) \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
  by (metis (full_types) injD reflect_tranclp)

end

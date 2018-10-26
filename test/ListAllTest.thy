theory ListAllTest
  imports Main
begin

lemma list_all2_rtrancl1:
  "(list_all2 P)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys"
  apply (induct rule: rtranclp_induct)
  apply (simp add: list.rel_refl)
  by (smt list_all2_trans rtranclp.rtrancl_into_rtrancl)


lemma list_all2_rtrancl2:
  assumes as_r: "(\<forall>x. P x x)" 
  shows "(list_all2 P\<^sup>*\<^sup>*) xs ys \<Longrightarrow> (list_all2 P)\<^sup>*\<^sup>* xs ys"
proof(induction rule: list_all2_induct)
  case Nil then show ?case by simp
next
  case (Cons x xs y ys)
  show ?case
  proof -
    define Q where Q: "Q = (\<lambda> x y. (list_all2 P)\<^sup>*\<^sup>* (x#xs) (y#ys))"
    from as_r obtain zs where zs: "(list_all2 P) xs zs \<and> (list_all2 P)\<^sup>+\<^sup>+ zs ys"
      by (metis Cons.IH Nitpick.rtranclp_unfold list_all2_refl tranclp.simps)
    define R where R: "R = (\<lambda> y. (list_all2 P)\<^sup>*\<^sup>* (x#xs) (y#zs))"
    with as_r zs have R_case_1: "R x" by blast
    from as_r R have R_case_2: "\<And>a b. P\<^sup>*\<^sup>* x a \<Longrightarrow> P a b \<Longrightarrow> R a \<Longrightarrow> R b"
      by (metis list.simps(11) list_all2_same rtranclp.simps) 
    with rtranclp_induct Cons.hyps R_case_1 have R_y: "R y" by smt
    define S where S: "S = (\<lambda> ys. (list_all2 P)\<^sup>*\<^sup>* (y#zs) (y#ys))"
    with as_r have S_case_1: "\<And>ys. (list_all2 P) zs ys \<Longrightarrow> S ys" by blast
    from as_r S have S_case_2: 
      "\<And>as bs. (list_all2 P)\<^sup>+\<^sup>+ zs as \<Longrightarrow> (list_all2 P) as bs \<Longrightarrow> S as \<Longrightarrow> S bs"
      by (simp add: rtranclp.rtrancl_into_rtrancl)
    with tranclp_induct as_r zs S S_case_1 have "S ys" 
      by (smt list_all2_refl rtranclp.rtrancl_refl tranclp.r_into_trancl)
    with Q R_y R S have "Q x y" by force
    with Q show ?thesis by blast
  qed
qed

lemma list_all2_rtrancl1E:
  "(list_all2 R)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (list_all2 R\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: list_all2_rtrancl1)

(*
lemma list_all2_direct_subtype':
  assumes prem: "(list_all2 R)\<^sup>*\<^sup>* xs ys"
      and refl: "\<And>x. R x x"
  shows "(list_all2 R)\<^sup>*\<^sup>* (x # xs) (x # ys)"
proof -
  obtain r where r: "r = (\<lambda>xs ys. list_all2 R xs ys)" by auto
(*  obtain P where P: "P = (\<lambda>xs ys. case (xs, ys) of (x # xt, y # yt) \<Rightarrow> x = y \<longrightarrow> (list_all2 R)\<^sup>*\<^sup>* (xt) (yt) | _ \<Rightarrow> True)" by auto*)
  obtain P where P: "P = (\<lambda>xs ys. \<exists>x xt yt. xs = x # xt \<longrightarrow> ys = x # yt \<longrightarrow> (list_all2 R)\<^sup>*\<^sup>* (xt) (yt))" by auto
  from prem r have major: "r\<^sup>*\<^sup>* xs ys" by simp
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y"
    by (metis (no_types, lifting) case_prodI list.case_eq_if list.rel_sel r_into_rtranclp)
  from P have cases_2: "\<And>x y z. r\<^sup>*\<^sup>* x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>*\<^sup>* y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    apply auto
    done
  from major cases_1 cases_2 have inv_conc: "P (xs) (ys)"
    using P by auto
  with P show ?thesis
    apply auto
qed
*)

thm list_all2_Cons

lemma q:
  "(list_all2 P)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* (x # xs) (x # ys)"
  unfolding list_all2_Cons
  apply (induct rule: rtranclp_induct)
  apply simp
  apply (erule list_all2_rtrancl1E)
  apply (erule list_all2_induct)

lemma list_all2_rtrancl2':
  "(\<And>x. P x x) \<Longrightarrow>
   (\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* xs ys"
  by (smt list_all2_mono r_into_rtranclp rtranclp_induct)

lemma list_all2_rtrancl2':
  "(\<And>x. P x x) \<Longrightarrow>
   (\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* xs ys"
  apply (rule r_into_rtranclp)

  thm list_all2_mono

lemma list_all2_rtrancl2:
  "(\<And>x. P x x) \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* xs ys"
  unfolding list_all2_iff
  apply (auto)



lemma list_all2_rtrancl2:
  "(\<And>x. P x x) \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* xs ys"
  apply (erule list_all2_induct)
  apply simp




lemma list_all2_rtrancl2_example:
  "list_all2 (\<lambda>x y. x = y \<or> Suc x = y)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (list_all2 (\<lambda>x y. x = y \<or> Suc x = y))\<^sup>*\<^sup>* xs ys"
  nitpick

lemma list_all2_rtrancl2_example_0_2:
  "list_all2 (\<lambda>x y. x = y \<or> Suc x = y)\<^sup>*\<^sup>* [0] [2] \<Longrightarrow>
   (list_all2 (\<lambda>x y. x = y \<or> Suc x = y))\<^sup>*\<^sup>* [0] [2]"
  apply (rule_tac ?b="[1]" in converse_rtranclp_into_rtranclp; simp)
  apply (rule_tac ?b="[2]" in converse_rtranclp_into_rtranclp; simp)
  done

lemma list_all2_rtrancl2_example_0_2:
  "list_all2 (\<lambda>x y. x = y \<or> Suc x = y)\<^sup>*\<^sup>* [0,1] [2,1] \<Longrightarrow>
   (list_all2 (\<lambda>x y. x = y \<or> Suc x = y))\<^sup>*\<^sup>* [0,1] [2,1]"
  apply (rule_tac ?b="[1,1]" in converse_rtranclp_into_rtranclp; simp)
  apply (rule_tac ?b="[2,1]" in converse_rtranclp_into_rtranclp; simp)
  done

lemma list_all2_rtrancl2_example1:
  "list_all2 (\<lambda>x y. x = y \<or> Suc x = y)\<^sup>*\<^sup>* [0] [2]"
  apply (auto)
  apply (rule_tac ?b="1" in converse_rtranclp_into_rtranclp; simp)
  apply (rule_tac ?b="2" in converse_rtranclp_into_rtranclp; simp)
  done

lemma list_all2_rtrancl2_example2:
  "(list_all2 (\<lambda>x y. x = y \<or> Suc x = y))\<^sup>*\<^sup>* [0] [2]"
  apply (rule_tac ?b="[1]" in converse_rtranclp_into_rtranclp; simp)
  apply (rule_tac ?b="[2]" in converse_rtranclp_into_rtranclp; simp)
  done

lemma list_all2_rtrancl2_example:
  "list_all2 (\<lambda>x y. x = y \<or> Suc x = y)\<^sup>*\<^sup>* [0] [2] \<Longrightarrow>
   (list_all2 (\<lambda>x y. x = y \<or> Suc x = y))\<^sup>*\<^sup>* [0] [2]"
  apply (rule_tac ?b="[1]" in converse_rtranclp_into_rtranclp; simp)
  apply (rule_tac ?b="[2]" in converse_rtranclp_into_rtranclp; simp)
  done


thm list_all2_trans

lemma q:
  "list_all2 P x y \<Longrightarrow>
   list_all2 P y z \<Longrightarrow>
   list_all2 P z w \<Longrightarrow>
   list_all2 P w v \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* x v"



lemma q:
  "(list_all2 P)\<^sup>*\<^sup>* x y \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* x y"

lemma q:
  "list_all2 P\<^sup>*\<^sup>* x y \<Longrightarrow>
   (list_all2 P)\<^sup>*\<^sup>* x y"


end

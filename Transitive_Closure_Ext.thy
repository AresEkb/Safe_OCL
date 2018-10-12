theory Transitive_Closure_Ext
  imports
    Main
    "HOL-Library.FuncSet"
begin

lemma acyclic_alt:
  "acyclicP R \<Longrightarrow> R\<^sup>*\<^sup>* x y \<Longrightarrow> \<not> R y x"
  apply (auto simp add: acyclic_def Enum.rtranclp_rtrancl_eq)
  by (metis case_prodI mem_Collect_eq rtrancl_into_trancl2)

definition rel_limited_under :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "rel_limited_under R A =
   (\<forall>x y z. R\<^sup>+\<^sup>+ x y \<longrightarrow> R y z \<longrightarrow> x \<in> A \<longrightarrow> z \<in> A \<longrightarrow> y \<in> A)"

definition rel_limited_under2 :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rel_limited_under2 R f =
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"

lemma q:
  "(\<forall>x y. R (f x) (f y) \<longrightarrow> R x y) \<Longrightarrow>
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"
  nitpick

lemma q:
  "rel_limited_under2 R f =
   rel_limited_under R (range f)"
  using rel_limited_under2_def rel_limited_under_def by fastforce

(*
  R = S = subtype\<^sup>*\<^sup>*
  Все эти штуки лучше определять через классы и локали
*)
definition funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "funct R S f \<equiv> (\<forall>x y. R x y \<longrightarrow> S (f x) (f y))"

definition faithful_funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "faithful_funct R S f \<equiv> funct R S f \<and> inj f"

definition full_funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "full_funct R S f \<equiv> funct R S f \<and> (\<forall>x y z. S (f x) y \<longrightarrow> S y (f z) \<longrightarrow> y \<in> range f)"
(*  "full_funct R S f \<equiv> funct R S f \<and> (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y)"*)

definition fully_faithful_funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "fully_faithful_funct R S f \<equiv> full_funct R S f \<and> faithful_funct R S f"
(*
lemma q:
  "(\<And>x y. R\<^sup>*\<^sup>* x y \<Longrightarrow> R\<^sup>*\<^sup>* (f x) (f y)) \<Longrightarrow>
   (\<And>x y. R (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   inj f \<Longrightarrow>
   R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> x \<in> range f \<Longrightarrow> z \<in> range f \<Longrightarrow> y \<in> range f"
*)

lemma q:
  "fully_faithful_funct R\<^sup>*\<^sup>* R\<^sup>*\<^sup>* f \<Longrightarrow> rel_limited_under R (range f)"
  apply (simp add: fully_faithful_funct_def full_funct_def
    faithful_funct_def funct_def)

(* Подумать что это за функтор
   fully faithful эндофунктор
   т.к. это биекция между морфизмами благодаря rel_limited_under
   *)
definition functor_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "functor_under_rel R f \<equiv>
    rel_limited_under R (range f) \<and>
    inj f \<and>
    (\<forall>x y. R (f x) (f y) \<longrightarrow> R x y)"

(* Это что-то типа естественного преобразования, нужно нарисовать все эти условия
   возможно что-то сгруппировать или упростить *)
definition natural_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "natural_under_rel R f g \<equiv>
    functor_under_rel R f \<and>
    functor_under_rel R g \<and>
    (\<forall>x. R (f x) (g x)) \<and>
    (\<forall>x y. R (f x) (g y) \<longrightarrow> x \<noteq> y \<longrightarrow> R x y) \<and>
    (\<forall>x y. \<not> R\<^sup>+\<^sup>+ (g x) (f y)) \<and>
    (\<forall>x y. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> (\<exists>z. y = f z \<or> y = g z))"

lemma tranclp_fun_preserve_gen_2:
  fixes f:: "'a \<Rightarrow> 'b"
    and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x x' :: 'a
  assumes prem: "(\<lambda>x x'. R (f x) (f x'))\<^sup>+\<^sup>+ x x'"
  shows "R\<^sup>+\<^sup>+ (f x) (f x')"
proof -
  obtain P where P: "P = (\<lambda>x x'. (\<lambda>y y'. R y y')\<^sup>+\<^sup>+ (f x) (f x'))" by auto
  obtain r where r: "r = (\<lambda>x x'. R (f x) (f x'))" by auto
  from prem r have major: "r\<^sup>+\<^sup>+ x x'" by blast
  from P r have cases_1: "\<And>y y'. r y y' \<Longrightarrow> P y y'" by simp
  from P have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z" by auto
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P x x'" by smt
  with P show ?thesis by simp
qed

lemma tranclp_fun_preserve_gen_2a:
  assumes as_R: "\<And>x x'. R x x' \<Longrightarrow> R (f x) (f x')"
      and prem: "R\<^sup>+\<^sup>+ x x'"
  shows "R\<^sup>+\<^sup>+ (f x) (f x')"
proof -
  obtain P where P: "P = (\<lambda>x x'. R\<^sup>+\<^sup>+ (f x) (f x'))" by auto
  obtain r where r: "r = (\<lambda>x x'. R (f x) (f x'))" by auto
  from prem r as_R have major: "r\<^sup>+\<^sup>+ x x'"
    by (smt tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)
  from P r have cases_1: "\<And>y y'. r y y' \<Longrightarrow> P y y'" by simp
  from P have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z" by auto
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P x x'" by smt
  with P show ?thesis by simp
qed

lemma tranclp_fun_preserve_gen_1:
  fixes f:: "'a \<Rightarrow> 'b"
    and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x x'::'a
  assumes as_f: "inj f"
    and as_R: "rel_limited_under R (range f)"
    and prem: "R\<^sup>+\<^sup>+ (f x) (f x')"
  shows "(\<lambda>x x'. R (f x) (f x'))\<^sup>+\<^sup>+ x x'"
proof -
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g (range f)" by auto
  obtain B where B: "B = range f" by auto
  obtain P where P: "P = (\<lambda>y y'. y \<in> B \<longrightarrow> y' \<in> B \<longrightarrow> (\<lambda> x x'. R (f x) (f x'))\<^sup>+\<^sup>+ (gr y) (gr y'))" by auto
  from B as_f have as_f2: "bij_betw f UNIV B" by (simp add: bij_betw_imageI)
  from prem have major: "R\<^sup>+\<^sup>+ (f x) (f x')" by blast
  from P as_f2 g gr have cases_1: "\<And>y y'. R y y' \<Longrightarrow> P y y'"
    by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_imp_surj_on 
        f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
  from P B as_R have cases_2:
    "\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> R\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    by (smt cases_1 rel_limited_under_def rtranclp_induct tranclp_into_rtranclp tranclp_rtranclp_tranclp)
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P (f x) (f x')" by smt
  with P B as_f g gr show ?thesis
    by (simp add: the_inv_f_f)
qed

lemma q:
  "    R\<^sup>+\<^sup>+ x y \<Longrightarrow>
       (x \<in> range f \<Longrightarrow>
       y \<in> range f \<Longrightarrow> R\<^sup>+\<^sup>+ (the_inv f x) (the_inv f y)) \<Longrightarrow>
       R\<^sup>+\<^sup>+ y z \<Longrightarrow>
       (y \<in> range f \<Longrightarrow>
       z \<in> range f \<Longrightarrow> R\<^sup>+\<^sup>+ (the_inv f y) (the_inv f z)) \<Longrightarrow>
       (*(\<And>x y. R x y \<Longrightarrow> R (f x) (f y)) \<Longrightarrow>
       (\<And>x y. R (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
       (\<And>x y. R x y \<Longrightarrow> R (f x) (f y)) \<Longrightarrow>*)
       inj f \<Longrightarrow>
       x \<in> range f \<Longrightarrow>
(*y \<in> range f \<Longrightarrow> *)
 (\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> x \<in> range f \<Longrightarrow> z \<in> range f \<Longrightarrow> y \<in> range f) \<Longrightarrow>
       z \<in> range f \<Longrightarrow> R\<^sup>+\<^sup>+ (the_inv f x) (the_inv f z)"
(*  by (meson tranclp_trans)*)
  apply (auto simp: the_inv_f_f)

lemma tranclp_fun_preserve_gen_1a:
  fixes f:: "'a \<Rightarrow> 'a"
    and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and x x'::'a
  assumes as_f: "functor_under_rel R f"
          (*as_f: "fully_faithful_funct R R f"*)
      and prem: "R\<^sup>+\<^sup>+ (f x) (f x')"
  shows "R\<^sup>+\<^sup>+ x x'"
proof -
  obtain B where B: "B = range f" by auto
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g B" by auto
  obtain P where P: "P = (\<lambda>y y'. y \<in> B \<longrightarrow> y' \<in> B \<longrightarrow> R\<^sup>+\<^sup>+ (gr y) (gr y'))" by auto
  from as_f have as_R2: "rel_limited_under R (range f)"
    by (simp add: functor_under_rel_def)
  from prem have major: "R\<^sup>+\<^sup>+ (f x) (f x')" by blast
  from P as_f B g gr have cases_1: "\<And>y y'. R y y' \<Longrightarrow> P y y'"
(*    by (simp add: P f_the_inv_into_f faithful_funct_def full_funct_def fully_faithful_funct_def tranclp.r_into_trancl)*)
    by (simp add: functor_under_rel_def f_the_inv_into_f tranclp.r_into_trancl)
  from P B as_R2 have cases_2:
    "\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> R\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
(*    apply (auto simp add: P B gr g faithful_funct_def full_funct_def fully_faithful_funct_def funct_def
            rel_limited_under_def)*)
(*    apply (rule impI)
    apply (rule impI)
    apply (erule conjE)
    apply (erule conjE)
    apply (erule conjE)
  *)
    by (smt cases_1 rel_limited_under_def rtranclp_induct tranclp_into_rtranclp tranclp_rtranclp_tranclp)
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P (f x) (f x')" by smt
  with P B as_f g gr show ?thesis
    by (simp add: functor_under_rel_def the_inv_f_f)
qed

lemma tranclp_fun_preserve1b:
  assumes as_nat: "natural_under_rel R f g"
      and as_x: "x \<noteq> x'"
      and prem: "R\<^sup>+\<^sup>+ (f x) (g x')"
    shows "R\<^sup>+\<^sup>+ x x'"
proof -
  obtain f' where f': "f' = the_inv_into UNIV f" by auto
  obtain g' where g': "g' = the_inv_into UNIV g" by auto
  obtain f'' where f'': "f'' = restrict f' (range f)" by auto
  obtain g'' where g'': "g'' = restrict g' (range g)" by auto
  obtain FR where FR: "FR = range f" by auto
  obtain GR where GR: "GR = range g" by auto
  obtain P where P: "P = (\<lambda>y y'.
     (y \<in> FR \<and> y' \<in> FR \<longrightarrow> R\<^sup>+\<^sup>+ (f'' y) (f'' y')) \<and>
     (y \<in> FR \<and> y' \<in> GR \<longrightarrow> (f'' y) \<noteq> (g'' y') \<longrightarrow> R\<^sup>+\<^sup>+ (f'' y) (g'' y')) \<and>
     (y \<in> GR \<and> y' \<in> FR \<longrightarrow> False) \<and>
     (y \<in> GR \<and> y' \<in> GR \<longrightarrow> R\<^sup>+\<^sup>+ (g'' y) (g'' y')))" by auto
  from prem have major: "R\<^sup>+\<^sup>+ (f x) (g x')" by blast
  from as_nat
  have cases_1: "\<And>y y'. R y y' \<Longrightarrow> P y y'"
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
    "\<And>x y z. R\<^sup>+\<^sup>+ (x) y \<Longrightarrow> P (x) y \<Longrightarrow> R\<^sup>+\<^sup>+ y (z) \<Longrightarrow> P y (z) \<Longrightarrow> P (x) (z)"
    apply (unfold f'' f' g'' g' P FR GR natural_under_rel_def functor_under_rel_def)
    apply (rule conjI)
    apply (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    apply (rule conjI)
    apply (smt f_the_inv_into_f functor_under_rel_def rangeI tranclp_trans)
    apply (rule conjI)
    apply (metis f_the_inv_into_f tranclp_trans)
    by (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
  from major cases_1 cases_2 have inv_conc: "P (f x) (g x')"
    apply (rule_tac ?x="f x" and ?y="g x'" and ?r="R" in tranclp_trans_induct)
    apply (simp)
    apply blast
    by blast
  with P FR GR as_nat f' f'' g' g'' as_x show ?thesis
    by (simp add: the_inv_f_f natural_under_rel_def functor_under_rel_def)
qed
(*
lemma tranclp_fun_preserve2b:
  assumes as_nat: "f_rel_g R f g"
      and prem: "R\<^sup>+\<^sup>+ x x'"
    shows "R\<^sup>+\<^sup>+ (f x) (g x')"
proof -
  obtain f' where f': "f' = the_inv_into UNIV f" by auto
  obtain g' where g': "g' = the_inv_into UNIV g" by auto
  obtain f'' where f'': "f'' = restrict f' (range f)" by auto
  obtain g'' where g'': "g'' = restrict g' (range g)" by auto
  obtain FR where FR: "FR = range f" by auto
  obtain GR where GR: "GR = range g" by auto
  obtain P where P: "P = (\<lambda>y y'.
     (y \<in> FR \<and> y' \<in> FR \<longrightarrow> R\<^sup>+\<^sup>+ (f'' y) (f'' y')) \<and>
     (y \<in> FR \<and> y' \<in> GR \<longrightarrow> (f'' y) \<noteq> (g'' y') \<longrightarrow> R\<^sup>+\<^sup>+ (f'' y) (g'' y')) \<and>
     (y \<in> GR \<and> y' \<in> FR \<longrightarrow> False) \<and>
     (y \<in> GR \<and> y' \<in> GR \<longrightarrow> R\<^sup>+\<^sup>+ (g'' y) (g'' y')))" by auto
  from prem have major: "R\<^sup>+\<^sup>+ (f x) (g x')" by blast
  from as_nat
  have cases_1: "\<And>y y'. R y y' \<Longrightarrow> P y y'"
    apply (unfold P f' f'' g' g'' FR GR f_rel_g_def functor_under_rel_def)
    apply (rule conjI)
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    apply (rule conjI)
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    apply (rule conjI)
    apply blast
    apply (metis f_the_inv_into_f restrict_apply' tranclp.r_into_trancl)
    done
  from as_nat have cases_2:
    "\<And>x y z. R\<^sup>+\<^sup>+ (x) y \<Longrightarrow> P (x) y \<Longrightarrow> R\<^sup>+\<^sup>+ y (z) \<Longrightarrow> P y (z) \<Longrightarrow> P (x) (z)"
    apply (unfold f'' f' g'' g' P FR GR f_rel_g_def functor_under_rel_def)
    apply (rule conjI)
    apply (metis (no_types, lifting) f_the_inv_into_f restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    apply (rule conjI)
    apply (smt f_the_inv_into_f rangeI tranclp_trans)
    apply (rule conjI)
    apply (metis f_the_inv_into_f tranclp_trans)
    by (metis (no_types, lifting) f_the_inv_into_f restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
  from major cases_1 cases_2 have inv_conc: "P (f x) (g x')"
    apply (rule_tac ?x="f x" and ?y="g x'" and ?r="R" in tranclp_trans_induct)
    apply (simp)
    apply blast
    by blast
  with P FR GR as_nat f' f'' g' g'' as_x show ?thesis
    by (simp add: the_inv_f_f f_rel_g_def functor_under_rel_def)
qed
*)

end
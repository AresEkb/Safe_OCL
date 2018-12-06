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
definition rel_limited_under :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rel_limited_under R f =
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"
(*
lemma q:
  "(\<forall>x y. R (f x) (f y) \<longrightarrow> R x y) \<Longrightarrow>
   (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"
  nitpick
*)
(*
  R = S = subtype\<^sup>*\<^sup>*
  Все эти штуки лучше определять через классы и локали
*)
(*
lemma q:
  "(R x y \<Longrightarrow> R y z \<Longrightarrow> (R OO R) x z) \<Longrightarrow>
   S (f x) (y) \<Longrightarrow> S (y) (f z) \<Longrightarrow> (S OO S) (f x) (f z)"
  nitpick

lemma q:
  "(R OO R) x z \<Longrightarrow> \<exists>y. R x y \<and> R y z \<and> R x z"
  nitpick
  oops
*)
(*
locale thin_cat = order
begin
end
*)
definition funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "funct R S f \<equiv> (\<forall>x y. R x y \<longrightarrow> S (f x) (f y))"

(*
('a :: {order} \<Rightarrow> 'b :: {order})
 \<and> (R OO R) x y \<longrightarrow> (S OO S) (f x) (f y)
  Определение функтора:
    с каждым объектом из 'a ассоциирует объект из 'b, т.к. это (полная) функуция
    с каждым морфизмом из R ассоциирует морфизм из S: (\<forall>x y. R x y \<longrightarrow> S (f x) (f y))
*)

definition faithful_funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "faithful_funct R S f \<equiv> funct R S f \<and> inj f"
(*
definition full_funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "full_funct R S f \<equiv> funct R S f \<and>
(*     (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y) \<and>*)
     (\<forall>x y z. S (f x) y \<longrightarrow> S y (f z) \<longrightarrow> y \<in> range f)"
(*  "full_funct R S f \<equiv> funct R S f \<and> (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y)"*)

definition fully_faithful_funct :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "fully_faithful_funct R S f \<equiv> full_funct R S f \<and> faithful_funct R S f"
*)
(*
lemma q:
  "(\<And>x y. R\<^sup>*\<^sup>* x y \<Longrightarrow> R\<^sup>*\<^sup>* (f x) (f y)) \<Longrightarrow>
   (\<And>x y. R (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   inj f \<Longrightarrow>
   R\<^sup>+\<^sup>+ x y \<Longrightarrow> R y z \<Longrightarrow> x \<in> range f \<Longrightarrow> z \<in> range f \<Longrightarrow> y \<in> range f"
*)
(*
lemma q1:
  "rel_limited_under R f =
   rel_limited_under R (range f)"
  using rel_limited_under_def rel_limited_under_def by fastforce

lemma q2:
  "fully_faithful_funct R\<^sup>*\<^sup>* R\<^sup>*\<^sup>* f \<Longrightarrow> rel_limited_under R (range f)"
  apply (simp add: fully_faithful_funct_def full_funct_def
    faithful_funct_def funct_def)
  by (metis (full_types) q1 r_into_rtranclp rel_limited_under_def tranclp_into_rtranclp)
*)
(* Подумать что это за функтор
   fully faithful эндофунктор
   т.к. это биекция между морфизмами благодаря rel_limited_under
   *)
(*
definition functor_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "functor_under_rel R f \<equiv>
    rel_limited_under R (range f) \<and>
    inj f \<and>
    (\<forall>x y. R (f x) (f y) \<longrightarrow> R x y)"
*)
definition functor_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "functor_under_rel R S f \<equiv>
    rel_limited_under S f \<and>
    inj f \<and>
    (\<forall>x y. S (f x) (f y) \<longrightarrow> R x y)"

(* Это что-то типа естественного преобразования, нужно нарисовать все эти условия
   возможно что-то сгруппировать или упростить *)
(*
definition natural_under_rel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "natural_under_rel R f g \<equiv>
    functor_under_rel R f \<and>
    functor_under_rel R g \<and>
    (\<forall>x. R (f x) (g x)) \<and>
    (\<forall>x y. R (f x) (g y) \<longrightarrow> x \<noteq> y \<longrightarrow> R x y) \<and>
    (\<forall>x y. \<not> R\<^sup>+\<^sup>+ (g x) (f y)) \<and>
    (\<forall>x y. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> (\<exists>z. y = f z \<or> y = g z))"
*)

lemma fun_preserve_morphism_composition':
  fixes f :: "'a \<Rightarrow> 'b"
    and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x y :: 'a
  assumes as_R: "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
      and prem: "R\<^sup>+\<^sup>+ x y"
  shows "S\<^sup>+\<^sup>+ (f x) (f y)"
proof -
  obtain P where P: "P = (\<lambda>x y. S\<^sup>+\<^sup>+ (f x) (f y))" by auto
  obtain r where r: "r = (\<lambda>x y. S (f x) (f y))" by auto
  from prem r as_R have major: "r\<^sup>+\<^sup>+ x y"
    by (smt tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y" by simp
  from P have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z" by auto
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P x y" by smt
  with P show ?thesis by simp
qed

lemma fun_preserve_morphism_composition:
  fixes f :: "'a \<Rightarrow> 'b"
    and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and S :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x y :: 'a
  assumes as_R: "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
      and prem: "R\<^sup>*\<^sup>* x y"
  shows "S\<^sup>*\<^sup>* (f x) (f y)"
proof -
  obtain P where P: "P = (\<lambda>x y. S\<^sup>*\<^sup>* (f x) (f y))" by auto
  obtain r where r: "r = (\<lambda>x y. S (f x) (f y))" by auto
  from prem r as_R have major: "r\<^sup>*\<^sup>* x y"
    by (metis mono_rtranclp)
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y" by simp
  from P have cases_2: "\<And>x y z. r\<^sup>*\<^sup>* x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>*\<^sup>* y z \<Longrightarrow> P y z \<Longrightarrow> P x z" by auto
  from major cases_1 cases_2 have inv_conc: "P x y"
    by (metis Nitpick.rtranclp_unfold P as_R prem fun_preserve_morphism_composition')
  with P show ?thesis by simp
qed

lemma tranclp_fun_preserve_gen_2:
  fixes f :: "'a \<Rightarrow> 'b"
    and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x y :: 'a
  assumes prem: "(\<lambda>x y. R (f x) (f y))\<^sup>+\<^sup>+ x y"
  shows "R\<^sup>+\<^sup>+ (f x) (f y)"
proof -
  obtain P where P: "P = (\<lambda>x y. R\<^sup>+\<^sup>+ (f x) (f y))" by auto
  obtain r where r: "r = (\<lambda>x y. R (f x) (f y))" by auto
  from prem r have major: "r\<^sup>+\<^sup>+ x y" by blast
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y" by simp
  from P have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z" by auto
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P x y" by smt
  with P show ?thesis by simp
qed

lemma tranclp_fun_preserve_gen_1:
  fixes f :: "'a \<Rightarrow> 'b"
    and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and x y :: 'a
  assumes as_f: "inj f"
    and as_R: "rel_limited_under R f"
    and prem: "R\<^sup>+\<^sup>+ (f x) (f y)"
  shows "(\<lambda>x y. R (f x) (f y))\<^sup>+\<^sup>+ x y"
proof -
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g (range f)" by auto
  obtain B where B: "B = range f" by auto
  obtain P where P: "P = (\<lambda>x y. x \<in> B \<longrightarrow> y \<in> B \<longrightarrow> (\<lambda>x y. R (f x) (f y))\<^sup>+\<^sup>+ (gr x) (gr y))" by auto
  from B as_f have as_f2: "bij_betw f UNIV B" by (simp add: bij_betw_imageI)
  from as_R have as_R2: "(\<forall>x y z. R\<^sup>+\<^sup>+ x y \<longrightarrow> R y z \<longrightarrow> x \<in> B \<longrightarrow> z \<in> B \<longrightarrow> y \<in> B)"
    by (metis B rangeE rel_limited_under_def)
  from prem have major: "R\<^sup>+\<^sup>+ (f x) (f y)" by blast
  have cases_1: "\<And>x y. R x y \<Longrightarrow> P x y"
    by (simp add: P B as_f2 g gr as_f f_the_inv_into_f tranclp.r_into_trancl)
  from as_R2 have cases_2:
    "\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> R\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    by (smt P cases_1 rtranclp_induct tranclp_into_rtranclp tranclp_rtranclp_tranclp)
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P (f x) (f y)" by smt
  with P B as_f g gr show ?thesis
    by (simp add: the_inv_f_f)
qed

lemma tranclp_fun_preserve_gen_1a:
  fixes f :: "'a \<Rightarrow> 'b"
    and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and x y :: 'a
  assumes as_f: "functor_under_rel R S f"
(*          as_f: "fully_faithful_funct R\<^sup>*\<^sup>* R\<^sup>*\<^sup>* f"*)
      and prem: "S\<^sup>+\<^sup>+ (f x) (f y)"
  shows "R\<^sup>+\<^sup>+ x y"
proof -
  obtain B where B: "B = range f" by auto
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g B" by auto
  obtain P where P: "P = (\<lambda>x y. x \<in> B \<longrightarrow> y \<in> B \<longrightarrow> R\<^sup>+\<^sup>+ (gr x) (gr y))" by auto
  from as_f have as_R2: "(\<forall>x y z. S\<^sup>+\<^sup>+ x y \<longrightarrow> S y z \<longrightarrow> x \<in> B \<longrightarrow> z \<in> B \<longrightarrow> y \<in> B)"
    by (metis (full_types) B functor_under_rel_def rangeE rel_limited_under_def)
(*    by (smt full_funct_def fully_faithful_funct_def r_into_rtranclp rangeE reflclp_tranclp rel_limited_under_def rtranclp_idemp rtranclp_reflclp)*)
  from prem have major: "S\<^sup>+\<^sup>+ (f x) (f y)" by blast
  from as_f have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
    by (simp add: B P f_the_inv_into_f functor_under_rel_def g gr tranclp.r_into_trancl)
(*    apply (auto simp add: P B g gr fully_faithful_funct_def faithful_funct_def full_funct_def funct_def)*)
(*    by (simp add: P f_the_inv_into_f faithful_funct_def full_funct_def fully_faithful_funct_def tranclp.r_into_trancl)*)
(*    by (simp add: functor_under_rel_def f_the_inv_into_f tranclp.r_into_trancl)*)
  from P B as_R2 have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
(*    apply (auto simp add: P B gr g faithful_funct_def full_funct_def fully_faithful_funct_def funct_def
            rel_limited_under_def)*)
(*    apply (rule impI)
    apply (rule impI)
    apply (erule conjE)
    apply (erule conjE)
    apply (erule conjE)
  *)
    by (smt cases_1 rel_limited_under_def rtranclp_induct tranclp_into_rtranclp tranclp_rtranclp_tranclp)
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P (f x) (f y)" by smt
  with P B as_f g gr show ?thesis
    by (simp add: functor_under_rel_def the_inv_f_f)
qed

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
(*      and as_fg: "range f \<inter> range g = {}"*)
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
(*
  obtain P where P: "P = (\<lambda>x y.
     (\<exists>xa ya. f xa = x \<and> f ya = y \<longrightarrow> R\<^sup>+\<^sup>+ (f'' x) (f'' y)) \<and>
     (\<exists>xa ya. f xa = x \<and> g ya = y \<and> (f'' x) \<noteq> (g'' y) \<longrightarrow> R\<^sup>+\<^sup>+ (f'' x) (g'' y)) \<and>
     (\<exists>xa ya. g xa = x \<and> f ya = y \<longrightarrow> False) \<and>
     (\<exists>xa ya. g xa = x \<and> g ya = y \<longrightarrow> R\<^sup>+\<^sup>+ (g'' x) (g'' y)))" by auto
*)
(*
  obtain P where P: "P = (\<lambda>x y.
     (case (x, y) of (f _, f _) \<Rightarrow> R\<^sup>+\<^sup>+ (f'' x) (f'' y)
                   | (f _, g _) \<Rightarrow> (f'' x) = (g'' y) \<or> R\<^sup>+\<^sup>+ (f'' x) (g'' y)
                   | (g _, f _) \<Rightarrow> False
                   | (g _, g _) \<Rightarrow> R\<^sup>+\<^sup>+ (g'' x) (g'' y)))" by auto
*)

  from prem have major: "S\<^sup>+\<^sup>+ (f x) (g y)" by blast
  from as_nat have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
(*
    apply (unfold P f' f'' g' g'' natural_under_rel_def functor_under_rel_def)
*)
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
(*
    apply (unfold f'' f' g'' g' P natural_under_rel_def functor_under_rel_def)
    apply (smt as_x inj_def)
    done
*)
(*
    apply (rule conjI)
    apply metis
    apply (rule conjI)
    apply metis
    apply (rule conjI)
    apply (metis tranclp_trans)
    by (metis (mono_tags, lifting) as_x inv_f_f)
*)
    apply (unfold f'' f' g'' g' P FR GR natural_under_rel_def functor_under_rel_def)
    apply (rule conjI)
    apply (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    apply (rule conjI)
    apply (smt f_the_inv_into_f functor_under_rel_def rangeI tranclp_trans)
    apply (rule conjI)
    apply (metis rangeE tranclp_trans)
(*    apply (metis f_the_inv_into_f tranclp_trans) *)
    apply (metis (full_types) f_the_inv_into_f functor_under_rel_def restrict_apply' tranclp_fun_preserve_gen_1a tranclp_trans)
    done
  from major cases_1 cases_2 have inv_conc: "P (f x) (g y)"
    apply (rule_tac ?x="f x" and ?y="g y" and ?r="S" in tranclp_trans_induct)
    apply (simp)
    apply blast
    by blast
(*  from as_x have q: "P (f x) (g y) \<Longrightarrow> (\<exists>xa ya. f x = xa \<longrightarrow> g y = ya \<longrightarrow> R\<^sup>+\<^sup>+ (f'' xa) (g'' ya))"
    by (metis (full_types) P)
  from as_x have q2: "\<And>x y. x \<in> range f \<Longrightarrow> y \<in> range g \<Longrightarrow> R\<^sup>+\<^sup>+ (f'' x) (g'' y) \<Longrightarrow> R\<^sup>+\<^sup>+ x y"
  from as_x have q2: "(\<exists>xa ya. f x = xa \<longrightarrow> g y = ya \<longrightarrow> R\<^sup>+\<^sup>+ (f'' xa) (g'' ya)) \<Longrightarrow> R\<^sup>+\<^sup>+ x y"*)
  with as_nat as_x show ?thesis
    apply (simp add: P f' f'' g' g'' the_inv_f_f natural_under_rel_def functor_under_rel_def)
    by (simp add: FR GR)
qed
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
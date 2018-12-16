(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* Preliminaries *}
section{* Transitive Closures *}
theory Transitive_Closure_Ext
  imports Main "HOL-Library.FuncSet"
begin

(*** Basic Properties *******************************************************)

subsection{* Basic Properties *}

text{* @{text "R\<^sup>+\<^sup>+"} is a transitive closure of a relation @{text R}. *}

text{* @{text "R\<^sup>*\<^sup>*"} is a reflexive transitive closure of a relation @{text R}. *}

text{* A function @{text f} is surjective on a transitive closure of a
 relation @{text R} iff for any two elements in the range of @{text f},
 related through @{text "R\<^sup>+\<^sup>+"}, all intermediate elements
 belong to the range of @{text f}. *}

abbreviation "surj_on_trancl R f \<equiv> (\<forall>x y z. R\<^sup>+\<^sup>+ (f x) y \<longrightarrow> R y (f z) \<longrightarrow> y \<in> range f)"

text {* A function @{text f} is bijective on a transitive closure of a
 relation @{text R} iff it's injective and surjective on @{text "R\<^sup>+\<^sup>+"}. *}

abbreviation "bij_on_trancl R f \<equiv> inj f \<and> surj_on_trancl R f"

(*** Helper Lemmas **********************************************************)

subsection{* Helper Lemmas *}

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
    by (erule tranclp_induct, auto) (meson tranclp_trans)
  thus ?thesis
    using assms by auto
qed

(*** Transitive Closure Preservation & Reflection ***************************)

subsection{* Transitive Closure Preservation *}

text {* A function @{text f} preserves a transitive closure of a relation
  @{text R} if @{text f} preserves @{text R}. *}

(* The proof was derived from the accepted answer on the website
   Stack Overflow that is available at
   https://stackoverflow.com/a/52573551/632199
   and provided with the permission of the author of the answer *)
lemma preserve_tranclp:
  assumes "\<And>x y. R x y \<Longrightarrow> S (f x) (f y)"
      and "R\<^sup>+\<^sup>+ x y"
    shows "S\<^sup>+\<^sup>+ (f x) (f y)"
proof -
  define P where P: "P = (\<lambda>x y. S\<^sup>+\<^sup>+ (f x) (f y))" 
  define r where r: "r = (\<lambda>x y. S (f x) (f y))"
  have major: "r\<^sup>+\<^sup>+ x y" by (insert assms r; erule tranclp_trans_induct; auto)
  have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y"
    unfolding P r by simp
  have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding P by auto
  from major cases_1 cases_2 have "P x y"
    by (rule tranclp_trans_induct, auto)
  with P show ?thesis by simp
qed

text {* A function @{text f} preserves a reflexive transitive closure
  of a relation @{text R} if @{text f} preserves @{text R}. *}

lemma preserve_rtranclp:
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (f y)"
  unfolding Nitpick.rtranclp_unfold
  by (metis preserve_tranclp)

text {* If one needs to prove that @{text "(f x)"} and @{text "(g y)"}
  are related through a reflexive transitive closure of a
  relation @{text S} then one can use the previous lemma and
  add a one more step from @{text "(f y)"} to @{text "(g y)"}. *}

lemma preserve_rtranclp':
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* (f x) (g y)"
  by (metis preserve_rtranclp rtranclp.rtrancl_into_rtrancl)

subsection{* Transitive Closure Reflection *}

text {* A function @{text f} reflects a transitive closure of a relation
  @{text S} if @{text f} reflects @{text S} and @{text f} is bijective
  on @{text "S\<^sup>+\<^sup>+"}. *}

(* The proof was derived from the accepted answer on the website
   Stack Overflow that is available at
   https://stackoverflow.com/a/52573551/632199
   and provided with the permission of the author of the answer *)
lemma reflect_tranclp:
  assumes refl_f: "\<And>x y. S (f x) (f y) \<Longrightarrow> R x y"
      and bij_f: "bij_on_trancl S f"
      and prem: "S\<^sup>+\<^sup>+ (f x) (f y)"
  shows "R\<^sup>+\<^sup>+ x y"
proof -
  define B where B: "B = range f"
  define g where g: "g = the_inv_into UNIV f"
  define gr where gr: "gr = restrict g B"
  define P where P: "P = (\<lambda>x y. x \<in> B \<longrightarrow> y \<in> B \<longrightarrow> R\<^sup>+\<^sup>+ (gr x) (gr y))"
  from prem have major: "S\<^sup>+\<^sup>+ (f x) (f y)" by blast
  from refl_f bij_f have cases_1: "\<And>x y. S x y \<Longrightarrow> P x y"
    unfolding B P g gr
    by (simp add: f_the_inv_into_f tranclp.r_into_trancl)
  from refl_f bij_f
  have "(\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> x \<in> B \<Longrightarrow> z \<in> B \<Longrightarrow> y \<in> B)"
    unfolding B
    by (rule_tac ?z="z" in tranclp_tranclp_to_tranclp_r, auto, blast)
  with P have cases_2:
    "\<And>x y z. S\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> S\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding B
    by auto
  from major cases_1 cases_2 have "P (f x) (f y)"
    by (rule tranclp_trans_induct, auto)
  with bij_f show ?thesis
    unfolding P B g gr
    by (simp add: the_inv_f_f)
qed

text {* A function @{text f} reflects a reflexive transitive closure
  of a relation @{text S} if @{text f} reflects @{text S} and @{text f}
  is bijective on @{text "S\<^sup>+\<^sup>+"}. *}

lemma reflect_rtranclp:
  "(\<And>x y. S (f x) (f y) \<Longrightarrow> R x y) \<Longrightarrow>
   bij_on_trancl S f \<Longrightarrow>
   S\<^sup>*\<^sup>* (f x) (f y) \<Longrightarrow> R\<^sup>*\<^sup>* x y"
  unfolding Nitpick.rtranclp_unfold
  by (metis (full_types) injD reflect_tranclp)

end

theory TupleTest
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = Void | Any | A | B | C "t list"

inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "Void \<sqsubset> A"
| "A \<sqsubset> B"
| "B \<sqsubset> Any"
| "Void \<sqsubset> C xs"
| "list_all2 (\<lambda>x y. x \<sqsubset> y)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   C xs \<sqsubset> C ys"
| "C xs \<sqsubset> Any"
(*
| "list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   C xs \<sqsubset> C ys"
*)

inductive_cases subtype_Void_x[elim]: "Void \<sqsubset> x"
inductive_cases subtype_x_Void[elim]: "x \<sqsubset> Void"
inductive_cases subtype_Any_x[elim]: "Any \<sqsubset> x"
inductive_cases subtype_x_Any[elim]: "x \<sqsubset> Any"
inductive_cases subtype_A_x[elim]: "A \<sqsubset> x"
inductive_cases subtype_x_A[elim]: "x \<sqsubset> A"
inductive_cases subtype_B_x[elim]: "B \<sqsubset> x"
inductive_cases subtype_x_B[elim]: "x \<sqsubset> B"
inductive_cases subtype_C_x[elim]: "C xs \<sqsubset> x"
inductive_cases subtype_x_C[elim]: "x \<sqsubset> C xs"

lemma trancl_subtype_Void_x [elim]:
  "subtype\<^sup>+\<^sup>+ Void x \<Longrightarrow>
   (x = A \<Longrightarrow> P) \<Longrightarrow>
   (x = B \<Longrightarrow> P) \<Longrightarrow>
   (\<And>xs. x = C xs \<Longrightarrow> P) \<Longrightarrow>
   (x = Any \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis subtype_x_Void t.exhaust tranclp.cases)

lemma trancl_subtype_A_x [elim]:
  "subtype\<^sup>+\<^sup>+ A x \<Longrightarrow>
   (x = B \<Longrightarrow> P) \<Longrightarrow>
   (x = Any \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis rtranclpD subtype_A_x subtype_Any_x subtype_B_x tranclpD)

lemma trancl_subtype_B_x [elim]:
  "subtype\<^sup>+\<^sup>+ B x \<Longrightarrow>
   (x = Any \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis rtranclpD subtype_Any_x subtype_B_x tranclpD)

lemma trancl_subtype_Any_x [elim]:
  "subtype\<^sup>+\<^sup>+ Any x \<Longrightarrow> P"
  by (meson subtype_Any_x tranclpD)


lemma trancl_subtype_x_Void [elim]:
  "subtype\<^sup>+\<^sup>+ x Void \<Longrightarrow> P"
  by (metis subtype_x_Void tranclp.cases)

lemma trancl_subtype_x_A [elim]:
  "subtype\<^sup>+\<^sup>+ x A \<Longrightarrow>
   (x = Void \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis subtype_x_A trancl_subtype_x_Void tranclp.cases)

lemma trancl_subtype_x_B [elim]:
  "subtype\<^sup>+\<^sup>+ x B \<Longrightarrow>
   (x = Void \<Longrightarrow> P) \<Longrightarrow> 
   (x = A \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis subtype_x_B trancl_subtype_x_A tranclp.cases)

lemma trancl_subtype_x_Any [elim]:
  "subtype\<^sup>+\<^sup>+ x Any \<Longrightarrow>
   (x = Void \<Longrightarrow> P) \<Longrightarrow>
   (x = A \<Longrightarrow> P) \<Longrightarrow>
   (x = B \<Longrightarrow> P) \<Longrightarrow>
   (\<And>xs. x = C xs \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis subtype_Any_x t.exhaust tranclpD)

lemma q:
  "(\<And>xa. 
               subtype\<^sup>+\<^sup>+ (C xs) xa \<Longrightarrow>
               (\<And>zs. xa = C zs \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow>
               (xa = Any \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow>
         subtype\<^sup>+\<^sup>+ (C xs) (C x) \<Longrightarrow>
         (\<And>zs. x = zs \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow> P"
  by blast

lemma trancl_subtype_x_C [elim]:
  "subtype\<^sup>+\<^sup>+ x (C ys) \<Longrightarrow>
   (\<And>zs. x = C zs \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ zs ys \<Longrightarrow> P) \<Longrightarrow>
   (x = Void \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct x; auto)

lemma C_functor:
  "functor_under_rel "

lemma q:
  "(\<lambda>xs ys. subtype (C xs) (C ys))\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (list_all2 subtype)\<^sup>+\<^sup>+ xs ys"

lemma q:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   list_all2 subtype\<^sup>+\<^sup>+ xs ys"

  thm subtype_C_x

lemma C_implies_C:
  "subtype\<^sup>*\<^sup>* (C xs) y \<Longrightarrow> y = "

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>*\<^sup>* (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> list_all2 subtype\<^sup>*\<^sup>* xs zs \<Longrightarrow> P) \<Longrightarrow>
   (y = Any \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct y arbitrary: xs; auto)
  using rtranclpD apply fastforce
  using rtranclpD apply fastforce
  using rtranclpD apply fastforce

     apply (erule converse_rtranclpE)
  using list_all2_rtrancl1 apply auto[1]
  apply (erule subtype_C_x)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow>
   (y = Any \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> (list_all2 subtype)\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow>
   (y = Any \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct y arbitrary: xs; auto)

lemma q:
  "(\<And>xa. xa \<in> set x \<Longrightarrow>
               subtype\<^sup>+\<^sup>+ (C xs) xa \<Longrightarrow>
               (\<And>zs. xa = C zs \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow>
               (xa = Any \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow>
         subtype\<^sup>+\<^sup>+ (C xs) (C x) \<Longrightarrow>
         (\<And>zs. x = zs \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow> P"


lemma subtype_acyclic:
  "x \<sqsubset> x \<Longrightarrow> False"
  by (erule subtype.cases; auto)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x x \<Longrightarrow> False"
  apply (cases x; auto)

end

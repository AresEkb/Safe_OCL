theory TupleAcyclicTest
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = A | B | C "t list"

definition "sublist f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 (\<lambda>x y. x = y \<or> f x y) (take (length ys) xs) ys"

lemma f_eq_mono [mono]:
  "(\<And>x y. f x y \<longrightarrow> g x y) \<Longrightarrow> 
   (\<lambda>x y. x = y \<or> f x y) x y \<longrightarrow> (\<lambda>x y. x = y \<or> g x y) x y"
  by simp

lemma sublist_mono [mono]:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow> 
   sublist f xs ys \<longrightarrow> sublist g xs ys"
  by (metis (no_types, lifting) in_set_takeD list.rel_mono_strong sublist_def)

inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "sublist subtype xs ys \<Longrightarrow>
   C xs \<sqsubset> C ys"

lemma subtype_acyclic:
  "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  using subtype.cases apply blast
  by (smt length_take list_all2_antisym list_all2_lengthD min.cobounded1 sublist_def subtype.cases t.distinct(5) t.inject take_all)

lemma q:
  "subtype\<^sup>+\<^sup>+ (C ys) (C xs) \<Longrightarrow>
   sublist subtype xs ys \<Longrightarrow> False"

lemma q:
  "x \<sqsubset> y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  apply (meson subtype.cases t.distinct(2) t.distinct(5) tranclpD)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct rule: tranclp_induct)
  apply (erule subtype.cases)
  apply (metis converse_tranclpE subtype.cases subtype.intros(1) subtype_acyclic t.distinct(5))
  apply auto[1]


end

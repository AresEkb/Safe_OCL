theory TupleAcyclicTest3
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = A | B | C "t list"

definition "sublist f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 (\<lambda>x y. x = y \<or> f x y) (take (length ys) xs) ys"

lemma sublist_mono [mono]:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow> 
   sublist f xs ys \<longrightarrow> sublist g xs ys"
  by (metis (no_types, lifting) in_set_takeD list.rel_mono_strong sublist_def)

inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "sublist subtype xs ys \<Longrightarrow>
   C xs \<sqsubset> C ys"

lemma subtype_asym:
  "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  using subtype.cases apply blast
  apply (erule subtype.cases; auto simp add: sublist_def)
  by (metis (mono_tags, lifting) length_take list_all2_antisym list_all2_lengthD min.cobounded1 take_all)

lemma trancl_subtype_x_A [elim]:
  "subtype\<^sup>+\<^sup>+ x A \<Longrightarrow> P"
  apply (induct rule: converse_tranclp_induct)
  using subtype.cases by auto

lemma trancl_subtype_B_x [elim]:
  "subtype\<^sup>+\<^sup>+ B x \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  using subtype.cases by auto

lemma C_functor:
  "functor_under_rel (sublist subtype) subtype C"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  using subtype.simps apply auto[1]
  apply (meson injI t.inject)
  by (simp add: subtype.simps)

lemma trancl_subtype_C_C:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (sublist subtype)\<^sup>+\<^sup>+ xs ys"
  by (meson C_functor tranclp_fun_preserve_gen_1a)

lemma list_all2_antisym2:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P x y \<Longrightarrow> Q y x \<Longrightarrow> x = y) \<Longrightarrow>
   list_all2 P xs ys \<Longrightarrow> list_all2 Q ys xs \<Longrightarrow> xs = ys"
  apply (simp add: list_all2_conv_all_nth)
  apply (rule nth_equalityI, blast, simp)
  done

lemma list_all2_take_length_trans:
  "(\<And>x y z. P1 x y \<Longrightarrow> P2 y z \<Longrightarrow> P3 x z) \<Longrightarrow>
   list_all2 P1 (take (length ys) xs) ys \<Longrightarrow>
   list_all2 P2 (take (length zs) ys) zs \<Longrightarrow>
   list_all2 P3 (take (length zs) xs) zs"
  apply (drule_tac ?n="length zs" in list_all2_takeI)
  apply (frule list_all2_lengthD)
  by (smt length_take list_all2_trans take_take)

lemma sublist_trans:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   sublist P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P\<^sup>+\<^sup>+ xs zs"
  unfolding sublist_def
  apply auto
  apply (frule list_all2_lengthD)
  apply (unfold length_take)
  apply (smt length_take list_all2_antisym2 list_all2_lengthD min.cobounded1 take_all)
  by (smt list_all2_mono list_all2_take_length_trans tranclp.r_into_trancl tranclp_trans)

abbreviation "acyclic_in R xs \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

lemma trancl_subtype_C_C'''':
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in subtype (set xs) \<Longrightarrow>
   sublist subtype\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono tranclp.r_into_trancl)
  by (metis (full_types) sublist_trans tranclp.trancl_into_trancl)

lemma trancl_subtype_C_x':
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   acyclic_in subtype (set xs) \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono subtype.cases t.distinct(3) t.inject tranclp.simps)
  by (metis subtype.cases t.distinct(3) trancl_subtype_C_C trancl_subtype_C_C'''' tranclp.trancl_into_trancl)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct x arbitrary: y)
  apply auto[1]
  apply auto[1]
  by (meson C_functor sublist_def trancl_subtype_C_C'''' tranclp_fun_preserve_gen_1a tranclp_trans)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  using trancl_subtype_acyclic trancl_subtype_C_x' by blast

end

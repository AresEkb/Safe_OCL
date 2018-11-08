theory TupleAcyclicTest2
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = A | B | C "t list"

definition "sublist f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 (\<lambda>x y. x = y \<or> f x y) (take (length ys) xs) ys"
(*
definition "sublist f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 (\<lambda>x y. x = y \<or> f x y) xs ys"
*)
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

lemma subtype_asym:
  "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  using subtype.cases apply blast
  apply (erule subtype.cases; auto simp add: sublist_def)
  by (metis (mono_tags, lifting) length_take list_all2_antisym list_all2_lengthD min.cobounded1 take_all)
(*  by (metis (mono_tags, lifting) list_all2_antisym)*)
(*
lemma sublist_subtype_not_tr:
  "sublist subtype x y \<Longrightarrow>
   sublist subtype y z \<Longrightarrow>
   sublist subtype x z \<Longrightarrow> False"
  sorry
*)
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

thm list_all2_trans

lemma list_all2_trans1:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) xs ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) xs zs"
  by (smt list_all2_trans)

lemma list_all2_trans2:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 P (take (length ys) xs) ys \<Longrightarrow>
   list_all2 P (take (length zs) ys) zs \<Longrightarrow>
   list_all2 P (take (length zs) xs) zs"
  sorry
(*  by (smt length_take list_all2_lengthD list_all2_takeI list_all2_trans take_take)*)

lemma list_all2_trans3:
  "(\<And>x y z. P1 x y \<Longrightarrow> P2 y z \<Longrightarrow> P3 x z) \<Longrightarrow>
   list_all2 P1 (take (length ys) xs) ys \<Longrightarrow>
   list_all2 P2 (take (length zs) ys) zs \<Longrightarrow>
   list_all2 P3 (take (length zs) xs) zs"
  sorry
(*  by (smt append_eq_append_conv_if append_take_drop_id length_take list_all2_append2 list_all2_lengthD list_all2_trans take_take)*)

lemma list_all2_trans4:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length zs) ys) zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length zs) xs) zs"
  by (smt list_all2_trans2)

lemma list_all2_trans5:
  "(\<And>x y z. P1 x y \<Longrightarrow> P2 y z \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> P3 x z) \<Longrightarrow>
   list_all2 P1 xs ys \<Longrightarrow>
   list_all2 P2 ys zs \<Longrightarrow>
   list_all2 P3 xs zs"
  by (metis (full_types) list_all2_conv_all_nth nth_mem)

lemma list_all2_antisym1:
  "(\<And>x y. P x y \<Longrightarrow> P y x \<Longrightarrow> x = y) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length xs) ys) xs \<Longrightarrow>
   xs = ys"
  by (smt le_cases list_all2_antisym list_all2_lengthD take_all)

lemma sublist_trans1:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   (\<And>x y. P x y \<Longrightarrow> P y x \<Longrightarrow> x = y) \<Longrightarrow>
   sublist P xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P xs zs"
  unfolding sublist_def
  apply auto
  apply (smt le_cases list_all2_antisym list_all2_lengthD take_all)
  by (smt list_all2_trans2)

lemma sublist_trans2:
  "(\<And>x y. P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> x = y) \<Longrightarrow>
   sublist P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P\<^sup>+\<^sup>+ xs zs"
  unfolding sublist_def
  apply auto
  apply (frule list_all2_lengthD)
  apply (unfold length_take)
  apply (metis (mono_tags, lifting) list_all2_antisym list_all2_lengthD min.cobounded1 take_all)
(*  apply (smt length_take list_all2_antisym list_all2_lengthD min.cobounded1 take_all)*)
  by (smt list_all2_mono list_all2_trans2 tranclp.r_into_trancl tranclp_trans)

thm length_take list_all2_antisym list_all2_lengthD min.cobounded1 take_all

lemma sublist_trans3:
  "(\<And>x y. P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   sublist P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P\<^sup>+\<^sup>+ xs zs"
  unfolding sublist_def
  apply auto
  apply (smt length_take list_all2_antisym list_all2_lengthD min.cobounded1 take_all)
  by (smt list_all2_mono list_all2_trans2 tranclp.r_into_trancl tranclp_trans)

thm list_all2_antisym

lemma list_all2_antisym2:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> P x y \<Longrightarrow> Q y x \<Longrightarrow> x = y) \<Longrightarrow>
   list_all2 P xs ys \<Longrightarrow> list_all2 Q ys xs \<Longrightarrow> xs = ys"
  apply (simp add: list_all2_conv_all_nth)
  apply (rule nth_equalityI, blast, simp)
  done

lemma sublist_trans4:
  "(\<And>x y. P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> False) \<Longrightarrow>
   sublist P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P\<^sup>+\<^sup>+ xs zs"
  unfolding sublist_def
  apply auto
  apply (frule list_all2_lengthD)
  apply (unfold length_take)
  apply (smt length_take list_all2_antisym2 list_all2_lengthD min.cobounded1 take_all)
  by (smt list_all2_mono list_all2_trans2 tranclp.r_into_trancl tranclp_trans)

lemma list_all2_asym:
  "(\<And>x y. P x y \<Longrightarrow> Q y x \<Longrightarrow> False) \<Longrightarrow>
   list_all2 P xs ys \<Longrightarrow>
   list_all2 Q ys xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> False"
  by (metis list.rel_sel)


lemma trancl_subtype_C_C'':
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x y. subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype y x \<Longrightarrow> x = y) \<Longrightarrow>
   sublist subtype\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono tranclp.r_into_trancl)
  using sublist_trans2 by blast

lemma trancl_subtype_C_C''':
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x y. subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype y x \<Longrightarrow> False) \<Longrightarrow>
   sublist subtype\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono tranclp.r_into_trancl)
  using sublist_trans3 by blast

lemma trancl_subtype_C_C'''':
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x y. subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype y x \<Longrightarrow> x \<in> set xs \<Longrightarrow> False) \<Longrightarrow>
   sublist subtype\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono tranclp.r_into_trancl)
  by (metis sublist_trans4)
(*  using sublist_trans3 by blast*)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>x y. subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype y x \<Longrightarrow> x \<in> set xs \<Longrightarrow> False) \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono subtype.cases t.distinct(3) t.inject tranclp.simps)
  by (smt sublist_trans4 subtype.cases t.distinct(3) t.inject)
(*  by (metis subtype.simps t.distinct(4) trancl_subtype_C_C trancl_subtype_C_C'' tranclp.trancl_into_trancl)
*)

lemma q:
  "(\<And>x y.
    x \<in> xs \<Longrightarrow>
    P\<^sup>+\<^sup>+ x y \<Longrightarrow>
    P\<^sup>+\<^sup>+ y x \<Longrightarrow> False) \<Longrightarrow>
   (\<And>x y. P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> x \<in> xs \<Longrightarrow> False)"
  using tranclp.r_into_trancl by auto

lemma q123:
  "(\<And>x y.
    x \<in> xs \<Longrightarrow>
    P\<^sup>+\<^sup>+ x y \<Longrightarrow>
    P\<^sup>+\<^sup>+ y x \<Longrightarrow> False) \<Longrightarrow>
   (\<And>x y. P\<^sup>+\<^sup>+ x y \<Longrightarrow> x \<in> xs \<Longrightarrow> P y x \<Longrightarrow> False)"
  using tranclp.r_into_trancl by auto

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct x arbitrary: y)
  apply auto[1]
  apply auto[1]
  by (smt C_functor q sublist_def trancl_subtype_C_C'''' tranclp_fun_preserve_gen_1a tranclp_trans)

end

theory TupleAcyclicTest4
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = A | B | C "t list"

definition "sublist f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 f (take (length ys) xs) ys"

lemma sublist_mono [mono]:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow> 
   sublist f xs ys \<longrightarrow> sublist g xs ys"
  by (metis (no_types, lifting) in_set_takeD list.rel_mono_strong sublist_def)

inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys \<Longrightarrow>
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
  "functor_under_rel (sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)) subtype C"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  apply (metis rangeI subtype.simps t.distinct(5))
  apply (meson injI t.inject)
  using subtype.simps by blast

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

abbreviation "acyclic_in R xs \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

lemma sublist_trans:
  "acyclic_in P (set xs) \<Longrightarrow>
   sublist P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P\<^sup>+\<^sup>+ xs zs"
  unfolding sublist_def
  apply auto
  apply (frule list_all2_lengthD)
  apply (unfold length_take)
  apply (smt list_all2_antisym2 list_all2_lengthD min.cobounded1 take_all tranclp.r_into_trancl tranclp_trans)
  by (smt list_all2_mono list_all2_take_length_trans tranclp.r_into_trancl tranclp_trans)

lemma list_all2_trans2:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  by (smt list_all2_trancl1 list_all2_trancl2 tranclp.trancl_into_trancl)

lemma list_all2_take_length_trans2:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length zs) ys) zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ (take (length zs) xs) zs"
  apply (drule_tac ?n="length zs" in list_all2_takeI)
  apply (frule list_all2_lengthD)
  by (smt length_take list_all2_trans take_take tranclp.trancl_into_trancl)


lemma list_all2_antisym3:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P x y \<Longrightarrow> Q y x \<Longrightarrow> False) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) xs ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> Q x y) ys xs \<Longrightarrow>
   xs = ys"
  by (metis (mono_tags, lifting) list_all2_antisym2)

lemma q21:
  "(\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ x y \<Longrightarrow>
   (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) x y"
  by (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclpD rtranclp_idemp)

lemma q22:
  "(\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) x y \<Longrightarrow>
   (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ x y"
  by (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl tranclp_into_rtranclp)

lemma q31:
  "list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys"
  by (smt list.rel_mono_strong rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl rtranclpD rtranclp_induct tranclp_into_rtranclp)

lemma q32:
  "list_all2 (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys"
  by (smt list_all2_conv_all_nth mono_rtranclp rtranclpD tranclp.r_into_trancl tranclp_into_rtranclp)



lemma q41:
  " (\<And>x y. x \<in> set zs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> P x y) zs ys \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
    ys \<noteq> zs \<Longrightarrow>
    False"
  by (metis (mono_tags, lifting) list_all2_antisym2 tranclp.r_into_trancl)

lemma q42:
  " (\<And>x y. x \<in> set zs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) zs ys \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
    ys \<noteq> zs \<Longrightarrow>
    False"
  by (metis (mono_tags, lifting) list_all2_antisym2)

lemma q43:
  " (\<And>x y. x \<in> set zs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ zs ys \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
    ys \<noteq> zs \<Longrightarrow>
    False"
  apply (drule q31)
  by (metis (mono_tags, lifting) list_all2_antisym2)



lemma sublist_trans2:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs zs"
  unfolding sublist_def
  apply auto
  apply (smt linear list_all2_antisym2 list_all2_lengthD take_all)
  by (smt list_all2_take_length_trans tranclp.r_into_trancl tranclp_trans)

lemma sublist_trans3:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  unfolding sublist_def
  apply auto
  apply (drule q31)
  apply (smt linear list_all2_antisym2 list_all2_lengthD take_all)
  apply (smt list_all2_take_length_trans tranclp.r_into_trancl tranclp_trans)
  done

lemma trancl_subtype_C_C:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys"
  using C_functor tranclp_fun_preserve_gen_1a by fastforce

lemma q51:
  "acyclic_in subtype (set xs) \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y) ys zs \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs zs"
  apply (rule sublist_trans3)
  apply (meson tranclp.trancl_into_trancl)
  by auto

lemma trancl_subtype_C_C''''':
  "(sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in (\<lambda>x y. x \<sqsubset> y) (set xs) \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis (mono_tags, lifting) sublist_mono tranclp.r_into_trancl)
  using q51 by blast

lemma trancl_subtype_C_C'''''':
  "(sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in (\<lambda>x y. x = y \<or> x \<sqsubset> y) (set xs) \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis (mono_tags, lifting) sublist_mono tranclp.r_into_trancl)
  by (meson Nitpick.rtranclp_unfold sublist_trans)
(*  by (metis (mono_tags, lifting) r_into_rtranclp sublist_trans)*)
(*  by (metis (mono_tags) sublist_trans tranclp.r_into_trancl)*)
(*  apply (metis sublist_mono tranclp.r_into_trancl)
  by (metis (full_types) sublist_trans tranclp.trancl_into_trancl)*)

lemma trancl_subtype_C_C''':
  "sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>*\<^sup>* xs ys"
  by (metis (no_types, lifting) sublist_mono tranclp_into_rtranclp)

lemma q1:
  "(\<lambda>x y. x = y \<or> f x y)\<^sup>+\<^sup>+ x y \<Longrightarrow> (\<lambda>x y. f x y)\<^sup>*\<^sup>* x y"
  by (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclp_idemp tranclp_into_rtranclp) 

lemma q2:
  "(\<lambda>x y. f x y)\<^sup>*\<^sup>* x y \<Longrightarrow> (\<lambda>x y. x = y \<or> f x y)\<^sup>+\<^sup>+ x y"
  by (metis (mono_tags, lifting) mono_rtranclp rtranclpD tranclp.r_into_trancl)

lemma q:
  "(\<lambda>x y. x = y \<or> f x y)\<^sup>+\<^sup>+ x y = (\<lambda>x y. f x y)\<^sup>*\<^sup>* x y"
  by (metis (full_types) q1 q2)


lemma trancl_subtype_C_C'''':
  "sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist (\<lambda>x y. x \<sqsubset> y)\<^sup>*\<^sup>* xs ys"
  unfolding q
  by simp
(*  by (smt Nitpick.rtranclp_unfold mono_rtranclp r_into_rtranclp rtranclp_idemp sublist_mono trancl_subtype_C_C''')*)

lemma q11:
  "acyclic_in (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs \<Longrightarrow>
   acyclic_in (\<lambda>x y. x \<sqsubset> y) xs"
  by (simp add: tranclp.r_into_trancl)


(*
lemma trancl_subtype_C_C'''':
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in subtype (set xs) \<Longrightarrow>
   sublist subtype\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono tranclp.r_into_trancl)
  by (metis (full_types) sublist_trans tranclp.trancl_into_trancl)
*)
(*
lemma trancl_subtype_C_C'':
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in subtype (set xs) \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* xs ys"
  by (metis r_into_rtranclp reflclp_tranclp rtranclp_idemp rtranclp_reflclp sublist_mono trancl_subtype_C_C'''')

lemma trancl_subtype_C_C''':
  "(sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in (\<lambda>x y. x = y \<or> x \<sqsubset> y) (set xs) \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>*\<^sup>* xs ys"
*)

lemma trancl_subtype_C_C''''''':
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   acyclic_in (\<lambda>x y. x \<sqsubset> y) (set xs) \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* xs ys"
  by (simp add: trancl_subtype_C_C trancl_subtype_C_C'''' trancl_subtype_C_C''''')

lemma sublist_subtype_into_rtranclp:
  "sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* xs ys"
  by (metis (mono_tags, lifting) Nitpick.rtranclp_unfold r_into_rtranclp sublist_mono)

lemma trancl_subtype_C_x':
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   acyclic_in (\<lambda>x y. x \<sqsubset> y) (set xs) \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> sublist subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis (no_types, lifting) sublist_subtype_into_rtranclp subtype.simps t.distinct(3) t.inject)
  by (metis subtype.cases t.distinct(4) trancl_subtype_C_C''''''' tranclp.trancl_into_trancl)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct x arbitrary: y)
  apply auto[1]
  apply auto[1]
  by (meson sublist_def trancl_subtype_C_C''''''' tranclp_trans)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> sublist subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  using trancl_subtype_acyclic trancl_subtype_C_x' by blast

end

theory Tuple
  imports Main "Transitive_Closure_Ext"
    "~~/src/HOL/Library/Finite_Map"
begin

definition subtuple where
  "subtuple f xs ys \<equiv>
    xs \<noteq> ys \<and> fmdom ys |\<subseteq>| fmdom xs \<and>
    (\<forall>y. y |\<in>| fmdom ys \<longrightarrow> (\<exists>a b. fmlookup xs y = Some a \<and> fmlookup ys y = Some b \<and> f a b))"

lemma subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> y \<in> fmran' ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   subtuple f xs ys \<longrightarrow> subtuple g xs ys"
  by (metis fmran'I subtuple_def)

lemma subtuple_code [code]:
  "subtuple f xs ys \<longleftrightarrow>
    xs \<noteq> ys \<and> fmdom ys |\<subseteq>| fmdom xs \<and>
    fBall (fmdom ys)
    (\<lambda>y. (case (fmlookup xs y, fmlookup ys y) of
      (Some a, Some b) \<Rightarrow> f a b | _ \<Rightarrow> False))"
  unfolding subtuple_def fBall_alt_def
  apply auto
  by (metis (mono_tags, lifting) fmdomE fset_rev_mp option.simps(5))

lemma subtuple_antisym:
  "subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> f \<tau> \<sigma> \<and> \<not> f \<sigma> \<tau>) \<pi> \<pi>' \<Longrightarrow>
   subtuple (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> f \<tau> \<sigma>) \<pi>' \<pi> \<Longrightarrow> False"
  unfolding subtuple_def
  apply auto
  by (metis fmap_ext fmlookup_restrict_fset fmrestrict_fset_dom option.inject)

abbreviation "acyclic_in R xs \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

lemma subtuple_trans:
  "acyclic_in P (fmran' xs) \<Longrightarrow>
   subtuple P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> subtuple P ys zs \<Longrightarrow> subtuple P\<^sup>+\<^sup>+ xs zs"
  unfolding subtuple_def
  apply auto
  apply (metis fmap_ext fmlookup_restrict_fset fmran'I fmrestrict_fset_dom option.inject tranclp.trancl_into_trancl)
  by (metis fset_mp option.inject tranclp.trancl_into_trancl)

lemma subtuple_trans2:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  unfolding subtuple_def eq_trancl
  apply auto
  apply (smt fmap_ext fmdom_notD fmran'I option.inject)
  by (metis fset_rev_mp option.inject tranclp.r_into_trancl tranclp.trancl_into_trancl)

lemma subtuple_trans3:
  "acyclic_in P (fmran' xs) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply (rule_tac ?ys="ys" in subtuple_trans2)
  apply (meson notin_fset tranclp.trancl_into_trancl)
  by auto


(*
definition "subtuple f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 f (take (length ys) xs) ys"

lemma subtuple_mono [mono]:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow> 
   subtuple f xs ys \<longrightarrow> subtuple g xs ys"
  by (metis (no_types, lifting) in_set_takeD list.rel_mono_strong subtuple_def)

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

lemma subtuple_trans:
  "acyclic_in P (set xs) \<Longrightarrow>
   subtuple P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> subtuple P ys zs \<Longrightarrow> subtuple P\<^sup>+\<^sup>+ xs zs"
  unfolding subtuple_def
  apply auto
  apply (frule list_all2_lengthD)
  apply (unfold length_take)
  apply (smt list_all2_antisym2 list_all2_lengthD min.cobounded1 take_all tranclp.r_into_trancl tranclp_trans)
  by (smt list_all2_mono list_all2_take_length_trans tranclp.r_into_trancl tranclp_trans)

lemma subtuple_trans2:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  unfolding subtuple_def eq_trancl
  apply auto
  apply (smt linear list_all2_antisym2 list_all2_lengthD take_all)
  apply (smt list_all2_take_length_trans tranclp.r_into_trancl tranclp_trans)
  done

lemma subtuple_trans3:
  "acyclic_in P (set xs) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply (rule subtuple_trans2)
  apply (meson tranclp.trancl_into_trancl)
  by auto
*)
(*
lemma subtuple_subtype_into_rtranclp:
  "subtuple (\<lambda>x y. x = y \<or> P x y) xs ys \<Longrightarrow>
   subtuple P\<^sup>*\<^sup>* xs ys"
  by (metis (mono_tags, lifting) Nitpick.rtranclp_unfold r_into_rtranclp subtuple_mono)
*)
end

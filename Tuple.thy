theory Tuple
  imports Main "Transitive_Closure_Ext"
    "~~/src/HOL/Library/Finite_Map"
begin

(* TODO: Заменить на fmrel_on_fset? *)
abbreviation
  "subtuple f xs ys \<equiv> fmrel f (fmrestrict_fset (fmdom ys) xs) ys"

abbreviation
  "strict_subtuple f xs ys \<equiv> xs \<noteq> ys \<and> subtuple f xs ys"

definition "t1 \<equiv> fmupd (1::nat) (1::nat) (fmupd (2::nat) (2::nat) fmempty)"
definition "t2 \<equiv> fmupd (3::nat) (3::nat) (fmupd (1::nat) (1::nat) (fmupd (2::nat) (1::nat) fmempty))"
definition "t3 \<equiv> fmupd (3::nat) (4::nat) (fmupd (1::nat) (1::nat) (fmupd (2::nat) (1::nat) fmempty))"

value "subtuple (\<le>) t1 t1"
value "subtuple (\<le>) t1 t2"
value "subtuple (\<le>) t2 t1"
value "subtuple (\<le>) t2 t3"
value "subtuple (\<le>) t3 t2"

lemma subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> y \<in> fmran' ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   subtuple f xs ys \<longrightarrow> subtuple g xs ys"
  by (metis (no_types, lifting) fmap.rel_mono_strong fmlookup_ran'_iff fmlookup_restrict_fset option.simps(3))

lemma strict_subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> y \<in> fmran' ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   strict_subtuple f xs ys \<longrightarrow> strict_subtuple g xs ys"
  using subtuple_mono by blast

lemma strict_subtuple_antisym:
  "strict_subtuple (\<lambda>x y. x = y \<or> f x y \<and> \<not> f y x) xs ys \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> f x y) ys xs \<Longrightarrow> False"
  apply auto
  by (smt fmap_ext fmdomE fmdom_notD fmdom_notI fmlookup_restrict_fset fmrel_cases fmrel_fmdom_eq option.inject)

abbreviation "acyclic_in R xs \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

lemma subtuple_trans:
  "acyclic_in P (fmran' xs) \<Longrightarrow>
   subtuple P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> subtuple P ys zs \<Longrightarrow> subtuple P\<^sup>+\<^sup>+ xs zs"
  by (smt fmdom_notI fmfilter_alt_defs(5) fmlookup_filter fmrelI fmrel_iff option.rel_sel tranclp.intros(2))

lemma strict_subtuple_trans:
  "acyclic_in P (fmran' xs) \<Longrightarrow>
   strict_subtuple P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> strict_subtuple P ys zs \<Longrightarrow> strict_subtuple P\<^sup>+\<^sup>+ xs zs"
  apply auto
  apply (smt fmap_ext fmfilter_alt_defs(5) fmlookup_filter fmran'I fmrel_iff option.collapse option.rel_sel tranclp.trancl_into_trancl)
  using subtuple_trans by blast

lemma subtuple_trans2:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  by (smt fmdom_notI fmlookup_restrict_fset fmrel_iff option.rel_sel tranclp.trancl_into_trancl)

lemma eq_trancl':
  "(\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) x y =
   (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ x y"
  by (simp add: eq_trancl)

lemma strict_subtuple_trans2:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply auto
  unfolding eq_trancl
  apply (smt ffmember_filter fmap_ext fmdomI fmdom_filter fmdom_notD fmdom_notI fmfilter_alt_defs(5) fmlookup_dom_iff fmlookup_restrict_fset fmran'I fmrel_fmdom_eq fmrel_iff fmrestrict_fset_dom option.inject option.rel_cases option.rel_sel option.sel)
  unfolding eq_trancl'
  using subtuple_trans2 by blast

lemma subtuple_trans3:
  "acyclic_in P (fmran' xs) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply (rule_tac ?ys="ys" in subtuple_trans2)
  apply (meson notin_fset tranclp.trancl_into_trancl)
  by auto

lemma strict_subtuple_trans3:
  "acyclic_in P (fmran' xs) \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply (rule_tac ?ys="ys" in strict_subtuple_trans2)
  apply (meson notin_fset tranclp.trancl_into_trancl)
  by auto

lemma fmrel_to_trancl:
  "fmrel P\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (fmrel P)\<^sup>+\<^sup>+ xs ys"
  sorry

(*
abbreviation
  "subtuple f xs ys \<equiv> fmrel f (fmrestrict_fset (fmdom ys) xs) ys"
*)

lemma subtuple_to_trancl':
  "subtuple (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   (\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  sorry

lemma subtype_Tuple_Tuple'_rev:
  "strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ \<pi> \<xi> \<Longrightarrow>
   acyclic_in direct_subtype (fmran' \<pi>) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ \<pi> \<xi>"
  sorry

lemma subtuple_to_trancl:
  "subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  sorry

lemma strict_subtuple_to_trancl':
  "strict_subtuple (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   (\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  sorry

lemma strict_subtuple_to_trancl:
  "strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  sorry


lemma fmrel_upd_rev:
  "fmrel R (fmupd k x xs) (fmupd k y ys) \<Longrightarrow>
   fmlookup xs k = None \<Longrightarrow>
   fmlookup ys k = None \<Longrightarrow>
   fmrel R xs ys"
  by (smt fmrel_iff fmupd_lookup option.rel_sel)
(*
lemma fmrel_induct
  [consumes 1, case_names Nil Cons, induct set: fmrel]:
  assumes P: "fmrel P xs ys"
  assumes Nil: "R fmempty fmempty"
  assumes Cons: "\<And>k x xs y ys.
    \<lbrakk>P x y; fmrel P xs ys; fmlookup xs k = None; fmlookup ys k = None; R xs ys\<rbrakk> \<Longrightarrow>
    R (fmupd k x xs) (fmupd k y ys)"
  shows "R xs ys"
using P Nil Cons
  apply (induct xs arbitrary: ys rule: fmap_induct)
  apply (metis fmdom'_empty fmrel_fmdom'_eq fmrestrict_set_dom fmrestrict_set_null)
(*  apply (induction xs arbitrary: ys)
  apply (metis (full_types) fmap_ext fmempty_lookup fmrel_cases option.simps(3))*)
sorry
(*  using P Nil Cons
  apply (induction "fmdom ys" arbitrary: ys rule: fset_induct_stronger)
  apply (metis fmrel_fmdom_eq fmrestrict_fset_dom fmrestrict_fset_null local.Nil)
  apply (induction xs)
  apply (metis finsert_not_fempty fmdom_empty fmrel_fmdom_eq)*)
*)

lemma fmrel_upd_rev_elim:
  "fmrel R (fmupd k x xs) (fmupd k y ys) \<Longrightarrow>
   fmlookup xs k = None \<Longrightarrow>
   fmlookup ys k = None \<Longrightarrow>
   (fmrel R xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: fmrel_upd_rev)

lemma fmrel_upd_rev_right:
  "fmrel R xs (fmupd k y ys) \<Longrightarrow>
   fmlookup ys k = None \<Longrightarrow>
   fmlookup xs' k = None \<Longrightarrow>
   xs = fmupd k x xs' \<Longrightarrow>
   (fmrel R xs' ys \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: fmrel_upd_rev)


abbreviation "tcf \<equiv> (\<lambda> v::(nat \<times> nat). (\<lambda> r::nat. snd v + r))"

interpretation tcf: comp_fun_commute tcf
proof 
  fix x y
  show "tcf y \<circ> tcf x = tcf x \<circ> tcf y"
  proof -
    fix z
    have "(tcf y \<circ> tcf x) z = snd y + snd x + z" by auto
    also have "(tcf x \<circ> tcf y) z = snd y + snd x + z" by auto
    ultimately have "(tcf y \<circ> tcf x) z = (tcf x \<circ> tcf y) z" by auto
    then show "(tcf y \<circ> tcf x) = (tcf x \<circ> tcf y)" by auto
  qed
qed

lemma ffold_rec_exp:
  assumes "k |\<in>| fmdom x"
    and "ky = (k, the (fmlookup (fmmap f x) k))"
  shows "ffold tcf 0 (fset_of_fmap (fmmap f x)) = 
        tcf ky (ffold tcf 0 ((fset_of_fmap (fmmap f x)) |-| {|ky|}))"
  using assms tcf.ffold_rec by auto

lemma elem_le_ffold:
  "k |\<in>| fmdom x \<Longrightarrow>
   f (the (fmlookup x k)) < Suc (ffold tcf 0 (fset_of_fmap (fmmap f x)))"
  by (subst ffold_rec_exp, auto)


end

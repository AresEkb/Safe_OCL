theory Tuple
  imports Main Transitive_Closure_Ext
    Finite_Map_Ext
begin

(* TODO: Заменить на fmrel_on_fset? *)
abbreviation
  "subtuple f xs ys \<equiv> fmrel_on_fset (fmdom ys) f xs ys"

abbreviation
  "strict_subtuple f xs ys \<equiv> subtuple f xs ys \<and> xs \<noteq> ys"

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
  by (smt fmran'I fmrel_on_fsetD fmrel_on_fsetI option.collapse option.rel_sel)
(*  by (metis (no_types, lifting) fmap.rel_mono_strong fmlookup_ran'_iff fmlookup_restrict_fset option.simps(3))*)

lemma strict_subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> y \<in> fmran' ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   strict_subtuple f xs ys \<longrightarrow> strict_subtuple g xs ys"
  using subtuple_mono by blast

lemma strict_subtuple_antisym:
  "strict_subtuple (\<lambda>x y. x = y \<or> f x y \<and> \<not> f y x) xs ys \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> f x y) ys xs \<Longrightarrow> False"
  apply auto
  by (smt fmap_ext fmdomE fmdom_notI fmfilter_alt_defs(5) fmlookup_filter fmrel_cases fmrel_fmdom_eq fmrel_on_fset_fmrel_restrict fmrestrict_fset_dom option.simps(1))
(*  by (smt fmap_ext fmdomE fmdom_notD fmdom_notI fmlookup_restrict_fset fmrel_cases fmrel_fmdom_eq option.inject)*)

(* TODO: Поменять аргументы местами *)
abbreviation "acyclic_on R xs \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

(* TODO: Определить аналогичный trans_on? *)
thm trans_def
thm transp_def

lemma subtuple_fmmerge2 [intro]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
   subtuple f xm (fmmerge g xm ym)"
  by (rule_tac ?S="fmdom ym" in fmrel_on_fsubset; auto)

lemma fmrel_trans:
  "(\<And>x y z. x \<in> fmran' xm \<Longrightarrow> P x y \<Longrightarrow> Q y z \<Longrightarrow> R x z) \<Longrightarrow>
   fmrel P xm ym \<Longrightarrow> fmrel Q ym zm \<Longrightarrow> fmrel R xm zm"
  unfolding fmrel_iff
  by (metis fmdomE fmdom_notD fmran'I option.rel_inject(2) option.rel_sel)

lemma fmrel_on_fset_trans:
  "(\<And>x y z. x \<in> fmran' xm \<Longrightarrow> P x y \<Longrightarrow> Q y z \<Longrightarrow> R x z) \<Longrightarrow>
   fmrel_on_fset (fmdom ym) P xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom zm) Q ym zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) R xm zm"
  apply (rule fmrel_on_fsetI)
  unfolding option.rel_sel
  apply auto
  apply (meson fmdom_notI fmrel_on_fset_fmdom)
  by (metis fmdom_notI fmran'I fmrel_on_fsetD fmrel_on_fset_fmdom option.rel_sel option.sel)

lemma fmrel_acyclic:
  "acyclic_on P (fmran' xm) \<Longrightarrow>
   fmrel P\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel P ym xm \<Longrightarrow>
   xm = ym"
  by (metis (full_types) fmap_ext fmran'I fmrel_cases option.sel tranclp.trancl_into_trancl)

lemma fmrel_acyclic':
  "acyclic_on P (fmran' ym) \<Longrightarrow>
   fmrel P\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel P ym xm \<Longrightarrow>
   xm = ym"
  by (smt fmran'E fmran'I fmrel_acyclic fmrel_cases option.inject tranclp_into_tranclp2)

lemma fmrel_on_fset_acyclic:
  "acyclic_on P (fmran' xm) \<Longrightarrow>
   fmrel_on_fset (fmdom ym) P\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom xm) P ym xm \<Longrightarrow>
   xm = ym"
  by (smt fmap_ext fmdom_filter fmfilter_alt_defs(5) fmlookup_filter fmrel_acyclic
          fmrel_fmdom_eq fmrel_on_fset_fmrel_restrict fmrestrict_fset_dom)

lemma fmrel_on_fset_acyclic':
  "acyclic_on P (fmran' ym) \<Longrightarrow>
   fmrel_on_fset (fmdom ym) P\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom xm) P ym xm \<Longrightarrow>
   xm = ym"
  by (smt fBall_alt_def fmlookup_dom_iff fmlookup_ran'_iff fmrel_on_fset_acyclic
          fmrel_on_fset_alt_def fmrel_on_fset_fmdom option.simps(11) tranclp_into_tranclp2)

lemma fmrel_trans':
  "fmrel P\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmrel P ym zm \<Longrightarrow> fmrel P\<^sup>+\<^sup>+ xm zm"
  by (rule fmrel_trans, auto)

lemma fmrel_on_fset_trans':
  "fmrel_on_fset (fmdom ym) P\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom zm) P ym zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) P\<^sup>+\<^sup>+ xm zm"
  by (rule fmrel_on_fset_trans, auto)

lemma strict_subtuple_trans:
  "acyclic_on P (fmran' xs) \<Longrightarrow>
   strict_subtuple P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> strict_subtuple P ys zs \<Longrightarrow> strict_subtuple P\<^sup>+\<^sup>+ xs zs"
  apply auto
  apply (rule fmrel_on_fset_trans, auto)
  using fmrel_on_fset_acyclic by auto

(*
lemma subtuple_trans2:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  by (smt fmdom_notD fmdom_notI fmrel_on_fsetD fmrel_on_fsetI option.rel_sel tranclp.trancl_into_trancl)
(*  by (smt fmdom_notI fmlookup_restrict_fset fmrel_iff option.rel_sel tranclp.trancl_into_trancl)*)
*)
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
  using fmrel_on_fset_trans' apply blast
  unfolding eq_trancl
  by (smt fmap_ext fmlookup_restrict_fset fmran'I fmrel_fmdom_eq fmrel_iff
          fmrel_on_fset_fmrel_restrict fmrestrict_fset_dom option.inject option.rel_cases)
(*  unfolding fmrel_on_fset_fmrel_restrict fmrestrict_fset_dom fmrel_iff fmlookup_restrict_fset
  by (smt fmap_rel_eq_rev fmdomE fmdom_notD fmran'I fmrelI option.rel_inject(2) option.rel_sel)*)
(*
lemma subtuple_trans3:
  "acyclic_on P (fmran' xs) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply (rule_tac ?ys="ys" in subtuple_trans2)
  apply (meson notin_fset tranclp.trancl_into_trancl)
  by auto
*)
lemma strict_subtuple_trans3:
  "acyclic_on P (fmran' xs) \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs zs"
  apply (rule_tac ?ys="ys" in strict_subtuple_trans2)
  apply (meson notin_fset tranclp.trancl_into_trancl)
  by auto

(* Возможно, стоит везде использовать этот предикат *)
thm transp_def
term transp
thm Finite_Map.fmap.rel_transp
(*
Это обратное отношение. Обратные отношения использовались при доказательстве
транзитивности для list_all2, возможно и тут пригодятся
Finite_Map.Finite_Map.fmap.rel_conversep: fmrel ?R\<inverse>\<inverse> = (fmrel ?R)\<inverse>\<inverse>
Finite_Map.Finite_Map.fmap.rel_flip: fmrel ?R\<inverse>\<inverse> ?a ?b = fmrel ?R ?b ?a
*)
thm fmrel_on_fset_fmrel_restrict fmrel_restrict_fset fmrelD

lemma fmrel_trancl_unfold:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmrel f\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)
  using fmrel_trans' by blast

lemma fmrel_trancl_fmdom_eq:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmdom xm = fmdom ym"
  by (induct rule: tranclp_induct; simp add: fmrel_fmdom_eq)


lemma rel_option_to_trancl:
  "rel_option P\<^sup>+\<^sup>+ (fmlookup xm x) (fmlookup ym x) \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (\<lambda>m n. rel_option P (fmlookup m x) (fmlookup n x))\<^sup>+\<^sup>+ xm ym"
  apply (erule option.rel_cases)
  apply (simp add: tranclp.r_into_trancl)
  sorry
(*
proof -
  obtain z where "P xa z" and
    "(\<lambda>m n. rel_option P (fmlookup m x) (fmlookup n x))\<^sup>+\<^sup>+ (fmupd x z fmempty) ym"
  apply (rule_tac ?b="z" in rtranclp_into_tranclp2)

    term fmupd
*)
  thm option.rel_cases rtranclp_into_tranclp2
(*
lemma q:
  assumes as_r: "(\<forall>x. P x x)"
  shows "(\<And>x. P x x) \<Longrightarrow>
       fmlookup xm x = Some xa \<Longrightarrow>
       fmlookup ym x = Some y \<Longrightarrow>
       P\<^sup>+\<^sup>+ xa y \<Longrightarrow>
       (\<lambda>m n. rel_option P (fmlookup m x)
               (fmlookup n x))\<^sup>+\<^sup>+
        xm ym"
proof -
  from as_r obtain zm where "(\<lambda>m n. rel_option P (fmlookup m x) (fmlookup n x)) xm zm" and
    "(\<lambda>m n. rel_option P (fmlookup m x) (fmlookup n x))\<^sup>+\<^sup>+ zm ym"
*)

(*  by (metis (no_types, lifting) fmran'I option.rel_cases option.rel_sel tranclp.r_into_trancl)*)
(*
lemma q:
  "\<forall>x. f P\<^sup>+\<^sup>+ x m n \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (\<And>x. f P\<^sup>+\<^sup>+ x m n \<Longrightarrow> (\<lambda>m n. f P x m n)\<^sup>+\<^sup>+ m n) \<Longrightarrow>
   (\<lambda>m n. \<forall>x. f P x m n)\<^sup>+\<^sup>+ m n"
nitpick
*)
thm fBallE

thm fmrel_on_fset_fmdom

(*   (\<And>x y. x \<in> fmran' xm \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>*)

(*
  Transitive_Closure.converse_tranclp_induct:
    ?r\<^sup>+\<^sup>+ ?a ?b \<Longrightarrow>
    (\<And>y. ?r y ?b \<Longrightarrow> ?P y) \<Longrightarrow> (\<And>y z. ?r y z \<Longrightarrow> ?r\<^sup>+\<^sup>+ z ?b \<Longrightarrow> ?P z \<Longrightarrow> ?P y) \<Longrightarrow> ?P ?a
*)

thm tranclp_induct

lemma q:
  "r\<^sup>+\<^sup>+ (fmlookup a x) (fmlookup b x) \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. r (fmlookup a x) (fmlookup y x) \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z.
     (\<lambda>m n. r (fmlookup m x) (fmlookup n x))\<^sup>+\<^sup>+ a y \<Longrightarrow>
     r (fmlookup y x) (fmlookup z x) \<Longrightarrow>
     P y \<Longrightarrow> P z) \<Longrightarrow>
   P b"
  nitpick

lemma q:
  "rel_option r\<^sup>+\<^sup>+ (fmlookup a x) (fmlookup b x) \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. rel_option r (fmlookup a x) (fmlookup y x) \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z.
     (\<lambda>m n. rel_option r (fmlookup m x) (fmlookup n x))\<^sup>+\<^sup>+ a y \<Longrightarrow>
     rel_option r (fmlookup y x) (fmlookup z x) \<Longrightarrow>
     P y \<Longrightarrow> P z) \<Longrightarrow>
   P b"


lemma fmrel_tranclp_induct':
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. fmrel r a y \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. (fmrel r)\<^sup>+\<^sup>+ a y \<Longrightarrow> fmrel r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
  apply (unfold fmrel_iff)
  apply (auto)

  thm fmrelI fmrel_code fmap.rel_mono_strong fmrel_cases fmrel_iff


lemma fmrel_tranclp_trans_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>x y. fmrel r x y \<Longrightarrow> P x y) \<Longrightarrow>
   (\<And>x y z. fmrel r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow> P a b"
  apply (frule_tac ?zm="a" in fmrel_trans)

lemma fmrel_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. fmrel r a y \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. fmrel r\<^sup>+\<^sup>+ a y \<Longrightarrow> fmrel r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
  apply (frule_tac ?P="r\<^sup>+\<^sup>+" and ?xm="a" and ?ym="b" in fmrel_trans)

  
  apply (unfold fmrel_code)
  apply auto
  apply (unfold fBall_alt_def)
  apply (erule allE)
  apply (erule allE)
  apply auto


lemma fmrel_tranclp_induct:
  assumes as_r: "\<forall>x. r x x"
  shows
    "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
     (\<And>y. fmrel r a y \<Longrightarrow> P y) \<Longrightarrow>
     (\<And>y z. fmrel r\<^sup>+\<^sup>+ a y \<Longrightarrow> fmrel r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
  apply (frule_tac ?P="r\<^sup>+\<^sup>+" and ?xm="a" in fmrel_trans)
(*  apply (unfold fmrel_code)
  apply auto
  apply (erule fBallE)
  apply (unfold fmrel_iff)
  apply auto*)

  thm fmrelI fmrel_code fmap.rel_mono_strong fmrel_cases

proof -
  from as_r obtain zm where 
      lp_xm_zm: "fmrel r a zm" and lp_pp_xm_zm: "fmrel r\<^sup>+\<^sup>+ zm b"
  
  apply (frule_tac ?zm="a" in fmrel_trans')
  apply (simp add: fmap.rel_refl)


lemma fmrel_converse_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>y. fmrel r y b \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. fmrel r y z \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ z b \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow> P a"
  apply (frule_tac ?zm="a" in fmrel_trans')

lemma fmrel_to_trancl:
  "fmrel P\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (fmrel P)\<^sup>+\<^sup>+ xm ym"
  apply (erule_tac ?r="P" in fmrel_tranclp_induct')
  apply auto

  apply (drule fmrel_trans')
  apply (rule rtranclp_into_tranclp2)
  apply (frule_tac ?xm="xm" in fmrel_on_fset_fmdom, simp)

  unfolding fmrel_code
  apply auto
  apply (erule fBallE)
  apply (erule fBallE)
  apply auto
(*
  unfolding fmrel_iff
  unfolding rel_option_iff option.case_eq_if
  apply auto*)
(*
  apply (drule fmrelD)
  apply auto
  apply (erule option.rel_cases)
*)

lemma subtuple_to_trancl':
  "subtuple (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   acyclic_on P (fmran' xs) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  apply (rule rtranclp_into_tranclp2)

  apply (unfold fmrel_on_fset_fmrel_restrict)
  apply auto

lemma subtuple_to_trancl':
  "subtuple (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   (\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  apply (unfold fmrel_on_fset_fmrel_restrict)
  apply auto

  unfolding fmmerge_def fmap_of_list.abs_eq map_of_map_restrict

  apply auto

(* Использует только эта теорема, в первую очередь нужно доказать её *)
lemma subtype_Tuple_Tuple'_rev:
  "strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ \<pi> \<xi> \<Longrightarrow>
   acyclic_on P (fmran' \<pi>) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ \<pi> \<xi>"
  sorry
(*
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
*)

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


end

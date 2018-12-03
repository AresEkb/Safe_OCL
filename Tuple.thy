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

lemma trancl_to_fmrel:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmrel f\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)
  using fmrel_trans' by blast

lemma fmrel_trancl_fmdom_eq:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmdom xm = fmdom ym"
  by (induct rule: tranclp_induct; simp add: fmrel_fmdom_eq)


lemma fmap_eqdom_Cons1:
  assumes as_1: "fmlookup xm i = None"
    and as_2: "fmdom (fmupd i x xm) = fmdom ym"  
    and as_3: "fmrel R (fmupd i x xm) ym" 
  shows 
    "(\<exists>z zm. 
    fmlookup zm i = None \<and> ym = (fmupd i z zm) \<and> R x z \<and> fmrel R xm zm)"
proof - 
  from as_1 as_2 as_3 obtain y where y: "fmlookup ym i = Some y"
    by force
  obtain z zm where z_zm: "ym = (fmupd i z zm) \<and> fmlookup zm i = None"
    using y by (smt fmap_ext fmlookup_drop fmupd_lookup)
  {
    assume "\<not>R x z"
    with as_1 z_zm have "\<not>fmrel R (fmupd i x xm) ym"
      by (metis fmrel_iff fmupd_lookup option.simps(11))
  }
  with as_3 have c3: "R x z" by auto
  {
    assume "\<not>fmrel R xm zm"
    with as_1 have "\<not>fmrel R (fmupd i x xm) ym" 
      by (metis fmrel_iff fmupd_lookup option.rel_sel z_zm)
  }
  with as_3 have c4: "fmrel R xm zm" by auto
  from z_zm c3 c4 show ?thesis by auto
qed

lemma fmap_eqdom_induct [consumes 2, case_names nil step]:
  assumes R: "fmrel R xm ym"
    and dom_eq: "fmdom xm = fmdom ym"
    and nil: "P (fmap_of_list []) (fmap_of_list [])"
    and step: 
    "\<And>x xm y ym i. 
    \<lbrakk>R x y; fmrel R xm ym; fmdom xm = fmdom ym; P xm ym\<rbrakk> \<Longrightarrow> 
    P (fmupd i x xm) (fmupd i y ym)"
  shows "P xm ym"
  using R dom_eq
proof(induct xm arbitrary: ym)
  case fmempty
  then show ?case
    by (metis fempty_iff fmdom_empty fmempty_of_list fmfilter_alt_defs(5) 
        fmfilter_false fmrestrict_fset_dom local.nil)
next
  case (fmupd i x xm) show ?case 
  proof -
    from fmupd.prems(1) obtain y where y: "fmlookup ym i = Some y"
      by (metis fmupd.prems(1) fmrel_cases fmupd_lookup option.discI)
    from fmupd.hyps(2) fmupd.prems(2) fmupd.prems(1) obtain z zm where 
      zm_i_none: "fmlookup zm i = None" and
      ym_eq_z_zm: "ym = (fmupd i z zm)" and 
      R_x_z: "R x z" and
      R_xm_zm: "fmrel R xm zm"
      using fmap_eqdom_Cons1 by metis
    then have dom_xm_eq_dom_zm: "fmdom xm = fmdom zm" 
      using fmrel_fmdom_eq by blast  
    with R_xm_zm fmupd.hyps(1) have P_xm_zm: "P xm zm" by blast
    from R_x_z R_xm_zm dom_xm_eq_dom_zm P_xm_zm have 
      "P (fmupd i x xm) (fmupd i z zm)" 
      by (rule step)
    then show ?thesis by (simp add: ym_eq_z_zm)
  qed
qed

lemma fmrel_to_rtrancl:
  assumes as_r: "(\<And>x. r x x)" 
    and rel_rpp_xm_ym: "(fmrel r\<^sup>*\<^sup>*) xm ym" 
  shows "(fmrel r)\<^sup>*\<^sup>* xm ym"
proof-
  from rel_rpp_xm_ym have dom_xm_eq_dom_ym: "fmdom xm = fmdom ym" 
    using fmrel_fmdom_eq by blast
  from rel_rpp_xm_ym dom_xm_eq_dom_ym show "(fmrel r)\<^sup>*\<^sup>* xm ym"
  proof(induct rule: fmap_eqdom_induct)
    case nil then show ?case by auto
  next
    case (step x xm y ym i) show ?case
    proof -
      from as_r have lp_xs_xs: "fmrel r xm xm" by (simp add: fmap.rel_refl)
      from step.hyps(1) have x_xs_y_zs: 
        "(fmrel r)\<^sup>*\<^sup>* (fmupd i x xm) (fmupd i y xm)"
      proof(induction rule: rtranclp_induct)
        case base then show ?case by simp
      next
        case (step y z) then show ?case 
        proof -
          have rt_step_2: "(fmrel r)\<^sup>*\<^sup>* (fmupd i y xm) (fmupd i z xm)" 
            by (rule r_into_rtranclp, simp add: fmrel_upd lp_xs_xs step.hyps(2))
          from step.IH rt_step_2 show ?thesis by (rule rtranclp_trans) 
        qed      
      qed
      from step.hyps(4) have "(fmrel r)\<^sup>*\<^sup>* (fmupd i y xm) (fmupd i y ym)"
      proof(induction rule: rtranclp_induct)
        case base then show ?case by simp
      next
        case (step ya za) show ?case
        proof -
          have rt_step_2: "(fmrel r)\<^sup>*\<^sup>* (fmupd i y ya) (fmupd i y za)" 
            by (rule r_into_rtranclp, simp add: as_r fmrel_upd step.hyps(2)) 
          from step.IH rt_step_2 show ?thesis by (rule rtranclp_trans)
        qed
      qed
      with x_xs_y_zs show ?thesis by simp
    qed
  qed
qed

lemma fmrel_to_trancl:
  assumes as_r: "(\<And>x. r x x)" 
    and rel_rpp_xm_ym: "(fmrel r\<^sup>+\<^sup>+) xm ym" 
  shows "(fmrel r)\<^sup>+\<^sup>+ xm ym" 
  by (metis as_r fmrel_to_rtrancl fmap.rel_mono_strong fmap.rel_refl 
      r_into_rtranclp reflclp_tranclp rel_rpp_xm_ym rtranclpD rtranclp_idemp 
      rtranclp_reflclp tranclp.r_into_trancl)

lemma fmrel_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. fmrel r a y \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. (fmrel r)\<^sup>+\<^sup>+ a y \<Longrightarrow> fmrel r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
  by (smt fmrel_to_trancl tranclp_induct)

lemma fmrel_tranclp_trans_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>x y. fmrel r x y \<Longrightarrow> P x y) \<Longrightarrow>
   (\<And>x y z. fmrel r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow> P a b"
  by (smt fmrel_to_trancl trancl_to_fmrel tranclp_trans_induct)

lemma fmrel_converse_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. fmrel r y b \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. fmrel r y z \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ z b \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow> P a"
  by (smt converse_tranclp_induct fmrel_to_trancl trancl_to_fmrel)

lemma trancl_to_fmrel':
  "(\<lambda>xm ym. fmrel r (f xm) (g ym))\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (\<And>xm ym. fmrel r (f xm) (g ym) \<Longrightarrow> fmrel r (g xm) (g ym)) \<Longrightarrow>
   fmrel r\<^sup>+\<^sup>+ (f xm) (g ym)"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)
  apply (rule_tac ?P="r\<^sup>+\<^sup>+" and ?Q="r" and ?ym="g y" in fmrel_trans, auto)
  done
(*
lemma trancl_to_fmrel':
  "(\<lambda>xm ym. fmrel r (f xm) (g ym))\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (\<And>xm. fmsubset (f xm) xm) \<Longrightarrow>
   fmrel r\<^sup>+\<^sup>+ (f xm) (g ym)"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)

lemma fmrel_to_trancl'':
  "fmrel r\<^sup>+\<^sup>+ (f xm) (g ym) \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<lambda>xm ym. fmrel r (f xm) (g ym))\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)
*)

lemma trancl_to_subtuple:
  "(subtuple r)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   subtuple r\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (metis subtuple_mono tranclp.r_into_trancl)
  using fmrel_on_fset_trans' by auto

thm fmrel_to_trancl
thm trancl_to_fmrel

lemma fmrel_to_subtuple:
  "fmrel r xm ym \<Longrightarrow>
   subtuple r xm ym"
  apply (unfold fmrel_on_fset_fmrel_restrict)
  by blast

lemma subtuple_to_fmrel:
  "subtuple r xm ym =
   fmrel r (fmrestrict_fset (fmdom ym) xm) ym"
  by (simp add: fmrel_on_fset_fmrel_restrict)

lemma subtuple_to_fmrel_trancl:
  "(subtuple r)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (fmrel r)\<^sup>+\<^sup>+ (fmrestrict_fset (fmdom ym) xm) ym"
  apply (drule trancl_to_subtuple)
  apply (rule fmrel_to_trancl, simp)
  apply (unfold fmrel_on_fset_fmrel_restrict, auto)
  done

lemma fmrel_to_subtuple_trancl:
  "(fmrel r)\<^sup>+\<^sup>+ (fmrestrict_fset (fmdom ym) xm) ym \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (subtuple r)\<^sup>+\<^sup>+ xm ym"
  apply (frule trancl_to_fmrel)
  apply (rule_tac ?r="r" in fmrel_tranclp_induct, auto)
  apply (metis (no_types, lifting) fmrel_fmdom_eq subtuple_to_fmrel tranclp.r_into_trancl)
  by (meson fmrel_to_subtuple tranclp.simps)

lemma subtuple_to_trancl:
  "subtuple r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (subtuple r)\<^sup>+\<^sup>+ xm ym"
  apply (rule fmrel_to_subtuple_trancl)
  apply (unfold fmrel_on_fset_fmrel_restrict)
  apply (simp add: fmrel_to_trancl)
  apply simp
  done


lemma subtuple_to_trancl':
  "subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_on P (fmran' xs) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  using subtuple_to_trancl by auto

lemma eq_trancl_rev:
  "(\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) x y =
   (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ x y"
  by (simp add: eq_trancl)

lemma subtuple_to_trancl'':
  "subtuple (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   acyclic_on P (fmran' xs) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  apply (unfold eq_trancl_rev)
  apply (simp add: subtuple_to_trancl')
  done

lemma subtuple_to_trancl''':
  "subtuple (\<lambda>x y. x = y \<or> P\<^sup>+\<^sup>+ x y) xs ys \<Longrightarrow>
   (\<And>x y. x \<in> fmran' xs \<Longrightarrow> P\<^sup>+\<^sup>+ x y \<Longrightarrow> P y x \<Longrightarrow> False) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> P x y))\<^sup>+\<^sup>+ xs ys"
  apply (unfold eq_trancl_rev)
  apply (rule subtuple_to_trancl, auto)
  done

lemma q11:
  "r\<^sup>+\<^sup>+ x y \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   acyclicP r \<Longrightarrow>
   (\<lambda>x y. r x y \<and> x \<noteq> y)\<^sup>+\<^sup>+ x y"
  apply (erule tranclp_trans_induct)
  using acyclic_alt tranclp.r_into_trancl apply fastforce
  by auto
(*
lemma q:
  "acyclicP r \<Longrightarrow>
   acyclicP (\<lambda>xm ym. fmrel (\<lambda>x y. x = y \<or> r x y) xm ym \<and> xm \<noteq> ym)"
  unfolding acyclic_def
  apply auto

  thm acyclic_alt

lemma q:
  "fmrel (\<lambda>x y. x = y \<or> r x y)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   xm \<noteq> ym \<Longrightarrow>
   acyclic_on r (fmran' xm) \<Longrightarrow>
   (\<lambda>xm ym. fmrel (\<lambda>x y. x = y \<or> r x y) xm ym \<and> xm \<noteq> ym)\<^sup>+\<^sup>+ xm ym"
*)
(*
lemma q12:
  "(\<lambda>x y. x = y \<or> r x y)\<^sup>+\<^sup>+ x y \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   acyclicP r \<Longrightarrow>
   (\<lambda>x y. r x y \<and> x \<noteq> y)\<^sup>+\<^sup>+ x y"
  apply (erule tranclp_trans_induct)

lemma q12:
  "strict_subtuple r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   acyclic_on r (fmran' xm) \<Longrightarrow>
   (strict_subtuple r)\<^sup>+\<^sup>+ xm ym"
  by (metis (mono_tags, lifting) strict_subtuple_mono tranclp.r_into_trancl)
*)
(* Использует только эта теорема, в первую очередь нужно доказать её *)
(*
lemma subtype_Tuple_Tuple'_rev:
  "strict_subtuple (\<lambda>x y. x = y \<or> r x y)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   acyclic_on r (fmran' xm) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> r x y))\<^sup>+\<^sup>+ xm ym"
  apply (unfold fmrel_on_fset_fmrel_restrict)
  apply auto
*)

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

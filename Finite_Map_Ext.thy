section{* Finite Maps *}
theory Finite_Map_Ext
  imports Main "HOL-Library.Finite_Map"
begin

(*** Helper Lemmas **********************************************************)

subsection{* Helper Lemmas *}

lemma fmrel_on_fset_fmdom:
  "fmrel_on_fset (fmdom ym) f xm ym \<Longrightarrow>
   k |\<in>| fmdom ym \<Longrightarrow>
   k |\<in>| fmdom xm"
  by (metis fmdom_notD fmdom_notI fmrel_on_fsetD option.rel_sel)

lemma fmap_rel_eq_rev:
  "(xm = ym) = fmrel (=) xm ym"
  by (simp add: fmap.rel_eq)

(*** Finite Map Merge *******************************************************)

subsection{* Merge Operation *}

definition "fmmerge f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma fmdom_fmmerge [simp]:
  "fmdom (fmmerge g xm ym) = fmdom xm |\<inter>| fmdom ym"
  by (auto simp add: fmmerge_def fmdom_of_list)

lemma fmmerge_commut:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   fmmerge f xm ym = fmmerge f ym xm"
  apply (unfold fmap_rel_eq_rev)
  apply (rule fmrelI)
  unfolding fmmerge_def fmlookup_of_list
  apply (auto simp add: Option.rel_option_iff option.case_eq_if fmmerge_def
             fmlookup_of_list)
  apply (smt finterD1 fmdom_notI fmran'I map_eq_conv notin_fset option.collapse
             sorted_list_of_fset_simps(1) inf_commute)
  apply (smt finterD1 fmdom_notI fmran'I map_eq_conv notin_fset option.collapse
             sorted_list_of_fset_simps(1) inf_commute)
  apply (smt finterD2 fmdom_notI fmran'I map_eq_conv notin_fset option.collapse
             sorted_list_of_fset_simps(1) inf_commute
             fmlookup_of_list option.inject prod.inject)
  done

lemma map_of_map_inter_eq_Some:
  "map_of
    (map
      (\<lambda>k. (k, f k xm ym))
      (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))
    k = Some z \<Longrightarrow>
   \<exists>x y. fmlookup xm k = Some x \<and> fmlookup ym k = Some y"
  unfolding map_of_map_restrict
  apply auto
  using fmdom'_alt_def fmlookup_dom'_iff apply fastforce
  using fmdom'_alt_def fmlookup_dom'_iff apply fastforce
  done

lemma map_of_map_inter_eq_None:
  "map_of
    (map
      (\<lambda>k. (k, f k xm ym))
      (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))
    k = None \<Longrightarrow>
   fmlookup xm k = None \<or> fmlookup ym k = None"
  unfolding map_of_map_restrict
  apply auto
  by (metis (no_types, lifting) Int_iff comp_apply fmdom'_alt_def
            fmdom'_notD option.simps(3) restrict_map_def)

lemma fmrel_on_fset_fmmerge1 [intro]:
  "(\<And>x y z. z \<in> fmran' zm \<Longrightarrow> f x z \<Longrightarrow> f y z \<Longrightarrow> f (g x y) z) \<Longrightarrow>
   fmrel_on_fset (fmdom zm) f xm zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) f ym zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) f (fmmerge g xm ym) zm"
  unfolding fmmerge_def
  apply (rule fmrel_on_fsetI)
  apply (frule_tac ?xm="xm" in fmrel_on_fset_fmdom, simp)
  apply (frule_tac ?xm="ym" in fmrel_on_fset_fmdom, simp)
  unfolding fmlookup_of_list fmlookup_dom_iff
  apply auto
  apply (unfold option_rel_Some2)
  apply (rule_tac ?x="g aa ab" in exI)
  apply auto
  apply (auto simp add: map_of_map_restrict fmdom.rep_eq domI)
  by (metis fmdomI fmran'I fmrel_on_fsetD option.rel_inject(2))

lemma fmrel_on_fset_fmmerge2 [intro]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel_on_fset (fmdom ym) f xm (fmmerge g xm ym)"
  apply (rule fmrel_on_fsetI)
  apply (auto simp add: Option.rel_option_iff option.case_eq_if
          fmmerge_def fmlookup_of_list)
  apply (drule map_of_map_inter_eq_None; auto)
  apply (drule map_of_map_inter_eq_Some; auto)
  apply (frule map_of_map_inter_eq_Some; auto)
  apply (auto simp add: map_of_map_restrict fmdom.rep_eq domI fmran'I)
  done

(*** Acyclicity *************************************************************)

subsection{* Acyclicity *}

abbreviation "acyclic_on xs R \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> \<not> R\<^sup>+\<^sup>+ x x)"

lemma fmrel_acyclic:
  "acyclic_on (fmran' xm) r \<Longrightarrow>
   fmrel r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel r ym xm \<Longrightarrow>
   xm = ym"
  by (metis (full_types) fmap_ext fmran'I fmrel_cases option.sel
            tranclp.trancl_into_trancl)

lemma fmrel_acyclic':
  "acyclic_on (fmran' ym) r \<Longrightarrow>
   fmrel r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel r ym xm \<Longrightarrow>
   xm = ym"
  by (smt fmran'E fmran'I fmrel_acyclic fmrel_cases option.inject
          tranclp_into_tranclp2)

lemma fmrel_on_fset_acyclic:
  "acyclic_on (fmran' xm) r \<Longrightarrow>
   fmrel_on_fset (fmdom ym) r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom xm) r ym xm \<Longrightarrow>
   xm = ym"
  by (smt fmap_ext fmdom_filter fmfilter_alt_defs(5) fmlookup_filter
          fmrel_acyclic fmrel_fmdom_eq fmrel_on_fset_fmrel_restrict
          fmrestrict_fset_dom)

lemma fmrel_on_fset_acyclic':
  "acyclic_on (fmran' ym) r \<Longrightarrow>
   fmrel_on_fset (fmdom ym) r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom xm) r ym xm \<Longrightarrow>
   xm = ym"
  by (smt fBall_alt_def fmlookup_dom_iff fmlookup_ran'_iff
          fmrel_on_fset_acyclic fmrel_on_fset_alt_def fmrel_on_fset_fmdom
          option.simps(11) tranclp_into_tranclp2)

(*** Transitive Closures ****************************************************)

subsection{* Transitive Closures *}

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
  by (metis fmdom_notI fmran'I fmrel_on_fsetD fmrel_on_fset_fmdom
            option.rel_sel option.sel)

lemma trancl_to_fmrel:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmrel f\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)
  by (rule fmrel_trans; auto)

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
proof -
  from rel_rpp_xm_ym have dom_xm_eq_dom_ym: "fmdom xm = fmdom ym" 
    using fmrel_fmdom_eq by blast
  from rel_rpp_xm_ym dom_xm_eq_dom_ym show "(fmrel r)\<^sup>*\<^sup>* xm ym"
  proof (induct rule: fmap_eqdom_induct)
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
  "(\<And>x. r x x) \<Longrightarrow>
   fmrel r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (fmrel r)\<^sup>+\<^sup>+ xm ym" 
  by (metis fmrel_to_rtrancl fmap.rel_mono_strong fmap.rel_refl 
      r_into_rtranclp reflclp_tranclp rtranclpD rtranclp_idemp 
      rtranclp_reflclp tranclp.r_into_trancl)

lemma fmrel_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. fmrel r a y \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. (fmrel r)\<^sup>+\<^sup>+ a y \<Longrightarrow> fmrel r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
  apply (drule fmrel_to_trancl, simp)
  apply (erule tranclp_induct; simp)
  done

lemma fmrel_converse_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>y. fmrel r y b \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. fmrel r y z \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ z b \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow> P a"
  apply (drule fmrel_to_trancl, simp)
  apply (erule converse_tranclp_induct; simp add: trancl_to_fmrel)
  done

lemma fmrel_tranclp_trans_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (\<And>x y. fmrel r x y \<Longrightarrow> P x y) \<Longrightarrow>
   (\<And>x y z. fmrel r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   P a b"
  apply (drule fmrel_to_trancl, simp)
  apply (erule tranclp_trans_induct, simp)
  using trancl_to_fmrel by blast

(*** Finite Map Size Calculation ********************************************)

subsection{* Size Calculation *}

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

(*** Code Setup *************************************************************)

subsection{* Code Setup *}

abbreviation "fmmerge_fun f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. if k |\<in>| fmdom xm \<and> k |\<in>| fmdom ym
         then (k, f (the (fmlookup xm k)) (the (fmlookup ym k)))
         else (k, undefined))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma fmmerge_fun_simp [code_abbrev, simp]:
  "fmmerge_fun f xm ym = fmmerge f xm ym"
  unfolding fmmerge_def fmap_of_list.abs_eq map_of_map_restrict
  apply auto
  by (smt IntD1 IntD2 fmember.rep_eq inf_fset.rep_eq map_eq_conv
          map_of_map_restrict sorted_list_of_fset_simps(1))

end

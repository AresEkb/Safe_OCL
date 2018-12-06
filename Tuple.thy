theory Tuple
  imports Main Transitive_Closure_Ext
    Finite_Map_Ext
begin

abbreviation
  "subtuple f xm ym \<equiv> fmrel_on_fset (fmdom ym) f xm ym"

abbreviation
  "strict_subtuple f xm ym \<equiv> subtuple f xm ym \<and> xm \<noteq> ym"

definition "t1 \<equiv> fmupd (1::nat) (1::nat) (fmupd (2::nat) (2::nat) fmempty)"
definition "t2 \<equiv> fmupd (3::nat) (3::nat) (fmupd (1::nat) (1::nat) (fmupd (2::nat) (1::nat) fmempty))"
definition "t3 \<equiv> fmupd (3::nat) (4::nat) (fmupd (1::nat) (1::nat) (fmupd (2::nat) (1::nat) fmempty))"

value "subtuple (\<le>) t1 t1"
value "subtuple (\<le>) t1 t2"
value "subtuple (\<le>) t2 t1"
value "subtuple (\<le>) t2 t3"
value "subtuple (\<le>) t3 t2"

(*** Base Lemmas ************************************************************)

lemma fmrel_to_subtuple:
  "fmrel r xm ym \<Longrightarrow>
   subtuple r xm ym"
  apply (unfold fmrel_on_fset_fmrel_restrict)
  by blast

lemma subtuple_eq_fmrel_fmrestrict_fset:
  "subtuple r xm ym = fmrel r (fmrestrict_fset (fmdom ym) xm) ym"
  by (simp add: fmrel_on_fset_fmrel_restrict)

lemma subtuple_fmdom:
  "subtuple f xm ym \<Longrightarrow>
   subtuple g ym xm \<Longrightarrow>
   fmdom xm = fmdom ym"
  by (meson fmrel_on_fset_fmdom fset_eqI)

(*** Basic Properties *******************************************************)

lemma subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> y \<in> fmran' ym \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   subtuple f xm ym \<longrightarrow> subtuple g xm ym"
  apply (auto)
  apply (rule fmrel_on_fsetI)
  apply (drule_tac ?P="f" and ?m="xm" and ?n="ym" in fmrel_on_fsetD, simp)
  apply (erule option.rel_cases, simp)
  apply (auto simp add: option.rel_sel fmran'I)
  done

lemma strict_subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> y \<in> fmran' ym \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   strict_subtuple f xm ym \<longrightarrow> strict_subtuple g xm ym"
  using subtuple_mono by blast

lemma subtuple_antisym:
  "subtuple (\<lambda>x y. x = y \<or> f x y \<and> \<not> f y x) xm ym \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> f x y) ym xm \<Longrightarrow>
   xm = ym"
  apply (frule subtuple_fmdom, simp)
  apply (rule fmap_ext)
  apply (unfold subtuple_eq_fmrel_fmrestrict_fset)
  apply (erule_tac ?x="x" in fmrel_cases)
  apply force
  apply (erule_tac ?x="x" in fmrel_cases)
  apply force
  by (metis fmrestrict_fset_dom option.sel)

lemma strict_subtuple_antisym:
  "strict_subtuple (\<lambda>x y. x = y \<or> f x y \<and> \<not> f y x) xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> f x y) ym xm \<Longrightarrow> False"
  by (auto simp add: subtuple_antisym)

lemma subtuple_acyclic:
  "acyclic_on (fmran' xm) P \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> P x y) ym xm \<Longrightarrow>
   xm = ym"
  unfolding eq_trancl
  apply (frule subtuple_fmdom, simp)
  apply (unfold fmrel_on_fset_fmrel_restrict, simp)
  apply (rule fmap_ext)
  apply (erule_tac ?x="x" in fmrel_cases)
  apply (metis fmrestrict_fset_dom)
  apply (erule_tac ?x="x" in fmrel_cases)
  apply (metis fmrestrict_fset_dom)
  by (metis fmran'I fmrestrict_fset_dom option.inject tranclp.trancl_into_trancl)

lemma strict_subtuple_trans:
  "acyclic_on (fmran' xm) P \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y) ym zm \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> P x y)\<^sup>+\<^sup>+ xm zm"
  apply auto
  using fmrel_on_fset_trans' apply blast
  by (drule_tac ?ym="ym" in subtuple_acyclic; auto)

(*** Transitive Closure Unfolding *******************************************)

lemma trancl_to_subtuple:
  "(subtuple r)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   subtuple r\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (metis subtuple_mono tranclp.r_into_trancl)
  using fmrel_on_fset_trans' by auto

lemma fmrel_to_subtuple_trancl:
  "(fmrel r)\<^sup>+\<^sup>+ (fmrestrict_fset (fmdom ym) xm) ym \<Longrightarrow>
   (\<And>x. r x x) \<Longrightarrow>
   (subtuple r)\<^sup>+\<^sup>+ xm ym"
  apply (frule trancl_to_fmrel)
  apply (rule_tac ?r="r" in fmrel_tranclp_induct, auto)
  apply (metis (no_types, lifting) fmrel_fmdom_eq
          subtuple_eq_fmrel_fmrestrict_fset tranclp.r_into_trancl)
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

(*** Misc *******************************************************************)

lemma subtuple_rtrancl_to_trancl:
  "subtuple r\<^sup>*\<^sup>* xm ym \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> r x y)\<^sup>+\<^sup>+ xm ym"
  unfolding tranclp_into_rtranclp2
  by simp

lemma subtuple_fmmerge2 [intro]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
   subtuple f xm (fmmerge g xm ym)"
  by (rule_tac ?S="fmdom ym" in fmrel_on_fsubset; auto)

end

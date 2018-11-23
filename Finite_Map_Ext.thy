theory Finite_Map_Ext
  imports Main "~~/src/HOL/Library/Finite_Map"
begin

definition "fmmerge f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma fmdom_fmmerge [simp]:
  "fmdom (fmmerge g xm ym) = fmdom xm |\<inter>| fmdom ym"
  by (auto simp add: fmmerge_def fmdom_of_list)

lemma fmrel_on_fset_fmdom:
  "fmrel_on_fset (fmdom ym) f xm ym \<Longrightarrow>
   k |\<in>| fmdom ym \<Longrightarrow>
   k |\<in>| fmdom xm"
  by (metis fmdom_notD fmdom_notI fmrel_on_fsetD option.rel_sel)

lemma fmap_rel_eq_rev:
  "(xm = ym) = fmrel (=) xm ym"
  by (simp add: fmap.rel_eq)

lemma fmmerge_commut:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   fmmerge f xm ym = fmmerge f ym xm"
  apply (unfold fmap_rel_eq_rev)
  apply (rule fmrelI)
  unfolding fmmerge_def fmlookup_of_list
  apply (auto simp add: Option.rel_option_iff option.case_eq_if fmmerge_def fmlookup_of_list)
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
  apply (auto simp add: Option.rel_option_iff option.case_eq_if fmmerge_def fmlookup_of_list)
  apply (drule map_of_map_inter_eq_None; auto)
  apply (drule map_of_map_inter_eq_Some; auto)
  apply (frule map_of_map_inter_eq_Some; auto)
  apply (auto simp add: map_of_map_restrict fmdom.rep_eq domI fmran'I)
  done

(*** Finite Map size calculation ********************************************)

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

abbreviation "fmmerge' f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. if k |\<in>| fmdom xm \<and> k |\<in>| fmdom ym then (k,
        f (the (fmlookup xm k)) (the (fmlookup ym k))) else (k, undefined))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma fmmerge_eq [simp]:
  "fmmerge' f xm ym = fmmerge f xm ym"
  unfolding fmmerge_def fmap_of_list.abs_eq map_of_map_restrict
  apply auto
  by (smt IntD1 IntD2 fmember.rep_eq inf_fset.rep_eq map_eq_conv
          map_of_map_restrict sorted_list_of_fset_simps(1))


(*
datatype (plugins del: "size") t = A | B | C "(nat, t) fmap"

instantiation t :: size 
begin

term size_fmap

primrec size_t :: "t \<Rightarrow> nat" where
  "size_t A = 0"
| "size_t B = 0"
| "size_t (C xm) = Suc (ffold tcf 0 (fset_of_fmap (fmmap size_t xm)))"

instance ..

end

function sup_t (infixl "\<squnion>" 65) where
  "A \<squnion> _ = A"
| "B \<squnion> x = (if x = B then B else A)"
| "C xm \<squnion> x = (case x of C ym \<Rightarrow> C (fmmerge' (\<squnion>) xm ym) | _ \<Rightarrow> A)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(x, y). size y)")
  apply auto[1]
  apply auto[1]
  by (simp add: elem_le_ffold)
*)

end

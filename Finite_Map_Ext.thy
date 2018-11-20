theory Finite_Map_Ext
  imports Main "~~/src/HOL/Library/Finite_Map"
begin

(* Попробовать эту функцию size_fmap *)

definition "fmmerge f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma q21:
  "fmlookup xm k = Some x \<Longrightarrow>
   fmlookup ym k = Some y \<Longrightarrow>
   map_of
    (map (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
         (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))
    k = Some (f x y)"
  by (auto simp add: map_of_map_restrict fmdom.rep_eq domI)

thm map_of_map_restrict

lemma q22:
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

lemma q23:
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

lemma q61:
  "fmrel_on_fset (fmdom ym) f xm ym \<Longrightarrow>
   x |\<in>| fmdom ym \<Longrightarrow>
   x |\<in>| fmdom xm"
  by (metis fmdom_notD fmdom_notI fmrel_on_fsetD option.rel_sel)

lemma fmrel_on_fset_fmmerge1:
  "(\<And>x y z. z |\<in>| fmran zm \<Longrightarrow> f x z \<Longrightarrow> f y z \<Longrightarrow> f (g x y) z) \<Longrightarrow>
   fmrel_on_fset (fmdom zm) f xm zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) f ym zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) f (fmmerge g xm ym) zm"
  unfolding fmmerge_def
  apply (rule fmrel_on_fsetI)
  apply (frule_tac ?xm="xm" in q61, simp)
  apply (frule_tac ?xm="ym" in q61, simp)
  unfolding fmlookup_of_list fmlookup_dom_iff
  apply auto
  apply (unfold option_rel_Some2)
  apply (rule_tac ?x="g aa ab" in exI)
  apply auto
  apply (auto simp add: map_of_map_restrict fmdom.rep_eq domI)
  by (metis fmdomI fmranI fmrel_on_fsetD option.rel_inject(2))

lemma fmrel_on_fset_fmmerge2:
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel_on_fset (fmdom ym) f xm (fmmerge g xm ym)"
  apply (rule fmrel_on_fsetI)
  apply (auto simp add: Option.rel_option_iff option.case_eq_if fmmerge_def fmlookup_of_list)
  apply (drule q23; auto)
  apply (drule q22; auto)
  apply (frule q22; auto)
  apply (auto simp add: map_of_map_restrict fmdom.rep_eq domI fmranI)
  done

lemma fmdom_inter_commut:
  "sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym) =
   sorted_list_of_fset (fmdom ym |\<inter>| fmdom xm)"
  by (simp add: inf_commute)

lemma double_fmrestrict_fset_fmdom:
  "fmrestrict_fset (fmdom (fmrestrict_fset (fmdom xs) ys)) xs =
   fmrestrict_fset (fmdom ys) xs"
  unfolding fmfilter_alt_defs(5) fmdom_filter ffmember_filter
  by (metis (mono_tags, lifting) fmdomI fmfilter_cong)

lemma fmmerge_commut:
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   fmmerge f xm ym = fmmerge f ym xm"
  unfolding fmmerge_def
  sorry
(* fmap_of_list.abs_eq*)
(*
  apply (induct ym)
  prefer 2
proof -
  fix xma :: "('b, 'a) fmap"
  have "\<forall>f fa fb fc b. fmlookup fb b \<noteq> (None::'a option) \<or> b |\<notin>| fmdom (fmrestrict_fset (fmdom (fc::('b, 'c) fmap)) (fmmerge fa (f::(_, 'a) fmap) fb::(_, 'c) fmap))"
    by (metis (no_types) fmmerge_def q18)
  then show "fmmerge f xma fmempty = fmmerge f fmempty xma"
    by (metis (no_types) all_not_fin_conv fmdom_empty fmempty_lookup fmran_empty fmrel_fmdom_eq fmrestrict_fset_dom fmrestrict_fset_empty fmrestrict_fset_null subtuple_fmmerge)
next

  unfolding fmmerge_def fmap_of_list.abs_eq
  apply auto

  unfolding fmlookup_of_list fmrestrict_fset_def map_restrict_set_def
            map_filter_def
*)
  thm fmmerge_def fmrel_code fmlookup_of_list fmap_of_list.abs_eq

end

theory FMRelTest
  imports Main "~~/src/HOL/Library/Finite_Map"
begin

datatype t = A | B | C "(nat, t) fmap"

term rel_fun
thm fmrel_upd
thm Finite_Map.fmap.rel_mono_strong Finite_Map.fmap.rel_cong_simp Finite_Map.fmap.rel_cong
thm fmrel_cases

thm fmlookup_dom_iff fmlookup_filter fmlookup_restrict_fset

abbreviation
  "subtuple f xs ys \<equiv> fmrel f (fmrestrict_fset (fmdom ys) xs) ys"

abbreviation
  "strict_subtuple f xs ys \<equiv> xs \<noteq> ys \<and> subtuple f xs ys"

lemma double_fmrestrict_fset_fmdom:
  "fmrestrict_fset (fmdom (fmrestrict_fset (fmdom xs) ys)) xs =
   fmrestrict_fset (fmdom ys) xs"
  unfolding fmfilter_alt_defs(5) fmdom_filter ffmember_filter
  by (metis (mono_tags, lifting) fmdomI fmfilter_cong)

(* К определению через fmmap_keys можно придти через fmmap_keys_of_list *)
(* Попробовать эту функцию size_fmap *)
definition "fmmerge f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma q11:
  "fmap_of_list (map
    (\<lambda>k. (k, f ( (fmlookup xm k)) ( (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))) =
   fmap_of_list (map
    (\<lambda>k. (k, f
      (if k |\<in>| fmdom xm then  (fmlookup xm k) else None)
      (if k |\<in>| fmdom ym then  (fmlookup ym k) else None)))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"
(*  by (metis fmdom_notD)*)
proof -
  { fix aa :: 'a
have "fmap_of_list (map (\<lambda>a. (a, f (fmlookup xm a) (fmlookup ym a))) (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))) = fmap_of_list (map (\<lambda>a. (a, f (if a |\<in>| fmdom xm then fmlookup xm a else None) (if a |\<in>| fmdom ym then fmlookup ym a else None))) (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))) \<or> (aa, f (fmlookup xm aa) (fmlookup ym aa)) = (aa, f (if aa |\<in>| fmdom xm then fmlookup xm aa else None) (if aa |\<in>| fmdom ym then fmlookup ym aa else None))"
  by (simp add: fmdom_notD) }
  then show ?thesis
    by meson
qed

thm fmdom_notD
(*
lemma q12:
  "fmap_of_list (map
    (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))) =
   fmap_of_list (map
    (\<lambda>k. (k, f
      (if k |\<in>| fmdom xm then the (fmlookup xm k) else A)
      (if k |\<in>| fmdom ym then the (fmlookup ym k) else A)))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"
*)
  term map_of
  thm fmmap_keys_of_list

lemma fmmerge_commut:
  "(\<And>x y. f x y = f y x) \<Longrightarrow>
   fmmerge f xm ym = fmmerge f ym xm"
  unfolding fmmerge_def
  by (simp add: inf_commute)
(*
lemma fmmerge_commut':
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow>f x y = f y x) \<Longrightarrow>
   fmmerge f xm ym = fmmerge f ym xm"
  unfolding fmmerge_def
*)
 
lemma q12:
  "x |\<in>| fmdom (fmrestrict_fset (fmdom ym) xm) \<Longrightarrow>
   fmlookup xm x \<noteq> None \<and> fmlookup ym x \<noteq> None"
  by (metis fmdom_notI fmlookup_restrict_fset)

lemma q13:
  "x |\<in>| fmdom xm \<Longrightarrow>
   fmlookup xm x \<noteq> None"
  by (metis fmdom_notI)

lemma fmdom'_alt_def_rev:
  "fset (fmdom m) = fmdom' m"
  by (simp add: fmdom'_alt_def)

lemma q21:
  "fmlookup xm x = Some y \<Longrightarrow>
   fmlookup ym x = Some ya \<Longrightarrow>
   map_of
    (map (\<lambda>k. (k, g (the (fmlookup xm k)) (the (fmlookup ym k))))
         (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))
    x = Some (g y ya)"
  unfolding map_of_map_restrict
  apply auto
  apply (unfold fmdom.rep_eq)
  by (simp add: domI)

  term map_of
  thm map_of_map_keys map_of_map_restrict


lemma subtuple_fmmerge:
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel f (fmrestrict_fset (fmdom ym) xm) (fmmerge g xm ym)"
  unfolding fmmerge_def fmrel_code fmlookup_of_list
  apply auto
  apply (unfold Option.rel_option_iff)
  apply auto
  apply (drule q12)
  apply auto
  apply (frule_tac ?ya="ya" and ?ym="ym" and ?g="g" in q21, auto)
  apply (simp add: fmranI)
  apply (drule q13)
  apply (drule q13)
  apply auto
  apply (frule_tac ?ya="ya" and ?ym="ym" and ?g="g" in q21, auto)
  apply (simp add: fmranI)
  done

lemma subtuple_fmmerge':
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    subtuple f xm (fmmerge g xm ym)"
  by (smt double_fmrestrict_fset_fmdom fmdom_restrict_fset
          fmrel_fmdom_eq fmrestrict_fset_dom fsubset_antisym subtuple_fmmerge)

(*
lemma subtuple_fmmerge:
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel f (fmrestrict_fset (fmdom ym) xm) (fmmerge g xm ym)"
  unfolding fmmerge_def fmrel_code fmlookup_of_list


lemma subtuple_fmmerge_upper:
  "(\<And>x y z.
    z |\<in>| fmran zm \<Longrightarrow>
    f x z \<Longrightarrow> f y z \<Longrightarrow> f (g x y) z) \<Longrightarrow>
   fmrel f (fmrestrict_fset (fmdom zm) xm) zm \<Longrightarrow>
   fmrel f (fmrestrict_fset (fmdom zm) ym) zm \<Longrightarrow>
   fmrel f (fmrestrict_fset (fmdom zm) (fmmerge g xm ym)) zm"
  unfolding fmmerge_def fmrel_code fmlookup_of_list
  apply auto
  apply (unfold Option.rel_option_iff)
  apply auto
  apply (frule_tac ?ya="ya" and ?ym="ym" and ?g="g" in q21)
*)
lemma q14:
  "x |\<in>|
   fmdom
   (fmrestrict_fset (fmdom zm)
    (fmap_of_list
      (map (\<lambda>k. (k, g (the (fmlookup xm k)) (the (fmlookup ym k))))
        (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))))) \<Longrightarrow>
   fmlookup zm x \<noteq> None"
  by (meson fmlookup_restrict_fset q13)


lemma q15:
  "x |\<in>|
   fmdom
   (fmrestrict_fset (fmdom zm)
    (fmap_of_list
      (map (\<lambda>k. (k, g (the (fmlookup xm k)) (the (fmlookup ym k))))
        (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))))) \<Longrightarrow>
   fmlookup (fmap_of_list
      (map (\<lambda>k. (k, g (the (fmlookup xm k)) (the (fmlookup ym k))))
        (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))) x \<noteq> None"
  by (drule q12; auto)

lemma q16:
  "fmlookup zm x = Some y \<Longrightarrow> x \<in> fset (fmdom zm)"
  by (meson fmdomI notin_fset)

lemma fmap_of_list_abs_eq_rev:
  "Abs_fmap (map_of x) = fmap_of_list x"
  by (simp add: fmap_of_list.abs_eq)

lemma q17:
  "x |\<in>|
   fmdom
   (fmrestrict_fset (fmdom zm)
    (fmap_of_list
      (map (\<lambda>k. (k, g (the (fmlookup xm k)) (the (fmlookup ym k))))
        (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))))) \<Longrightarrow>
   x |\<in>| fmdom zm"
  apply (drule q14)
  by (meson fmdom_notD)

lemma q18:
  "x |\<in>|
   fmdom
   (fmrestrict_fset (fmdom zm)
    (fmap_of_list
      (map (\<lambda>k. (k, g (the (fmlookup xm k)) (the (fmlookup ym k))))
        (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym))))) \<Longrightarrow>
   fmlookup xm x \<noteq> None \<and> fmlookup ym x \<noteq> None"
  apply (drule q15)
  unfolding fmlookup_of_list fmrestrict_fset_def map_restrict_set_def
            map_filter_def
  apply auto
  apply (unfold map_of_map_restrict)
  apply auto
  apply (unfold fmdom'_alt_def_rev)
  apply (unfold restrict_map_def)
  apply (cases "x \<in> fmdom' xm \<inter> fmdom' ym", auto)
  apply (simp add: fmlookup_dom'_iff)
  apply (cases "x \<in> fmdom' xm \<inter> fmdom' ym", auto)
  apply (simp add: fmlookup_dom'_iff)
  done

thm fmrel_code

lemma q31:
  "(case fmlookup xm x of
         None \<Rightarrow>
           (case fmlookup zm x of None \<Rightarrow> True | Some a \<Rightarrow> False)
         | Some xa \<Rightarrow>
             (case fmlookup zm x of None \<Rightarrow> False | Some x \<Rightarrow> f xa x)) \<Longrightarrow>
   fmlookup zm x = Some xb \<Longrightarrow>
   (case fmlookup xm x of
         None \<Rightarrow> False
         | Some xa \<Rightarrow> f xa xb)"
  by (metis option.case_eq_if option.simps(5))
(*
lemma q:
  "(\<And>x y z.
               z |\<in>| fmran zm \<Longrightarrow>
               f x z \<Longrightarrow> f y z \<Longrightarrow> f (g x y) z) \<Longrightarrow>
           fmlookup zm x = Some a \<Longrightarrow>
           case fmlookup xm x of None \<Rightarrow> False
           | Some xa \<Rightarrow> f xa a \<Longrightarrow>
           case fmlookup ym x of None \<Rightarrow> False
           | Some xa \<Rightarrow> f xa a \<Longrightarrow>
           case fmlookup
                 (fmap_of_list
                   (map (\<lambda>k. (k, g (the (fmlookup xm k))
  (the (fmlookup ym k))))
                     (sorted_list_of_fset
                       (fmdom xm |\<inter>| fmdom ym))))
                 x of
           None \<Rightarrow>
             case fmlookup zm x of None \<Rightarrow> True
             | Some a \<Rightarrow> False
           | Some xa \<Rightarrow>
               case fmlookup zm x of None \<Rightarrow> False
               | Some x \<Rightarrow> f xa x"
  apply (cases "fmlookup xm x = None \<and> fmlookup ym x = None", auto)
*)
(*
lemma q32:
  "(case fmlookup xm x of None \<Rightarrow> False | Some xa \<Rightarrow> f xa) \<Longrightarrow>
   (\<And>xa. fmlookup xm x = Some xa \<Longrightarrow> f xa \<Longrightarrow> P) \<Longrightarrow> P"
  using case_optionE by blast
*)
lemma subtuple_fmmerge_upper:
  "(\<And>x y z.
    z |\<in>| fmran zm \<Longrightarrow>
    f x z \<Longrightarrow> f y z \<Longrightarrow> f (g x y) z) \<Longrightarrow>
   subtuple f xm zm \<Longrightarrow>
   subtuple f ym zm \<Longrightarrow>
   subtuple f (fmmerge g xm ym) zm"
  unfolding fmmerge_def fmrel_code fmlookup_of_list
  apply auto
  apply (unfold Option.rel_option_iff)
  apply auto
  apply (drule q18)
  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply auto
  apply (frule_tac ?ya="ya" and ?ym="ym" and ?g="g" in q21)
  apply auto[1]
  apply (metis (no_types, lifting) fmdomE fmlookup_of_list fmranI option.simps(5))

  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply auto
  apply (unfold fmlookup_dom_iff)[1]
  apply auto
  apply (drule_tac ?xb="a" in q31, simp)
  apply (drule_tac ?xb="a" in q31, simp)
  apply (erule case_optionE)
  apply (erule case_optionE)
  apply auto[1]
  apply auto[1]
  apply (erule case_optionE)
  apply auto[1]
  apply (unfold option.case_eq_if)[1]
  apply auto[1]
  apply (simp add: fmlookup_of_list q21)
  apply (unfold fmlookup_of_list)
  apply (frule_tac ?ym="ym" and ?ya="xaa" and ?g="g" in q21)
  apply auto[1]
  using fmranI apply fastforce

  apply (erule_tac ?x="x" in fBallE)
  apply auto
  apply (erule case_optionE)
  apply auto
  apply (erule case_optionE)
  apply auto

  apply (erule_tac ?x="x" in fBallE)
  apply auto
  apply (erule_tac ?x="x" in fBallE)
  apply (erule_tac ?x="x" in fBallE)
  apply auto
  apply (erule case_optionE)
  apply auto

  apply (erule_tac ?x="x" in fBallE)
  apply auto

  apply (erule case_optionE)
  apply auto
  done






(*
  unfolding fmmerge_def fmap.in_rel
  apply auto

  thm fmap.rel_map fmrel_iff
  thm map_of_transfer
  term size_fmap

lemma supc_less_eq_sup':
  "(\<And>x y. x |\<in>| fmran xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel_on_fset (fmdom xm |\<inter>| fmdom ym) f xm (fmmerge g xm ym)"
  unfolding fmmerge_def fmrel_on_fset_fmrel_restrict
  apply (rule fmrel_restrict_fset)
  apply auto
*)
(*
lemma q:
  "fmmap_keys
    (\<lambda>k x. (f x (the (fmlookup ys k))))
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. (f x (the (fmlookup (fmrestrict_fset (fmdom xs) ys) k))))
    (fmrestrict_fset (fmdom (fmrestrict_fset (fmdom xs) ys)) xs)"
  apply auto


lemma q:
  "fmmap_keys
    (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. (f x (the (fmlookup ys k))))
    (fmrestrict_fset (fmdom ys) xs)"

lemma q:
  "fmmap_keys
    (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
    (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. (f x (the (fmlookup ys k))))
    (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"

definition
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
*)
















lemma fmrel_upd_rev:
  "fmrel R (fmupd k x xs) (fmupd k y ys) \<Longrightarrow>
   fmlookup xs k = None \<Longrightarrow>
   fmlookup ys k = None \<Longrightarrow>
   fmrel R xs ys"
  by (smt fmrel_iff fmupd_lookup option.rel_sel)

term fmap_of_list

lemma list_all2_to_fmrel:
  "list_all2 (\<lambda>(a, x) (b, y). a = b \<and> R x y) xs ys \<Longrightarrow>
   fmrel R (fmap_of_list xs) (fmap_of_list ys)"
  by (induct rule: list_all2_induct; auto)

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

lemma sorted_list_of_fmempty:
  "sorted_list_of_fmap fmempty = []"
  unfolding sorted_list_of_fmap_def sorted_list_of_fset_def
  by auto

term rel_fun
thm fmrel_upd
thm Finite_Map.fmap.rel_mono_strong Finite_Map.fmap.rel_cong_simp Finite_Map.fmap.rel_cong
thm fmrel_cases

lemma fmrel_to_trancl:
  "a = fmrel P\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   b = (fmrel P)\<^sup>+\<^sup>+ xs ys \<Longrightarrow> b"
  sorry




lemma q:
  "R x y \<Longrightarrow>
   fmrel R xm ym \<Longrightarrow>
   fmlookup xm k = None \<Longrightarrow>
   fmlookup ym k = None \<Longrightarrow>
   list_all2 (\<lambda>(a, x) (b, y). a = b \<and> R x y)
    (sorted_list_of_fmap xm) (sorted_list_of_fmap ym) \<Longrightarrow>
   list_all2 (\<lambda>(a, x) (b, y). a = b \<and> R x y)
    (sorted_list_of_fmap (fmupd k x xm))
    (sorted_list_of_fmap (fmupd k y ym))"
  apply (erule_tac ?x="k" in fmrel_cases)
  apply auto

thm fmrel_cases

lemma fmrel_to_list_all2:
  "fmrel R xm ym \<Longrightarrow>
   list_all2 (\<lambda>(a, x) (b, y). a = b \<and> R x y)
    (sorted_list_of_fmap xm)
    (sorted_list_of_fmap ym)"
  apply (erule fmrel_cases)
(*
  apply (induct rule: fmrel_induct)
  apply (simp add: sorted_list_of_fmempty)
*)



thm fmrel_induct

(*
abbreviation
  "subtuple f xs ys \<equiv> fmrel f (fmrestrict_fset (fmdom ys) xs) ys"
*)

thm list_all2_induct

lemma fmrel_upd_rev_elim:
  "fmrel R xs ys \<Longrightarrow>
   xs = ys"
  apply (induct rule: fmrel_induct; auto)

lemma fmrel_upd_rev_elim:
  "fmrel R (fmupd k x xs) (fmupd k y ys) \<Longrightarrow>
   fmlookup xs k = None \<Longrightarrow>
   fmlookup ys k = None \<Longrightarrow>
   (fmrel R xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: fmrel_induct)

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
   (
   fmrel R xs' ys \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: fmrel_upd_rev)

lemma q:
  "       (\<And>xs. fmrel P\<^sup>+\<^sup>+ xs m \<Longrightarrow>
              (\<And>x. P x x) \<Longrightarrow> (fmrel P)\<^sup>+\<^sup>+ xs m) \<Longrightarrow>
       fmlookup m x = None \<Longrightarrow>
       fmrel P\<^sup>+\<^sup>+ xs (fmupd x y m) \<Longrightarrow>
       (\<And>x. P x x) \<Longrightarrow> (fmrel P)\<^sup>+\<^sup>+ xs (fmupd x y m)"
  apply (induct xs arbitrary: m rule: fmap_induct)
  apply (metis finsert_not_fempty fmdom_empty fmdom_fmupd fmrel_fmdom_eq)

  thm fmrel_upd_rev_right
lemma fmrel_to_trancl:
  "fmrel P\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (fmrel P)\<^sup>+\<^sup>+ xs ys"
  apply (induct arbitrary: xs rule: fmap_induct)
  apply (metis (mono_tags, lifting) bot_fset.rep_eq empty_iff fmap.rel_mono_strong fmran'_alt_def fmran_empty tranclp.r_into_trancl)
  apply (erule fmrel_upd_rev_right)
  apply simp
  apply simp
(*  by (metis fmap.rel_mono_strong tranclp.r_into_trancl)*)
(*  by (meson fmap.rel_cong tranclp.r_into_trancl)*)


end

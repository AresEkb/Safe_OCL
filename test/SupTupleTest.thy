theory SupTupleTest
  imports Main "~~/src/HOL/Library/Finite_Map"
begin

datatype (plugins del: "size") t = A | B | C "(nat, t) fmap"
(*
definition
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"

definition
  "supc'' f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. f x (the (fmlookup ys k)))
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
*)
definition
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom (fmrestrict_fset (fmdom ys) xs)) then (f x (the (fmlookup ys k))) else A)
      (fmrestrict_fset (fmdom ys) xs)"

definition
  "supc' f xs ys \<equiv>
    fmap_of_list (map
      (\<lambda>k. (k, f (the (fmlookup xs k)) (the (fmlookup ys k))))
      (sorted_list_of_fset (fmdom xs |\<inter>| fmdom ys)))"

definition
  "supc'' f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. f x (the (fmlookup ys k)))
      (fmrestrict_fset (fmdom ys) xs)"

lemma fmrestrict_fset_dom_rev:
  "m = fmrestrict_fset (fmdom m) m"
  by simp

lemma fmmap_keys_if_simp:
  "fmmap_keys (\<lambda>k x. if k |\<in>| fmdom xs then f k x else g k x) xs =
   fmmap_keys (\<lambda>k x. f k x) xs"
  sorry

lemma q:
  "supc f xs ys = supc'' f xs ys"
  unfolding supc_def supc''_def
  apply (subst fmmap_keys_if_simp)
  apply auto
  done

lemma q111:
  "fmdom xs |\<inter>| fmdom ys = fmdom ys |\<inter>| fmdom xs"
  by auto

lemma q:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   (\<lambda>k. (k, f (the (fmlookup xs k)) (the (fmlookup ys k)))) =
   (\<lambda>k. (k, f (the (fmlookup ys k)) (the (fmlookup xs k))))"
  nitpick

lemma q:
  "(\<And>x y. x \<in> fmran' xs \<inter> fmran' ys \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   map (\<lambda>k. (k, f (the (fmlookup xs k)) (the (fmlookup ys k)))) =
   map (\<lambda>k. (k, f (the (fmlookup ys k)) (the (fmlookup xs k))))"

lemma Tuple_sup_commut':
  "(\<And>x y. x \<in> fmran' xs \<inter> fmran' ys \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   supc' f xs ys = supc' f ys xs"
  unfolding supc'_def
(*
lemma q:
  "(fmrestrict_fset (fmdom ys) xs) =
   (fmrestrict_fset (ffilter (\<lambda>k. k |\<in>| fmdom ys) (fmdom xs)) xs)"
  by (metis ffmember_filter fmdomI fmfilter_alt_defs(5) fmfilter_cong)
*)

(*fmrel f (fmrestrict_fset (fmdom ys) xs) ys*)

lemma q:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel f
     (fmrestrict_fset (fmdom ys) xs)
     (supc g xs ys)"
  sorry
  unfolding supc_def
  apply auto[1]

lemma q:
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> f x (g x y)) \<Longrightarrow>
    fmrel f
     (fmrestrict_fset
       (ffilter (\<lambda>k. k |\<in>| fmdom ys) (fmdom xs)) xs)
     (supc g xs ys)"
  unfolding supc_def
  apply auto[1]







lemma fmdom_fmrestrict_fset_commut:
  "fmdom (fmrestrict_fset (fmdom ys) xs) = fmdom (fmrestrict_fset (fmdom xs) ys)"
  by (smt antisym_conv ffmember_filter fmdom_filter fmdom_restrict_fset
          fmfilter_alt_defs(5) fmfilter_cong fmrestrict_fset_dom_rev)


lemma Tuple_sup_commut':
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   supc f xs ys = supc f ys xs"
  unfolding supc_def
  apply (induct xs arbitrary: ys)
  apply simp
  apply (metis (no_types, lifting) fmdom_empty fmrestrict_fset_empty fmrestrict_fset_fmmap_keys_rev fmrestrict_fset_null)
  apply auto





lemma q31:
  "(\<And>x. f x = g x) \<Longrightarrow> f = g"
  by (simp add: ext)

lemma q32:
  "f = g \<Longrightarrow> (\<And>x. f x = g x)"
  by (simp add: ext)

lemma q33:
  "(\<And>x y. f x y = g x y) \<Longrightarrow> f = g"
  by (simp add: ext)

lemma q34:
  "f = g \<Longrightarrow> (\<And>x y. f x y = g x y)"
  by (simp add: ext)

lemma q11:
  "k |\<in>| fmdom xs \<Longrightarrow> \<exists>x. fmlookup xs k = Some x"
  by auto

lemma q12:
  "k |\<in>| fmdom xs \<Longrightarrow> fmlookup xs k \<noteq> None"
  by auto

lemma q13:
  "k |\<in>| fmdom xs \<Longrightarrow>
   (if (k |\<in>| fmdom xs) then (f x (the (fmlookup xs k))) else A) = f x (the (fmlookup xs k))"
  by auto

lemma q21:
  "(\<And>x k. f x = g x) \<Longrightarrow>
   fmmap_keys f (fmfilter P xs) = fmmap_keys g (fmfilter P xs)"
  by meson

lemma fmfilter_fmmap_keys_rev:
  "fmmap_keys f (fmfilter P m) = fmfilter P (fmmap_keys f m)"
  by simp

lemma fmrestrict_fset_fmmap_keys_rev:
  "fmmap_keys f (fmrestrict_fset S m) = fmrestrict_fset S (fmmap_keys f m)"
  by simp

lemma q41:
  "(\<And>x k. k |\<in>| ys \<Longrightarrow> f = g) \<Longrightarrow>
   fmmap_keys f (fmrestrict_fset ys xs) = fmmap_keys g (fmrestrict_fset ys xs)"
  by (metis equalsffemptyI fmrestrict_fset_fmmap_keys fmrestrict_fset_null)


lemma q111:
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. f x (the (fmlookup (fmrestrict_fset (fmdom ys) ys) k)))
    (fmrestrict_fset (fmdom (fmrestrict_fset (fmdom ys) ys)) xs)"
  by simp

lemma q112:
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. f x (the (if k |\<in>| fmdom ys then fmlookup ys k else None)))
    (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
  by (metis (full_types, hide_lams) fmdom_notD)

lemma q112':
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. f x (the (if k |\<in>| fmdom ys then fmlookup ys k else g)))
    (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
  apply (subst fmdom_notD)

thm fmlookup_restrict_fset
thm fmfilter_alt_defs fmdom_notD

lemma q113:
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. f x (the (if k |\<in>| fmdom ys then fmlookup ys k else None)))
    (fmrestrict_fset (fmdom ys) xs)"
  by (metis (full_types, hide_lams) fmdom_notD)

lemma q114:
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. f x (if k |\<in>| fmdom ys then the (fmlookup ys k) else the None))
    (fmrestrict_fset (fmdom ys) xs)"
  by (metis (full_types, hide_lams) fmdom_notD)

lemma q115:
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. (if k |\<in>| fmdom ys then f x (the (fmlookup ys k)) else f x (the None)))
    (fmrestrict_fset (fmdom ys) xs)"
  by (metis (full_types, hide_lams) fmdom_notD)

lemma q115:
  "fmmap_keys
    (\<lambda>k x. f x (the (fmlookup ys k)))
    (fmrestrict_fset (fmdom ys) xs) =
   fmmap_keys
    (\<lambda>k x. (if k |\<in>| fmdom ys then f x (the (fmlookup ys k)) else g))
    (fmrestrict_fset (fmdom ys) xs)"
  by (metis (full_types, hide_lams) fmdom_notD)

thm fmdom_notD

lemma supc_eq:
  "supc f xs ys = supc'' f xs ys"
  unfolding supc_def supc''_def


thm fmfilter_false

lemma q:
  "k |\<in>| ys \<Longrightarrow>
   (\<lambda>k x. if k |\<in>| ys then f else g) k = (\<lambda>k x. f) k"
  apply (simp add: ext)

(********* Goal *********)

lemma fmmap_keys_fmupd:
  "fmmap_keys f (fmupd x y xs) =
   fmupd x (f x y) (fmmap_keys f xs)"
  sorry

lemma fmupd_if_simp:
  "fmupd x (if x |\<in>| fmdom (fmupd x y xs) then f x y else g) = fmupd x (f x y)"
  by auto

lemma q:
  "fmlookup xs x = None \<Longrightarrow>
   (\<lambda>k x. if k |\<in>| fmdom xs then f k x else g) =
   (\<lambda>k xa. if k |\<in>| fmdom (fmupd x y xs) then f k xa else g)"

lemma q:
  "(\<lambda>k x. if k |\<in>| fmdom xs then f k x else g) =
   (\<lambda>k xa. if k = x \<or> k |\<in>| fmdom xs then f k xa else g)"
  nitpick

lemma q:
  "    fmmap_keys (\<lambda>k x. if k |\<in>| fmdom xs then f k x else g) xs =
       fmmap_keys (\<lambda>k x. f k x) xs \<Longrightarrow>
       fmlookup xs x = None \<Longrightarrow>
       fmmap_keys
        (\<lambda>k xa. if k |\<in>| fmdom (fmupd x y xs) then f k xa else g)
        (fmupd x y xs) =
       fmmap_keys (\<lambda>k x. f k x) (fmupd x y xs)"
  unfolding fmmap_keys_fmupd 
  apply auto

lemma fmmap_keys_if_simp:
  "fmmap_keys
    (\<lambda>k x. if k |\<in>| fmdom xs then f else g)
    xs =
   fmmap_keys
    (\<lambda>k x. f)
    xs"
  apply (induct xs)
  apply (metis (no_types, lifting) fmrestrict_fset_fmmap_keys fmrestrict_fset_null)

lemma fmmap_keys_if_simp:
  "fmmap_keys
    (\<lambda>k x. if k |\<in>| ys then f else g)
    (fmfilter (\<lambda>k. k |\<in>| ys) xs) =
   fmmap_keys
    (\<lambda>k x. f)
    (fmfilter (\<lambda>k. k |\<in>| ys) xs)"
  apply (induct xs)
  apply (metis (no_types, lifting) fmfilter_empty fmrestrict_set_fmmap_keys fmrestrict_set_null)


lemma fmmap_keys_if_simp:
  "fmmap_keys
    (\<lambda>k x. if k |\<in>| ys then f else g)
    (fmrestrict_fset ys xs) =
   fmmap_keys
    (\<lambda>k x. f)
    (fmrestrict_fset ys xs)"
  apply (induct xs)
  apply (metis fmrestrict_fset_fmmap_keys fmrestrict_fset_null)
  apply auto
  apply (unfold fmrestrict_fset_fmmap_keys_rev)

lemma q42:
  "fmmap_keys
    (\<lambda>k x. if k \<in> fmdom' ys then f else g)
    (fmfilter (\<lambda>k. k \<in> fmdom' ys) xs) =
   fmmap_keys
    (\<lambda>k x. f)
    (fmfilter (\<lambda>k. k \<in> fmdom' ys) xs)"
  apply (induct xs arbitrary: ys)
  apply (metis (no_types, lifting) empty_iff fmdom'_empty fmfilter_false fmfilter_fmmap_keys_rev)
  apply (unfold fmfilter_fmmap_keys_rev)


thm fmrestrict_fset_fmmap_keys fmfilter_cong fmfilter_cong' fmfilter_upd fmlookup_filter
thm fmsubset_filter_mono





(*
  by (metis equalsffemptyI fmrestrict_fset_null fmrestrict_set_fmmap_keys fmrestrict_set_null)
  by (simp add: fmap_ext)
  by (metis ex_fin_conv fmrestrict_fset_fmmap_keys fmrestrict_fset_null)
*)
thm equalsffemptyI fmrestrict_fset_null fmrestrict_set_fmmap_keys fmrestrict_set_null
thm ex_fin_conv fmrestrict_fset_fmmap_keys fmrestrict_fset_null


lemma q42:
  "(\<And>x k. k |\<in>| ys \<Longrightarrow> f k x = g k x) \<Longrightarrow>
   fmmap_keys f (fmrestrict_fset ys xs) = fmmap_keys g (fmrestrict_fset ys xs)"
  unfolding fmrestrict_fset_fmmap_keys_rev
  apply (induct xs arbitrary: ys)
  apply (metis fmrestrict_fset_null)
  apply (simp add: fmap_ext)
  apply auto
  done

lemma q42:
  "(\<And>x k. k |\<in>| ys \<Longrightarrow> f x = g x) \<Longrightarrow>
   fmmap_keys f (fmrestrict_fset ys xs) = fmmap_keys g (fmrestrict_fset ys xs)"
  unfolding fmrestrict_fset_fmmap_keys_rev
  apply (induct ys)
  apply (metis fmrestrict_fset_null)
  apply (simp add: fmap_ext)
  done
(*
  by (metis equalsffemptyI fmrestrict_fset_null fmrestrict_set_fmmap_keys fmrestrict_set_null)
  by (simp add: fmap_ext)
  by (metis ex_fin_conv fmrestrict_fset_fmmap_keys fmrestrict_fset_null)
*)
thm equalsffemptyI fmrestrict_fset_null fmrestrict_set_fmmap_keys fmrestrict_set_null
thm ex_fin_conv fmrestrict_fset_fmmap_keys fmrestrict_fset_null

lemma q43:
  "(\<And>x k. k |\<in>| ys \<Longrightarrow> f k x = g k x) \<Longrightarrow>
   fmmap_keys f (fmrestrict_fset ys xs) = fmmap_keys g (fmrestrict_fset ys xs)"
  unfolding fmrestrict_fset_fmmap_keys_rev
  apply (induct ys)
  apply (metis fmrestrict_fset_null)
  apply (simp add: fmap_ext)
  done

lemma q22:
  "(\<And>x k. P k \<Longrightarrow> f = g) \<Longrightarrow>
   fmmap_keys f (fmfilter P xs) = fmmap_keys g (fmfilter P xs)"
  unfolding fmfilter_fmmap_keys_rev
  apply (frule fmfilter_false)
  by (metis fmfilter_false)

lemma q23:
  "(\<And>x k. P k \<Longrightarrow> f x = g x) \<Longrightarrow>
   fmmap_keys f (fmfilter P xs) = fmmap_keys g (fmfilter P xs)"
  by (metis fmfilter_false fmfilter_fmmap_keys)

lemma q35:
  "(\<And>x k. P k \<Longrightarrow> f x = g x) \<Longrightarrow>
   (\<And>x k. P k \<Longrightarrow> f = g)"
  by (simp add: ext)

lemma q36:
  "(\<And>x k. P k \<Longrightarrow> f k x = g k x) \<Longrightarrow>
   (\<And>x k. P k \<Longrightarrow> f = g)"
  nitpick

lemma q24:
  "(\<And>x k. P k \<Longrightarrow> f k x = g k x) \<Longrightarrow>
   fmmap_keys f (fmfilter P xs) = fmmap_keys g (fmfilter P xs)"

definition
  "supc' f xs ys \<equiv>
    fmap_of_list (map
      (\<lambda>k. (k, f (the (fmlookup xs k)) (the (fmlookup ys k))))
      (sorted_list_of_fset (fmdom xs |\<inter>| fmdom ys)))"

lemma Tuple_sup_commut':
  "(\<And>x y. x \<in> fmran' xs \<Longrightarrow> f x y = f y x) \<Longrightarrow>
   supc f xs ys = supc f ys xs"
  unfolding supc_def
  apply (induct xs arbitrary: ys)
  apply (metis (no_types, lifting) fmdom_empty fmrestrict_fset_empty fmrestrict_fset_fmmap_keys_rev fmrestrict_fset_null)
  apply auto


lemma supc_eq:
  "supc f xs ys = supc' f xs ys"
  unfolding supc_def supc'_def



end

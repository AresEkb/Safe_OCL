theory TupleTest
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = A | B | C "t list"

definition "only_one p xs ys \<equiv>
  \<exists>h t x y. xs = h@[x]@t \<and> ys = h@[y]@t \<and> x \<noteq> y \<and> p x y"

lemma only_one_mono [mono]: "(\<And> x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> p x y \<longrightarrow> q x y) \<Longrightarrow>
  only_one p xs ys \<longrightarrow> only_one q xs ys"
  by (smt UnCI list.set_intros(1) only_one_def set_append)

lemma q21:
  "x # xs = yh @ xa # yt \<Longrightarrow>
   y # xs = yh @ ya # yt \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   yh = []"
  by (metis hd_append list.sel(1))

lemma q22:
  "x # xs = yh @ xa # yt \<Longrightarrow>
   y # xs = yh @ ya # yt \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   xs = yt"
  by (metis append_eq_Cons_conv list.inject)

lemma q23:
  "x # xs = yh @ xa # yt \<Longrightarrow>
   y # xs = yh @ ya # yt \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   x = xa \<and> y = ya"
  by (metis hd_append list.sel(1))

lemma q24:
  "h @ x # t = ha @ xa # ta \<Longrightarrow>
   h @ y # t = ha @ ya # ta \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   x = xa \<and> y = ya"
  by (smt append.assoc append.right_neutral append_Nil2 append_assoc append_eq_append_conv2 list.inject q23 same_append_eq self_append_conv2)


definition "sublist f xs ys \<equiv>
  xs \<noteq> ys \<and> list_all2 (\<lambda>x y. x = y \<or> f x y) (take (length ys) xs) ys"

lemma f_eq_mono [mono]:
  "(\<And>x y. f x y \<longrightarrow> g x y) \<Longrightarrow> 
   (\<lambda>x y. x = y \<or> f x y) x y \<longrightarrow> (\<lambda>x y. x = y \<or> g x y) x y"
  by simp

lemma sublist_mono [mono]:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow> 
   sublist f xs ys \<longrightarrow> sublist g xs ys"
  by (metis (no_types, lifting) in_set_takeD list.rel_mono_strong sublist_def)
(*  by (metis in_set_takeD list.rel_mono_strong sublist_def)*)
(*
inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "xs = ys @ [t] \<Longrightarrow>
   C xs \<sqsubset> C ys"
| "only_one subtype xs ys \<Longrightarrow>
   C xs \<sqsubset> C ys"
*)
inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "sublist subtype xs ys \<Longrightarrow>
   C xs \<sqsubset> C ys"

(*
lemma sublist_mono2 [mono]:
  "mono sublist"
  unfolding mono_def
  by (metis (full_types) list.rel_mono predicate2D predicate2I sublist_def)
*)

inductive_cases subtype_A_x[elim]: "A \<sqsubset> x"
inductive_cases subtype_x_A[elim]: "x \<sqsubset> A"
inductive_cases subtype_B_x[elim]: "B \<sqsubset> x"
inductive_cases subtype_x_B[elim]: "x \<sqsubset> B"
inductive_cases subtype_C_x[elim]: "C xs \<sqsubset> x"
inductive_cases subtype_x_C[elim]: "x \<sqsubset> C xs"

lemma subtype_acyclic:
  "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  apply auto[1]
  apply (erule subtype_C_x; auto)
  by (smt le_cases list_all2_antisym list_all2_lengthD sublist_def take_all)
(*  unfolding only_one_def apply auto
  apply (erule subtype_C_x; auto)
  unfolding only_one_def apply auto
  by (metis q24)*)
(*  by (smt Cons_eq_appendI only_one_def q24)*)
(*  by (metis (no_types, lifting) le_cases list_all2_antisym list_all2_lengthD sublist_def take_all)*)

lemma list_all2_subtype_acyclic:
  "list_all2 subtype x y \<Longrightarrow>
   list_all2 subtype y x \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   False"
  apply (induct rule: list_all2_induct; simp)
  apply auto
  using subtype_acyclic by auto


lemma trancl_subtype_A_x [elim]:
  "subtype\<^sup>+\<^sup>+ A x \<Longrightarrow>
   (x = B \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis converse_tranclpE subtype_A_x subtype_B_x)

lemma trancl_subtype_B_x [elim]:
  "subtype\<^sup>+\<^sup>+ B x \<Longrightarrow> P"
  by (metis subtype_B_x tranclpD)

lemma trancl_subtype_x_A [elim]:
  "subtype\<^sup>+\<^sup>+ x A \<Longrightarrow> P"
  by (metis subtype_x_A tranclp.cases)

lemma trancl_subtype_x_B [elim]:
  "subtype\<^sup>+\<^sup>+ x B \<Longrightarrow>
   (x = A \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis subtype_x_B trancl_subtype_x_A tranclp.cases)

lemma C_functor:
  "functor_under_rel (sublist subtype) subtype C"
  unfolding functor_under_rel_def rel_limited_under_def
  by (auto simp add: inj_def)

lemma q11:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (sublist subtype)\<^sup>+\<^sup>+ xs ys"
  by (meson C_functor tranclp_fun_preserve_gen_1a)

lemma q12:
  "(\<lambda>xs ys. C xs \<sqsubset> C ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtype\<^sup>+\<^sup>+ (C xs) (C ys)"
  by (simp add: fun_preserve_morphism_composition')

lemma q13:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (\<lambda>xs ys. C xs \<sqsubset> C ys)\<^sup>+\<^sup>+ xs ys"
  by (smt q11 subtype.intros(2) tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)

lemma sublist_only_one_id_functor:
  "functor_under_rel (sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y)) (only_one subtype) id"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  unfolding only_one_def sublist_def
  by (auto simp add: list.rel_refl list_all2_appendI)

lemma q31:
  "only_one subtype xs ys \<Longrightarrow>
   sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys"
  unfolding only_one_def sublist_def
  apply auto
  by (simp add: list.rel_refl list_all2_appendI)

lemma q32:
  "only_one subtype xs ys \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* xs ys"
  by (metis (mono_tags, lifting) Nitpick.rtranclp_unfold q31 r_into_rtranclp sublist_mono)

lemma q33:
  "(only_one subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys"
  apply (erule tranclp_trans_induct)
  apply (auto simp add: q31 tranclp.r_into_trancl)
  done

lemma q34:
  "(only_one subtype)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>*\<^sup>* xs ys"
  by (metis (mono_tags, lifting) mono_rtranclp q31)

lemma q35:
  "sublist subtype xs ys \<Longrightarrow> xs \<noteq> ys"
  using subtype.intros(2) subtype_acyclic by auto

lemma q36:
  "only_one subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow> xs \<noteq> ys"
  unfolding only_one_def
  apply auto
  done

lemma q37:
  "only_one subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> xs \<noteq> ys"
  unfolding only_one_def
  apply auto
  done

lemma q61:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) xs ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) ys zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) xs zs"
  by (smt list_all2_trans)

lemma q62:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 P (take (length ys) xs) ys \<Longrightarrow>
   list_all2 P (take (length zs) ys) zs \<Longrightarrow>
   list_all2 P (take (length zs) xs) zs"
  sorry
(*  by (smt length_take list_all2_lengthD list_all2_takeI list_all2_trans take_take)*)

lemma q63:
  "(\<And>x y z. P1 x y \<Longrightarrow> P2 y z \<Longrightarrow> P3 x z) \<Longrightarrow>
   list_all2 P1 (take (length ys) xs) ys \<Longrightarrow>
   list_all2 P2 (take (length zs) ys) zs \<Longrightarrow>
   list_all2 P3 (take (length zs) xs) zs"
  sorry
(*  by (smt append_eq_append_conv_if append_take_drop_id length_take list_all2_append2 list_all2_lengthD list_all2_trans take_take)*)

lemma q64:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length zs) ys) zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length zs) xs) zs"
  by (smt q62)

lemma q65:
  "(\<And>x y. P x y \<Longrightarrow> P y x \<Longrightarrow> x = y) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> P x y) (take (length xs) ys) xs \<Longrightarrow>
   xs = ys"
  by (smt le_cases list_all2_antisym list_all2_lengthD take_all)

lemma sublist_trans:
  "(\<And>x y z. P x y \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   (\<And>x y. P x y \<Longrightarrow> P y x \<Longrightarrow> x = y) \<Longrightarrow>
   sublist P xs ys \<Longrightarrow> sublist P ys zs \<Longrightarrow> sublist P xs zs"
  unfolding sublist_def
  apply auto
  apply (smt le_cases list_all2_antisym list_all2_lengthD take_all)
  by (smt q62)

lemma q81:
  "list_all2 P xs ys \<Longrightarrow> xs \<noteq> ys \<Longrightarrow> sublist P xs ys"
  by (simp add: list_all2_lengthD list_all2_mono sublist_def)

lemma q82:
  "xs = ys @ zs \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> sublist P xs ys"
  by (simp add: list_all2_all_nthI sublist_def)

lemma q83:
  "sublist R xs ys \<Longrightarrow>
   R x y \<Longrightarrow>
   sublist R (x # xs) (y # ys)"
  by (simp add: sublist_def)
(*
lemma q83:
  "sublist R xs ys \<Longrightarrow>
   (\<And>zs. xs = ys @ zs \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> P) \<Longrightarrow>
   (sublist R (x # xs) (y # ys) \<Longrightarrow> xs \<noteq> ys \<Longrightarrow> P) \<Longrightarrow> P"

lemma q83:
  "sublist R xs ys \<Longrightarrow>
   (\<And>zs. xs = ys @ zs \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> P) \<Longrightarrow>
   (list_all2 R xs ys \<Longrightarrow> xs \<noteq> ys \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding sublist_def
  apply auto

  thm sublist_def

definition "sublist2 f xs ys \<equiv>
  list_all2 (\<lambda>x y. x = y \<or> f x y) xs ys"

lemma sublist2_induct
  [consumes 1, case_names Nil Cons, induct set: list_all2]:
  assumes P: "sublist2 P xs ys"
  assumes Nil: "R [] []"
  assumes Cons: "\<And>x xs y ys.
    \<lbrakk>P x y \<or> x = y; sublist2 P xs ys; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys)"
  shows "R xs ys"
using P
  apply (induct xs arbitrary: ys)
  apply (simp add: local.Nil sublist2_def)
  by (smt list_all2_induct local.Cons local.Nil sublist2_def)

definition "sublist3 f xs ys \<equiv>
  list_all2 f (take (length ys) xs) ys"

lemma sublist3_induct
  [consumes 1, case_names Nil Cons, induct set: list_all2]:
  assumes P: "sublist3 P xs ys"
  assumes Nil: "\<And>xs. R xs []"
  assumes Cons: "\<And>x xs y ys.
    \<lbrakk>P x y; sublist3 P xs ys; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys)"
  shows "R xs ys"
using P
  apply (induct xs arbitrary: ys)
  apply (simp add: local.Nil sublist3_def)
  apply (auto simp add: sublist3_def)
  apply (erule list_all2_induct)
  apply (simp add: local.Nil)

lemma q:
  "sublist P xs ys \<Longrightarrow>
   (\<And>xs. xs \<noteq> [] \<Longrightarrow> R xs []) \<Longrightarrow>
   (\<And>x xs y ys. P x y \<Longrightarrow> P x x \<Longrightarrow> P y y \<Longrightarrow> sublist P xs ys \<Longrightarrow> R xs ys \<Longrightarrow> R (x # xs) (y # ys)) \<Longrightarrow>
   R xs ys"
  nitpick

lemma q:
  "sublist P xs ys \<Longrightarrow> (\<forall>zs. xs = ys @ zs) \<or> list_all2 P xs ys"

  thm list_all2_induct



lemma sublist_induct
  [consumes 1, case_names Nil Cons, induct set: sublist]:
  assumes P: "sublist P xs ys"
  assumes xs_ys: "xs \<noteq> ys"
  assumes Nil: "\<And>zs. R (ys @ zs) []"
  assumes Cons: "\<And>x xs y ys.
    \<lbrakk>P x y; sublist P xs ys; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys)"
  shows "R xs ys"
  nitpick
  apply (induct ys arbitrary: xs)


lemma sublist_induct
  [consumes 1, case_names Nil Cons, induct set: sublist]:
  assumes P: "sublist P xs ys"
  assumes Nil: "R [] []"
  assumes Cons: "\<And>x xs y ys.
    \<lbrakk>P x y; sublist P xs ys; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys)"
  shows "R xs ys"
using P
  apply (induct xs arbitrary: ys)
  apply (metis (no_types, lifting) list_all2_Nil sublist_def take_eq_Nil)

  unfolding sublist_def
  apply auto
  sorry
*)

definition "sublist2 f xs ys \<equiv>
  list_all2 (\<lambda>x y. x = y \<or> f x y) xs ys"

lemma sublist2_subtype_trancl1:
  "(list_all2 (\<lambda>x y. x = y \<or> f x y))\<^sup>+\<^sup>+ (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> f x y)\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  apply (induct rule: converse_tranclp_induct)
  apply (smt list.rel_mono_strong sublist2_def tranclp.r_into_trancl)
  apply (auto simp add: sublist2_def)

lemma sublist2_subtype_trancl1:
  "(sublist2 P)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist2 P\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: converse_tranclp_induct)
  apply (smt list.rel_mono_strong sublist2_def tranclp.r_into_trancl)
  apply (auto simp add: sublist2_def)

lemma sublist_subtype_trancl1:
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist subtype\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: converse_tranclp_induct)
  apply (metis sublist_mono tranclp.r_into_trancl)
(*  by (metis (mono_tags) sublist_def sublist_induct)*)

lemma sublist_subtype_implies_not_eq:
  "sublist subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   xs \<noteq> ys"
  by (simp add: sublist_def)

lemma sublist_subtype_trancl2:
  "sublist subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (sublist subtype)\<^sup>+\<^sup>+ xs ys"
  apply (frule sublist_subtype_implies_not_eq)
(*  apply (induct rule: sublist_induct)
  apply simp
  by (metis (mono_tags) sublist_def sublist_induct)*)

(*
lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> (sublist subtype)\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  using sublist_def apply blast
  by (metis subtype_C_x tranclp.trancl_into_trancl)
*)
lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono subtype.simps t.inject t.simps(5) tranclp.r_into_trancl)
  using q11 sublist_subtype_trancl1 tranclp.trancl_into_trancl by fastforce

lemma trancl_subtype_x_C [elim]:
  "subtype\<^sup>+\<^sup>+ x (C ys) \<Longrightarrow>
   (\<And>zs. x = C zs \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ zs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct x; auto)
  done

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x x \<Longrightarrow> False"
  apply (erule tranclp.cases; auto)
  using subtype_acyclic apply auto[1]
  apply (erule subtype.cases; auto)
  apply (erule trancl_subtype_C_x; auto)
  by (meson sublist_def sublist_subtype_trancl1 sublist_subtype_trancl2 tranclp.trancl_into_trancl)
(*  by (smt sublist_def subtype.cases t.inject trancl_subtype_C_x trancl_subtype_x_A tranclp_into_tranclp2)
*)












lemma only_one_subtype_not_tr:
  "only_one subtype xs ys \<Longrightarrow>
   only_one subtype ys zs \<Longrightarrow>
   only_one subtype xs zs \<Longrightarrow>
   False"
  sorry

lemma trancl_only_one_subtype_acyclic:
  "(only_one subtype)\<^sup>+\<^sup>+ xs xs \<Longrightarrow> False"





lemma trancl_subtype_x_C:
  "list_all2 subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow> subtype\<^sup>+\<^sup>+ (C xs) (C ys)"

lemma trancl_subtype_x_C:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow> list_all2 subtype\<^sup>+\<^sup>+ xs ys"



(*
inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "zs \<noteq> [] \<Longrightarrow>
   xs = ys @ zs \<Longrightarrow>
   C xs \<sqsubset> C ys"
| "list_all2 subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   C xs \<sqsubset> C ys"
*)
(*
inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "list_all2 subtype\<^sup>*\<^sup>* (take (length ys) xs) ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   C xs \<sqsubset> C ys"
*)
(*
| "list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   C xs \<sqsubset> C ys"
*)



end

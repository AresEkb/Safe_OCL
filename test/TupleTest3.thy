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
  xs \<noteq> ys \<and> list_all2 f (take (length ys) xs) ys"

lemma sublist_mono [mono]:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow> 
   sublist f xs ys \<longrightarrow> sublist g xs ys"
  by (metis in_set_takeD list.rel_mono_strong sublist_def)

inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "xs = ys @ [t] \<Longrightarrow>
   C xs \<sqsubset> C ys"
| "only_one subtype xs ys \<Longrightarrow>
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
  unfolding only_one_def apply auto
  apply (erule subtype_C_x; auto)
  unfolding only_one_def apply auto
  by (metis q24)
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
(*
lemma C_functor:
  "functor_under_rel (only_one subtype) subtype C"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  using inj_def apply blast
(*  using inj_def by blast*)
*)
lemma q11:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (only_one subtype)\<^sup>+\<^sup>+ xs ys"
  by (meson C_functor tranclp_fun_preserve_gen_1a)
(*
lemma q:
  "list_all2 subtype xs ys \<Longrightarrow>
   list_all2 subtype ys zs \<Longrightarrow>
   list_all2 subtype xs zs \<Longrightarrow> False"
  apply (induct rule: list_all2_induct)

lemma q:
  "list_all2 subtype (take (length ys) xs) ys \<Longrightarrow>
   list_all2 subtype (take (length zs) ys) zs \<Longrightarrow>
   list_all2 subtype (take (length zs) xs) zs \<Longrightarrow> False"
  apply (induct rule: list_all2_induct)
  apply simp

lemma sublist_subtype_not_tr:
  "sublist subtype xs ys \<Longrightarrow>
   sublist subtype ys zs \<Longrightarrow>
   sublist subtype xs zs \<Longrightarrow>
   False"
  unfolding sublist_def
  apply auto
  sorry
*)
(*
lemma q:
  "    ha @ xa # ta = h @ y # t \<Longrightarrow>
       h @ x # t = hb @ xb # tb \<Longrightarrow>
       ha @ ya # ta = hb @ yb # tb \<Longrightarrow>
       x \<noteq> y \<Longrightarrow>
       x \<sqsubset> y \<Longrightarrow>
       xa \<noteq> ya \<Longrightarrow>
       xa \<sqsubset> ya \<Longrightarrow>
       xb \<noteq> yb \<Longrightarrow>
       xb \<sqsubset> yb \<Longrightarrow> False"

lemma q:
  "    ha @ xa # ta = h @ y # t \<Longrightarrow>
       h @ x # t = hb @ xb # tb \<Longrightarrow>
       ha @ ya # ta = hb @ yb # tb \<Longrightarrow>
       x \<noteq> y \<Longrightarrow>
       x \<sqsubset> y \<Longrightarrow>
       xa \<noteq> ya \<Longrightarrow>
       xa \<sqsubset> ya \<Longrightarrow>
       xb \<noteq> yb \<Longrightarrow>
       xb \<sqsubset> yb \<Longrightarrow> False"

lemma only_one_subtype_not_tr:
  "only_one subtype xs ys \<Longrightarrow>
   only_one subtype ys zs \<Longrightarrow>
   only_one subtype xs zs \<Longrightarrow>
   False"
  unfolding only_one_def
  apply (auto)
  sorry
*)
(*
lemma q13:
  "(\<lambda>xs ys. list_all2 subtype\<^sup>*\<^sup>* (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 subtype\<^sup>*\<^sup>* (take (length ys) xs) ys"
  sorry

lemma q12:
  "(sublist subtype\<^sup>*\<^sup>* )\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* xs ys"
  unfolding sublist_def
  sorry




lemma q:
  "list_all2 subtype (take (length y) x) y \<Longrightarrow>
   list_all2 subtype (take (length x) y) x \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   False"
  by (metis length_take list_all2_lengthD list_all2_subtype_acyclic min.absorb_iff2 take_all)

term "mono R"
lemma q:
  "(\<And>x y. R x y \<Longrightarrow> R y x \<Longrightarrow> x = y) \<Longrightarrow>
   strict_mono R\<^sup>*\<^sup>* \<Longrightarrow>
   R\<^sup>*\<^sup>* x y \<Longrightarrow> R\<^sup>*\<^sup>* y x \<Longrightarrow> x = y"
  nitpick


lemma q:
  "list_all2 subtype\<^sup>*\<^sup>* x y \<Longrightarrow>
   list_all2 subtype\<^sup>*\<^sup>* y x \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   False"

lemma q:
  "(list_all2 subtype)\<^sup>*\<^sup>* x y \<Longrightarrow>
   (list_all2 subtype)\<^sup>*\<^sup>* y x \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   False"

lemma q:
  "(list_all2 subtype)\<^sup>*\<^sup>* (take (length y) x) y \<Longrightarrow>
   (list_all2 subtype)\<^sup>*\<^sup>* (take (length x) y) x \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   False"

lemma sublist_tr:
  "sublist subtype\<^sup>*\<^sup>* x y \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* y z \<Longrightarrow>
   sublist subtype\<^sup>*\<^sup>* x z"
  unfolding sublist_def
  apply auto

lemma q:
  assumes prem: "(sublist subtype\<^sup>*\<^sup>* )\<^sup>+\<^sup>+ xs ys"
  shows "sublist subtype\<^sup>*\<^sup>* xs ys"
proof -
  obtain r where r: "r = sublist subtype\<^sup>*\<^sup>*" by auto
  obtain P where P: "P = sublist subtype\<^sup>*\<^sup>*" by auto
  from prem r have major: "r\<^sup>+\<^sup>+ xs ys" by simp
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y" by simp
  have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding r P
    sorry
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P xs ys" by smt
  with P show ?thesis by simp
qed
*)

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
(*  by (smt q31 tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)*)

lemma q34:
  "(only_one subtype)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   (sublist (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>*\<^sup>* xs ys"
  by (metis (mono_tags, lifting) mono_rtranclp q31)

lemma q35:
  "only_one subtype xs ys \<Longrightarrow> xs \<noteq> ys"
  using subtype.intros(3) subtype_acyclic by auto

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
(*
lemma q:
  assumes prem: "(only_one subtype)\<^sup>+\<^sup>+ xs ys"
  shows "xs \<noteq> ys"
proof -
  obtain r where r: "r = only_one subtype" by auto
  obtain P where P: "P = (\<lambda>(xs::t list) ys. xs \<noteq> ys)" by auto
  from prem r have major: "r\<^sup>+\<^sup>+ xs ys" by simp
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y"
    using q35 by auto
  have cases_2: "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    unfolding r P
    sorry
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P xs ys" by smt
  with P show ?thesis by simp
qed
*)


lemma q38:
  "(only_one (<))\<^sup>+\<^sup>+ (xs::nat list) (xs::nat list) \<Longrightarrow> False"
  unfolding only_one_def
  apply auto


lemma q38:
  "(only_one subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow> xs \<noteq> ys"
  sorry


lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> (only_one subtype)\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply auto[1]
  by (metis subtype_C_x tranclp.trancl_into_trancl)
(*  by (metis rtranclp.rtrancl_into_rtrancl subtype_C_x)*)
(*  apply (metis r_into_rtranclp sublist_mono subtype_C_x)
  by (metis length_0_conv list_all2_Nil2 list_all2_lengthD sublist_def sublist_subtype_not_tr subtype.simps t.distinct(3) take_Nil take_eq_Nil)*)

(*  using sublist_def apply blast
  using q11 q12 tranclp.trancl_into_trancl by fastforce*)

lemma trancl_subtype_x_C [elim]:
  "subtype\<^sup>+\<^sup>+ x (C ys) \<Longrightarrow>
   (\<And>zs. x = C zs \<Longrightarrow> (only_one subtype)\<^sup>+\<^sup>+ zs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct x; auto)
  done

lemma only_one_subtype_not_tr:
  "only_one subtype xs ys \<Longrightarrow>
   only_one subtype ys zs \<Longrightarrow>
   only_one subtype xs zs \<Longrightarrow>
   False"
  sorry

lemma trancl_only_one_subtype_acyclic:
  "(only_one subtype)\<^sup>+\<^sup>+ xs xs \<Longrightarrow> False"


lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x x \<Longrightarrow> False"
  apply (erule tranclp.cases; auto)
  using subtype_acyclic apply auto[1]
 by (metis q11 q38 subtype.cases trancl_subtype_x_A tranclp.trancl_into_trancl)
(*  apply (cases x; auto)
  apply (erule trancl_subtype_C_x)
  using sublist_def by auto*)





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

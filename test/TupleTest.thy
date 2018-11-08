theory TupleTest
  imports Main "../Transitive_Closure_Ext"
begin

datatype t = A | B | C "t list"

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
  using C_functor tranclp_fun_preserve_gen_1a by fastforce

lemma q12:
  "(\<lambda>xs ys. C xs \<sqsubset> C ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtype\<^sup>+\<^sup>+ (C xs) (C ys)"
  by (simp add: fun_preserve_morphism_composition')

lemma q13:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (\<lambda>xs ys. C xs \<sqsubset> C ys)\<^sup>+\<^sup>+ xs ys"
  by (smt q11 subtype.intros(2) tranclp.r_into_trancl tranclp_trans tranclp_trans_induct)

lemma q35:
  "sublist subtype xs ys \<Longrightarrow> xs \<noteq> ys"
  by (simp add: sublist_def)

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

definition "sublist2 f xs ys \<equiv>
  list_all2 (\<lambda>x y. x = y \<or> f x y) xs ys"

lemma sublist1_trancl1:
  "(\<lambda>xs ys. xs \<noteq> ys \<and> list_all2 f xs ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 f\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (simp add: list_all2_trancl1 tranclp.r_into_trancl)
  by (smt list_all2_trans tranclp.trancl_into_trancl)

lemma sublist2_trancl1:
  "(\<lambda>xs ys. list_all2 f (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 f\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  apply (induct rule: tranclp_induct)
  apply (simp add: list_all2_trancl1 tranclp.r_into_trancl)
  by (smt list_all2_mono q62 tranclp.r_into_trancl tranclp_trans)

lemma sublist3_trancl1:
  "(\<lambda>xs ys. xs \<noteq> ys \<and> list_all2 f (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 f\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  apply (induct rule: tranclp_induct)
  apply (simp add: list_all2_trancl1 tranclp.r_into_trancl)
  by (smt list_all2_mono q62 tranclp.r_into_trancl tranclp_trans)

(*
lemma list_all2_trancl2:
  assumes as_r: "(\<forall>x. P x x)" 
  shows "list_all2 P\<^sup>+\<^sup>+ (take (length ys) xs) ys \<Longrightarrow>
         (\<lambda>xs ys. list_all2 P (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys"
proof(induction rule: list_all2_induct)
  case Nil then show ?case
    by (simp add: tranclp.r_into_trancl)
next
  case (Cons x xs y ys) show ?case
  proof -
    from as_r obtain zs where 
      lp_xs_zs: "(list_all2 P) xs zs" and lp_pp_xs_zs: "(\<lambda>xs ys. xs \<noteq> ys \<and> list_all2 P xs ys)\<^sup>+\<^sup>+ zs ys"
(*      by (meson Cons.hyps(2) list_all2_same list_all2_trancl2)
    from Cons.hyps(1) have x_xs_y_zs: "(list_all2 P)\<^sup>+\<^sup>+ (x#xs) (y#zs)"
    proof(induction rule: tranclp_induct)
      case base then show ?case using as_r lp_xs_zs by blast
    next
      case (step y z) then show ?case
        using as_r by (metis list.rel_inject(2) list_all2_same tranclp.trancl_into_trancl)
    qed
    from lp_pp_xs_zs have "(list_all2 P)\<^sup>+\<^sup>+ (y#zs) (y#ys)"
    proof(induction rule: tranclp_induct)
      case (base y) then show ?case using as_r by blast
    next
      case (step y z) then show ?case
        using as_r
        by (metis list.rel_inject(2) tranclp.simps)
    qed
    with x_xs_y_zs show ?thesis by force
  qed*)
qed
*)


(*
lemma sublist1_trancl2:
  "list_all2 f\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   (\<And>x. f x x) \<Longrightarrow>
   (\<lambda>xs ys. xs \<noteq> ys \<and> list_all2 f xs ys)\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: list_all2_induct)
  apply simp
  apply auto

lemma sublist2_trancl1:
  "list_all2 f\<^sup>+\<^sup>+ (take (length ys) xs) ys \<Longrightarrow>
   (\<And>x. f x x) \<Longrightarrow>
   (\<lambda>xs ys. list_all2 f (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: list_all2_induct)
  apply (simp add: tranclp.r_into_trancl)


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
  unfolding sublist_def
  apply auto
(*  by (metis (mono_tags) sublist_def sublist_induct)*)
*)

lemma sublist_subtype_implies_not_eq:
  "sublist subtype\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   xs \<noteq> ys"
  by (simp add: sublist_def)
(*
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
*)
lemma q81:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (sublist subtype)\<^sup>+\<^sup>+ xs ys"
  apply (simp add: q11)
  done

lemma list_all2_sublist_subtype_functor:
  "functor_under_rel
    (\<lambda>xs ys. list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) (take (length ys) xs) ys)
    (sublist subtype) id"
  unfolding functor_under_rel_def rel_limited_under_def sublist_def
  apply auto
  done

lemma q82:
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<lambda>xs ys. list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys"
  apply (rule_tac ?S="sublist subtype" and ?f="id" in tranclp_fun_preserve_gen_1a)
  apply (simp add: list_all2_sublist_subtype_functor)
  by simp

lemma q83:
  "(\<lambda>xs ys. list_all2 P (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x. P x x) \<Longrightarrow>
   (\<lambda>xs ys. list_all2 P xs ys)\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  apply (induct rule: converse_tranclp_induct)
  apply simp
proof -
  fix y :: "'a list" and z :: "'a list"
assume a1: "(\<lambda>xs ys. list_all2 P (take (length ys) xs) ys)\<^sup>+\<^sup>+ z ys"
  assume a2: "(\<And>x. P x x) \<Longrightarrow> (list_all2 P)\<^sup>+\<^sup>+ (take (length ys) z) ys"
  assume a3: "\<And>x. P x x"
  assume a4: "list_all2 P (take (length z) y) z"
  have f5: "list_all2 P\<^sup>+\<^sup>+ (take (length ys) z) ys"
    using a1 sublist2_trancl1 by blast
  have "\<forall>as. (list_all2 P)\<^sup>+\<^sup>+ as ys \<or> \<not> list_all2 P as (take (length ys) z)"
using a3 a2 by (metis (no_types) tranclp.r_into_trancl tranclp_trans)
then show "(list_all2 P)\<^sup>+\<^sup>+ (take (length ys) y) ys"
using f5 a4 by (metis length_take list_all2_lengthD list_all2_takeI take_take)
qed
(*  by (metis length_take list_all2_lengthD list_all2_takeI sublist2_trancl1 take_take tranclp.r_into_trancl tranclp_trans)
  by (smt append_eq_conv_conj append_take_drop_id length_take list_all2_append2 list_all2_trancl1 min_def_raw take_take tranclp_into_tranclp2)*)

lemma q84:
  "(\<lambda>xs ys. list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) (take (length ys) xs) ys)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<lambda>xs ys. list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys)\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  using q83 by blast

lemma q85:
  "(\<lambda>xs ys. list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys)\<^sup>+\<^sup>+ (take (length ys) xs) ys \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  apply (simp add: list_all2_trancl1)
  done

lemma q86:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length ys) xs) ys"
  by (simp add: list_all2_trancl1 q81 q82 q84)


lemma trancl_subtype_C_x:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length zs) xs) zs \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  using q86 apply blast
  by (metis (no_types, lifting) q86 subtype_C_x tranclp.trancl_into_trancl)

lemma trancl_subtype_x_C:
  "subtype\<^sup>+\<^sup>+ x (C ys) \<Longrightarrow>
   (\<And>zs. x = C zs \<Longrightarrow> list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length ys) zs) ys \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (no_types, lifting) q86 subtype.cases t.simps(7) trancl_subtype_A_x tranclpD)


lemma trancl_subtype_C_x:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>xa y. xa \<in> set xs \<Longrightarrow> subtype\<^sup>+\<^sup>+ xa y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y xa \<Longrightarrow> False) \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow>
    list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length zs) xs) zs \<Longrightarrow>
    xs \<noteq> zs \<Longrightarrow> P) \<Longrightarrow> P"



lemma q:
  "(sublist subtype)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   (\<And>x y z. subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype y z \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<noteq> z) \<Longrightarrow>
   xs \<noteq> ys"
  apply (induct rule: tranclp_induct)
   apply (simp add: q35)
  apply (auto)
  apply (drule subtype.intros(2))

  apply (rule fun_preserve_morphism_composition')
  by (metis fun_preserve_morphism_composition' subtype.intros(2) t.inject)

thm subtype.intros(2) t.inject





lemma trancl_subtype_C_x' [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length zs) xs) zs \<Longrightarrow> xs \<noteq> zs \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  using q35 q86 apply blast
  apply (erule subtype.cases)
  apply simp
  apply auto



(*
lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>zs. y = C zs \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ xs zs \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis sublist_mono subtype.simps t.inject t.simps(5) tranclp.r_into_trancl)
  using q11 sublist_subtype_trancl1 tranclp.trancl_into_trancl by fastforce
*)
lemma trancl_subtype_x_C [elim]:
  "subtype\<^sup>+\<^sup>+ x (C ys) \<Longrightarrow>
   (\<And>zs. x = C zs \<Longrightarrow> sublist subtype\<^sup>+\<^sup>+ zs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct x; auto)
  done

lemma q:
  "(\<And>xa. xa \<in> set zs \<Longrightarrow> subtype\<^sup>+\<^sup>+ xa xa \<Longrightarrow> False) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> False"

lemma q:
  "(\<And>xa. xa \<in> set zs \<Longrightarrow> subtype\<^sup>+\<^sup>+ xa xa \<Longrightarrow> False) \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ zs zs \<Longrightarrow> zs \<noteq> [] \<Longrightarrow> False"
  nitpick

lemma q:
  "list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length zs) xs) zs \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ (take (length xs) zs) xs \<Longrightarrow>
   (\<And>x y. x \<in> set xs \<Longrightarrow> subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False) \<Longrightarrow> False"
  apply (induct rule: list_all2_induct)
  apply (induct rule: list_all2_induct)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct x arbitrary: y)
  apply auto[1]
  apply auto[1]
  apply (erule trancl_subtype_C_x)
  apply (erule trancl_subtype_x_C)
  apply auto[1]

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x x \<Longrightarrow> False"
  apply (induct x)
  apply auto[1]
  apply auto[1]
  apply (erule trancl_subtype_C_x; auto)
(*
  apply (erule tranclp.cases; auto)
  using subtype_acyclic apply auto[1]
  apply (erule subtype.cases; auto)
  apply (erule trancl_subtype_C_x; auto)
*)
(*
  by (meson sublist_def sublist_subtype_trancl1 sublist_subtype_trancl2 tranclp.trancl_into_trancl)
*)
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




end

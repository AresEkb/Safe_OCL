theory Least_Test
  imports Main
begin

datatype ty = A | B | C | D | E | F

instantiation ty :: order
begin

fun less_ty where
  "A < x = (x = B \<or> x = C \<or> x = D \<or> x = E \<or> x = F)"
| "B < x = False"
| "C < x = (x = D \<or> x = E \<or> x = F)"
| "D < x = (x = F)"
| "E < x = (x = F)"
| "F < x = False"

definition "(\<le>) \<equiv> (\<lambda>x y :: ty. x = y \<or> x < y)"

lemma less_le_not_le_ty:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  for x y :: ty
  unfolding less_eq_ty_def apply auto
  by (erule less_ty.elims; auto)+

lemma order_refl_ty:
  "x \<le> x"
  for x :: ty
  unfolding less_eq_ty_def by simp

lemma order_trans_ty:
  "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  for x y z :: ty
  unfolding less_eq_ty_def apply auto
  by (erule less_ty.elims; auto)

lemma antisym_ty:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  for x y :: ty
  unfolding less_eq_ty_def apply auto
  by (erule less_ty.elims; auto)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_ty)
  apply (simp add: order_refl_ty)
  apply (rule order_trans_ty; auto)
  by (simp add: antisym_ty)

end

inductive test where
  "test B C"
| "test C D"
| "test D E"
| "test D D"
| "test E A"

inductive test_not_least where
  "test y' z' \<Longrightarrow>
   x \<le> y' \<Longrightarrow>
   y' < y \<Longrightarrow>
   test_not_least x y z"

inductive least_test where
  "test y z \<Longrightarrow>
   x \<le> y \<Longrightarrow>
   \<not> test_not_least x y z \<Longrightarrow>
   least_test x y z"

lemma q11:
  "test y z \<Longrightarrow> x \<le> y \<Longrightarrow> (\<And>y' z'. test y' z' \<Longrightarrow> x \<le> y' \<Longrightarrow> \<not> y' < y) \<Longrightarrow>
   least_test x y z"
  by (smt least_test.intros test_not_least.cases)

lemma least_test_simp:
  "least_test x y z = (test y z \<and> x \<le> y \<and> (\<forall>y' z'. test y' z' \<longrightarrow> x \<le> y' \<longrightarrow> \<not> y' < y))"
  using least_test.simps q11 test_not_least.intros by fastforce

lemma q22:
  "\<not> test_not_least x y z =
   (\<forall>y' z'. test y' z' \<longrightarrow> x \<le> y' \<longrightarrow> \<not> y' < y)"
  by (smt test_not_least.cases test_not_least.intros)

lemma q22':
  "test_not_least x y z =
   (\<exists>y' z'. test y' z' \<and> x \<le> y' \<and> y' < y)"
  by (smt test_not_least.cases test_not_least.intros)

lemma q:
  "\<not> (test y' z' \<longrightarrow> x \<le> y' \<longrightarrow> \<not> y' < y)"
  apply (unfold HOL.not_imp)

(*
  HOL.not_all: (\<not> (\<forall>x. ?P x)) = (\<exists>x. \<not> ?P x)
*)

lemma q23:
  "(\<forall>y' z'. test y' z' \<longrightarrow> x \<le> y' \<longrightarrow> \<not> y' < y) \<Longrightarrow>
   \<not> test_not_least x y z"
  using test_not_least.cases by force

inductive least_test_not_unique where
  "least_test x y' z' \<Longrightarrow>
   y \<noteq> y' \<or> z \<noteq> z' \<Longrightarrow>
   least_test_not_unique x y z"

inductive unique_least_test where
  "least_test x y z \<Longrightarrow>
   \<not> least_test_not_unique x y z \<Longrightarrow>
   unique_least_test x y z"

lemma q41:
  "(\<not> least_test_not_unique x y z) =
   (\<forall>y' z'. least_test x y' z' \<longrightarrow> y = y' \<and> z = z')"
  by (simp add: least_test_not_unique.simps)

lemma q42:
  "least_test_not_unique x y z =
   (\<exists>y' z'. least_test x y' z' \<and> (y \<noteq> y' \<or> z \<noteq> z'))"
  by (meson least_test_not_unique.cases least_test_not_unique.intros)

lemma q31:
  "unique_least_test x y z = (least_test x y z \<and>
   (\<forall>y' z'. least_test x y' z' \<longrightarrow> y = y' \<and> z = z'))"
  by (simp add: least_test_not_unique.simps unique_least_test.simps)


lemma q32:
  " unique_least_test x y z =
    (test y z \<and>
     x \<le> y \<and>
     (\<forall>y' z'.
         test y' z' \<and>
         x \<le> y' \<and>
         (\<forall>y'a. Ex (test y'a) \<longrightarrow> x \<le> y'a \<longrightarrow> \<not> y'a < y') \<longrightarrow>
         y = y' \<and> z = z' \<and> \<not> y' < y))"
  unfolding q31 least_test_simp apply simp
(*  by (smt le_less less_le_not_le less_ty.elims(1) order.strict_implies_order)*)
  sorry

lemma q:
  "(
         test y' z' \<and>
         x \<le> y' \<and>
         (\<forall>y'a. Ex (test y'a) \<longrightarrow> x \<le> y'a \<longrightarrow> \<not> y'a < y') \<longrightarrow>
         y = y' \<and> z = z' \<and> \<not> y' < y) =
    (
         test y' z' \<longrightarrow>
         x \<le> y' \<longrightarrow>
         y = y' \<and> z = z' \<and> \<not> y' < y)"

lemma q32:
  " unique_least_test x y z =
    (test y z \<and>
     x \<le> y \<and>
     (\<forall>y' z'.
         test y' z' \<longrightarrow>
         x \<le> y' \<longrightarrow>
         y = y' \<and> z = z' \<and> \<not> y' < y))"
  unfolding q31 least_test_simp apply simp
  apply (rule iffI)
  apply (elim conjE)
  apply (intro conjI)
  apply blast
    apply blast
  apply (elim allE impE)
        apply (intro allI impI conjI)
  apply simp
  apply simp

lemma q33:
  "unique_least_test x y z = (test y z \<and> x \<le> y \<and> 
   (\<forall>y' z'. test y' z' \<longrightarrow> x \<le> y' \<longrightarrow> y = y' \<and> z = z' \<and> \<not> y' < y))"
  nitpick
  unfolding q31 least_test_simp
  apply simp
  apply (rule iffI)
   apply (elim conjE allE impE)
  apply auto[1]
  apply (intro conjI)

lemma q:
  "unique_least_test x y z =
    (test y z \<and>
     x \<le> y \<and>
     (\<forall>y'. Ex (test y') \<longrightarrow> x \<le> y' \<longrightarrow> \<not> y' < y) \<and>
     (\<forall>y' z'.
         test y' z' \<and>
         x \<le> y' \<longrightarrow>
         y = y' \<and> z = z' \<and> \<not> y' < y))"
  unfolding q31 least_test_simp apply simp

lemma q31':
  "unique_least_test x y z = (least_test x y z \<and>
   (\<forall>y' z'. least_test x y' z' \<longrightarrow> y = y' \<and> z = z'))"
  unfolding least_test_simp apply simp
  unfolding q31 least_test_simp apply simp
  done


(*
  by (metis less_irrefl less_ty.elims(2) test.cases
      ty.distinct(1) ty.distinct(19) ty.distinct(21)
      ty.distinct(23) ty.distinct(3) ty.distinct(5) ty.distinct(7))
*)
(*
  by (smt less_ty.elims(2) test.simps ty.distinct(1) ty.distinct(19)
      ty.distinct(21) ty.distinct(23) ty.distinct(27) ty.distinct(29)
      ty.distinct(3) ty.distinct(5) ty.distinct(7))
*)
(*
lemma least_test_simp:
  "least_test x y z = (test y z \<and> x \<le> y \<and> (\<forall>y' z'. test y' z' \<longrightarrow> x \<le> y' \<longrightarrow> \<not> y' < y))"
  using least_test.simps q11 test_not_least.intros by fastforce
*)









code_pred [show_modes] unique_least_test .

thm test_not_least.equation

values "{(y, z). least_test A y z}"
values "{(y, z). least_test B y z}" (* (B, C) *)
values "{(y, z). least_test C y z}" (* (C, D) *)
values "{(y, z). least_test D y z}"
values "{(y, z). least_test E y z}"

values "{(y, z). unique_least_test A y z}"
values "{(y, z). unique_least_test B y z}" (* (B, C) *)
values "{(y, z). unique_least_test C y z}" (* (C, D) *)
values "{(y, z). unique_least_test D y z}"
values "{(y, z). unique_least_test E y z}" (* (E, A) *)

lemma unique_least_test_det:
  "unique_least_test x y z \<Longrightarrow>
   unique_least_test x y' z' \<Longrightarrow> y = y' \<and> z = z'"
  using least_test_not_unique.intros unique_least_test.cases by blast

lemma least_test_greater_eq:
  "least_test x y z \<Longrightarrow> x \<le> y"
  using least_test.cases by auto

lemma least_test_least:
  "least_test x y z \<Longrightarrow>
   test y' z' \<Longrightarrow> x \<le> y' \<Longrightarrow> \<not> y' < y"
  by (meson least_test.cases test_not_least.intros)


(*
definition (in ord)
  Least :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" (binder "LEAST " 10) where
  "Least P = (THE x. P x \<and> (\<forall>y. P y \<longrightarrow> x \<le> y))"

lemma Least_equality:
  assumes "P x"
    and "\<And>y. P y \<Longrightarrow> x \<le> y"
  shows "Least P = x"
unfolding Least_def by (rule the_equality)
  (blast intro: assms antisym)+

lemma LeastI2_order:
  assumes "P x"
    and "\<And>y. P y \<Longrightarrow> x \<le> y"
    and "\<And>x. P x \<Longrightarrow> \<forall>y. P y \<longrightarrow> x \<le> y \<Longrightarrow> Q x"
  shows "Q (Least P)"
unfolding Least_def by (rule theI2)
  (blast intro: assms antisym)+

*)

lemma least_test_least':
  "least_test x y z = ((\<forall>y'. \<exists>z'. test y' z' \<and> x \<le> y' \<longrightarrow> \<not> y' < y) \<and> (\<exists>z''. test y z''))"
  apply auto
  apply (simp add: least_test_least)
  using least_test.cases apply blast

value "least_test A B C"
value "test E A"
value "A \<le> E"
value "B \<le> E"

end

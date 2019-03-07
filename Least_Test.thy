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

inductive least_test_not_unique where
  "least_test x y' z' \<Longrightarrow>
   y \<noteq> y' \<or> z \<noteq> z' \<Longrightarrow>
   least_test_not_unique x y z"

inductive unique_least_test where
  "least_test x y z \<Longrightarrow>
   \<not> least_test_not_unique x y z \<Longrightarrow>
   unique_least_test x y z"

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

end

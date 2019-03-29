(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Errorable Type\<close>
theory Errorable_Type
  imports Main "HOL-Library.FSet"
begin

datatype 'a errorable_type ("_\<^sub>E" [21] 21) =
  ErrorFree 'a
| Errorable 'a

instantiation errorable_type :: (order) order
begin

fun less_errorable_type where
  "ErrorFree \<tau> < ErrorFree \<sigma> = (\<tau> < \<sigma>)"
| "Errorable \<tau> < ErrorFree \<sigma> = False"
| "ErrorFree \<tau> < Errorable \<sigma> = (\<tau> \<le> \<sigma>)"
| "Errorable \<tau> < Errorable \<sigma> = (\<tau> < \<sigma>)"

fun less_eq_errorable_type where
  "ErrorFree \<tau> \<le> ErrorFree \<sigma> = (\<tau> \<le> \<sigma>)"
| "Errorable \<tau> \<le> ErrorFree \<sigma> = False"
| "ErrorFree \<tau> \<le> Errorable \<sigma> = (\<tau> \<le> \<sigma>)"
| "Errorable \<tau> \<le> Errorable \<sigma> = (\<tau> \<le> \<sigma>)"

lemma less_le_not_le_errorable_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a errorable_type"
  by (cases \<tau>; cases \<sigma>; auto)

lemma order_refl_errorable_type:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a errorable_type"
  by (cases \<tau>; auto)

lemma order_trans_errorable_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a errorable_type"
  by (cases \<tau>; cases \<sigma>; cases \<rho>; auto)

lemma antisym_errorable_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a errorable_type"
  by (cases \<tau>; cases \<sigma>; auto)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_errorable_type)
  apply (simp add: order_refl_errorable_type)
  using order_trans_errorable_type apply blast
  by (simp add: antisym_errorable_type)

end

lemma type_less_x_ErrorFree_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < ErrorFree \<sigma>"
  by simp

lemma type_less_eq_x_ErrorFree_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> ErrorFree \<sigma>"
  by simp

lemma type_less_x_Errorable_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Errorable \<sigma>"
  "\<tau> = Errorable \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Errorable \<sigma>"
  by simp_all

lemma type_less_eq_x_Errorable_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Errorable \<sigma>"
  "\<tau> = Errorable \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Errorable \<sigma>"
  by simp_all

lemma type_less_x_ErrorFree [elim!]:
  "\<tau> < ErrorFree \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule less_errorable_type.elims; auto)

lemma type_less_eq_x_ErrorFree [elim!]:
  "\<tau> \<le> ErrorFree \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule less_eq_errorable_type.elims; auto)

lemma type_less_x_Errorable [elim!]:
  "\<tau> < Errorable \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Errorable \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule less_errorable_type.elims; auto)

lemma type_less_eq_x_Errorable [elim!]:
  "\<tau> \<le> Errorable \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Errorable \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule less_eq_errorable_type.elims; auto)

lemma type\<^sub>N\<^sub>E_less_left_simps [simp]:
  "ErrorFree \<rho> < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = ErrorFree \<upsilon> \<and> \<rho> < \<upsilon> \<or>
      \<sigma> = Errorable \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  "Errorable \<rho> < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Errorable \<upsilon> \<and> \<rho> < \<upsilon>)"
  by (induct \<sigma>; auto)+

lemma type\<^sub>N\<^sub>E_less_eq_left_simps [simp]:
  "ErrorFree \<rho> \<le> \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = ErrorFree \<upsilon> \<and> \<rho> \<le> \<upsilon> \<or>
      \<sigma> = Errorable \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  "Errorable \<rho> \<le> \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Errorable \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  by (auto simp: dual_order.order_iff_strict)

lemma type\<^sub>N\<^sub>E_less_right_simps [simp]:
  "\<tau> < ErrorFree \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> < \<upsilon>)"
  "\<tau> < Errorable \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Errorable \<rho> \<and> \<rho> < \<upsilon>)"
  by auto

lemma type\<^sub>N\<^sub>E_less_eq_right_simps [simp]:
  "\<tau> \<le> ErrorFree \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> \<le> \<upsilon>)"
  "\<tau> \<le> Errorable \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Errorable \<rho> \<and> \<rho> \<le> \<upsilon>)"
  by auto

notation sup (infixl "\<squnion>" 65)

instantiation errorable_type :: (semilattice_sup) semilattice_sup
begin

fun sup_errorable_type where
  "ErrorFree \<tau> \<squnion> \<sigma> = (case \<sigma>
    of ErrorFree \<rho> \<Rightarrow> ErrorFree (\<tau> \<squnion> \<rho>)
     | Errorable \<rho> \<Rightarrow> Errorable (\<tau> \<squnion> \<rho>))"
| "Errorable \<tau> \<squnion> \<sigma> = (case \<sigma>
    of ErrorFree \<rho> \<Rightarrow> Errorable (\<tau> \<squnion> \<rho>)
     | Errorable \<rho> \<Rightarrow> Errorable (\<tau> \<squnion> \<rho>))"

lemma sup_ge1_errorable_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: "'a errorable_type"
  by (cases \<tau>; cases \<sigma>; simp)

lemma sup_commut_errorable_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: "'a errorable_type"
  by (cases \<tau>; cases \<sigma>; simp add: sup.commute)

lemma sup_least_errorable_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a errorable_type"
  by (cases \<tau>; cases \<sigma>; cases \<rho>; simp)

instance
  apply intro_classes
  apply (simp add: sup_ge1_errorable_type)
  apply (simp add: sup_ge1_errorable_type sup_commut_errorable_type)
  by (simp add: sup_least_errorable_type)

end

fun is_errorable_type where
  "is_errorable_type (ErrorFree \<tau>) = False"
| "is_errorable_type (Errorable \<tau>) = True"

abbreviation "is_error_free \<tau> \<equiv> \<not> is_errorable_type \<tau>"

fun to_error_free where
  "to_error_free (ErrorFree \<tau>) = (ErrorFree \<tau>)"
| "to_error_free (Errorable \<tau>) = (ErrorFree \<tau>)"

fun to_errorable where
  "to_errorable (ErrorFree \<tau>) = (Errorable \<tau>)"
| "to_errorable (Errorable \<tau>) = (Errorable \<tau>)"

fun unwrap_errorable_type where
  "unwrap_errorable_type (ErrorFree \<tau>) = \<tau>"
| "unwrap_errorable_type (Errorable \<tau>) = \<tau>"

end

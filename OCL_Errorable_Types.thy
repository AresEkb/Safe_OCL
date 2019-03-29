(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Errorable Types\<close>
theory OCL_Errorable_Types
  imports "OCL_Types" Errorable_Type
begin

(*** Definition *************************************************************)

section \<open>Definition\<close>

type_synonym 'a type\<^sub>N\<^sub>E = "'a type\<^sub>N errorable_type"

abbreviation Required_ErrorFree ("_[1]" [1000] 1000) where
  "Required_ErrorFree \<tau> \<equiv> ErrorFree (Required \<tau>)"

abbreviation Optional_ErrorFree ("_[?]" [1000] 1000) where
  "Optional_ErrorFree \<tau> \<equiv> ErrorFree (Optional \<tau>)"

abbreviation Required_Errorable ("_[1!]" [1000] 1000) where
  "Required_Errorable \<tau> \<equiv> Errorable (Required \<tau>)"

abbreviation Optional_Errorable ("_[?!]" [1000] 1000) where
  "Optional_Errorable \<tau> \<equiv> Errorable (Optional \<tau>)"


fun is_finite_type where
  "is_finite_type (ErrorFree \<tau>) = is_finite_type\<^sub>N \<tau>"
| "is_finite_type (Errorable \<tau>) = is_finite_type\<^sub>N \<tau>"

fun is_required_type\<^sub>N
and is_required_type where
  "is_required_type\<^sub>N (Required \<tau>) = True"
| "is_required_type\<^sub>N (Optional \<tau>) = False"

| "is_required_type (ErrorFree \<tau>) = is_required_type\<^sub>N \<tau>"
| "is_required_type (Errorable \<tau>) = is_required_type\<^sub>N \<tau>"

abbreviation "is_optional_type \<tau> \<equiv> \<not> is_required_type \<tau>"

fun is_object_type where
  "is_object_type (ErrorFree \<tau>) = is_object_type\<^sub>N \<tau>"
| "is_object_type (Errorable \<tau>) = is_object_type\<^sub>N \<tau>"

inductive element_type where
  "element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   element_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   element_type (Errorable \<tau>) (Errorable \<sigma>)"

inductive is_collection_type where
  "element_type \<tau> \<sigma> \<Longrightarrow>
   is_collection_type \<tau>"

inductive to_single_type where
  "\<not> is_collection_type \<tau> \<Longrightarrow>
   to_single_type \<tau> \<tau>"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   to_single_type \<tau> \<rho>"

inductive inner_element_type where
  "element_type \<tau> \<sigma> \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   inner_element_type \<tau> \<rho>"

inductive update_element_type where
  "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (ErrorFree \<tau>) (Errorable \<sigma>) (Errorable \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>)"

inductive to_unique_collection_type where
  "to_unique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_unique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type (Errorable \<tau>) (Errorable \<sigma>)"

inductive to_nonunique_collection_type where
  "to_nonunique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_nonunique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type (Errorable \<tau>) (Errorable \<sigma>)"

inductive to_ordered_collection_type where
  "to_ordered_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_ordered_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type (Errorable \<tau>) (Errorable \<sigma>)"

inductive tuple_element_type where
  "fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   tuple_element_type (Tuple \<pi>)[1] elem (ErrorFree \<tau>)"
| "fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   tuple_element_type (Tuple \<pi>)[1!] elem (Errorable \<tau>)"

abbreviation "to_required_type \<equiv> map_errorable_type to_required_type\<^sub>N"
abbreviation "to_optional_type_nested \<equiv> map_errorable_type to_optional_type_nested\<^sub>N"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma element_type_det:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   element_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: element_type.simps element_type\<^sub>N_det)

lemma to_single_type_det:
  "to_single_type \<tau> \<sigma> \<Longrightarrow>
   to_single_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (induct arbitrary: \<rho> rule: to_single_type.induct)
  apply (metis is_collection_type.intros to_single_type.cases)
  by (metis element_type_det is_collection_type.intros to_single_type.cases)

lemma inner_element_type_det:
  "inner_element_type \<tau> \<sigma> \<Longrightarrow>
   inner_element_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (auto simp: inner_element_type.simps)
  using element_type_det to_single_type_det by blast

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<upsilon> \<Longrightarrow> \<rho> = \<upsilon>"
  by (auto simp: update_element_type.simps update_element_type\<^sub>N_det)

lemma to_unique_collection_type_det:
  "to_unique_collection_type \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_unique_collection_type.simps to_unique_collection_type\<^sub>N_det)

lemma to_nonunique_collection_type_det:
  "to_nonunique_collection_type \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_nonunique_collection_type.simps to_nonunique_collection_type\<^sub>N_det)

lemma to_ordered_collection_type_det:
  "to_ordered_collection_type \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_ordered_collection_type.simps to_ordered_collection_type\<^sub>N_det)

lemma tuple_element_type_det:
  "tuple_element_type \<tau> elem \<sigma> \<Longrightarrow>
   tuple_element_type \<tau> elem \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (induct rule: tuple_element_type.induct; erule tuple_element_type.cases; auto)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred element_type .
code_pred is_collection_type .
code_pred to_single_type .
code_pred inner_element_type .
code_pred to_unique_collection_type .
code_pred to_nonunique_collection_type .
code_pred to_ordered_collection_type .
code_pred tuple_element_type .

end

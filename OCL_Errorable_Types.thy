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

type_synonym 'a type\<^sub>N\<^sub>E = "'a type\<^sub>N errorable"

notation to_errorable_type ("_[!]" [1000] 1000)

abbreviation Required_ErrorFree ("_[1]" [1000] 1000) where
  "Required_ErrorFree \<tau> \<equiv> ErrorFree (Required \<tau>)"

abbreviation Optional_ErrorFree ("_[?]" [1000] 1000) where
  "Optional_ErrorFree \<tau> \<equiv> ErrorFree (Optional \<tau>)"

abbreviation Required_Errorable ("_[1!]" [1000] 1000) where
  "Required_Errorable \<tau> \<equiv> Errorable (Required \<tau>)"

abbreviation Optional_Errorable ("_[?!]" [1000] 1000) where
  "Optional_Errorable \<tau> \<equiv> Errorable (Optional \<tau>)"


fun finite_type where
  "finite_type (ErrorFree \<tau>) = finite_type\<^sub>N \<tau>"
| "finite_type (Errorable \<tau>) = finite_type\<^sub>N \<tau>"

inductive object_type where
  "object_type\<^sub>N \<tau> \<C> n \<Longrightarrow>
   object_type (ErrorFree \<tau>) \<C> n"
| "object_type\<^sub>N \<tau> \<C> n \<Longrightarrow>
   object_type (Errorable \<tau>) \<C> n"

inductive collection_type where
  "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type (ErrorFree \<tau>) k (ErrorFree \<sigma>) n"
| "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type (Errorable \<tau>) k (Errorable \<sigma>) n"

(* Тут нужен комментарий, почему мы спускаем ошибочность до элементов *)

inductive map_type where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) n"

inductive map_type' where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (ErrorFree \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) n"

(* Тут нужен комментарий, почему мы спускаем ошибочность до элементов *)

inductive tuple_type where
  "tuple_type\<^sub>N \<tau> \<pi> n \<Longrightarrow>
   tuple_type (ErrorFree \<tau>) (fmmap ErrorFree \<pi>) n"
| "tuple_type\<^sub>N \<tau> \<pi> n \<Longrightarrow>
   tuple_type (Errorable \<tau>) (fmmap Errorable \<pi>) n"

inductive tuple_type' where
  "tuple_type\<^sub>N \<tau> (fmmap unwrap_errorable_type \<pi>) n \<Longrightarrow>
   \<not> fBex (fmran \<pi>) errorable_type \<Longrightarrow>
   tuple_type' (ErrorFree \<tau>) \<pi> n"
| "tuple_type\<^sub>N \<tau> (fmmap unwrap_errorable_type \<pi>) n \<Longrightarrow>
   fBex (fmran \<pi>) errorable_type \<Longrightarrow>
   tuple_type' (Errorable \<tau>) \<pi> n"

(* Доказать эквивалентность предикатов *)

inductive is_collection_type where
  "collection_type \<tau> _ _ _ \<Longrightarrow>
   is_collection_type \<tau>"

inductive to_single_type where
  "\<not> is_collection_type \<tau> \<Longrightarrow>
   to_single_type \<tau> \<tau>"
| "collection_type \<tau> _ \<sigma> _ \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   to_single_type \<tau> \<rho>"

inductive inner_element_type where
  "collection_type \<tau> _ \<sigma> _ \<Longrightarrow>
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
(*
inductive tuple_element_type where
  "fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   tuple_element_type (Tuple \<pi>)[1] elem (ErrorFree \<tau>)"
| "fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   tuple_element_type (Tuple \<pi>)[1!] elem (Errorable \<tau>)"
*)

fun required_type where
  "required_type (ErrorFree \<tau>) = required_type\<^sub>N \<tau>"
| "required_type (Errorable \<tau>) = required_type\<^sub>N \<tau>"

abbreviation "optional_type \<tau> \<equiv> \<not> required_type \<tau>"

abbreviation "to_required_type \<equiv> map_errorable to_required_type\<^sub>N"
abbreviation "to_optional_type_nested \<equiv> map_errorable to_optional_type_nested\<^sub>N"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma collection_type_det:
  "collection_type \<tau> k\<^sub>1 \<sigma>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   collection_type \<tau> k\<^sub>2 \<sigma>\<^sub>2 n\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "collection_type \<tau>\<^sub>1 k \<sigma> n \<Longrightarrow>
   collection_type \<tau>\<^sub>2 k \<sigma> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim collection_type.cases; simp add: collection_type\<^sub>N_det(1))
  by (elim collection_type.cases; simp add: collection_type\<^sub>N_det(2))

lemma map_type_det:
  "map_type \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 \<Longrightarrow>
   map_type \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "map_type' \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow>
   map_type' \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim map_type.cases; simp add: map_type\<^sub>N_det(1))
  by (elim map_type'.cases; simp add: map_type\<^sub>N_det(2))

lemma tuple_type_det:
  "tuple_type \<tau> \<pi>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   tuple_type \<tau> \<pi>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<and>  n\<^sub>1 =  n\<^sub>2"
  "tuple_type' \<tau>\<^sub>1 \<pi> n \<Longrightarrow>
   tuple_type' \<tau>\<^sub>2 \<pi> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim tuple_type.cases)
  using tuple_type\<^sub>N_det(1) apply blast+
  apply (elim tuple_type'.cases)
  using tuple_type\<^sub>N_det(2) by blast+

lemma to_single_type_det:
  "to_single_type \<tau> \<sigma> \<Longrightarrow>
   to_single_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (induct rule: to_single_type.induct)
  apply (erule to_single_type.cases; simp add: is_collection_type.intros)
  using collection_type_det(1) is_collection_type.intros to_single_type.simps by blast

lemma inner_element_type_det:
  "inner_element_type \<tau> \<sigma> \<Longrightarrow>
   inner_element_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  unfolding inner_element_type.simps
  using inner_element_type.simps collection_type_det to_single_type_det by blast

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
(*
lemma tuple_element_type_det:
  "tuple_element_type \<tau> elem \<sigma> \<Longrightarrow>
   tuple_element_type \<tau> elem \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (induct rule: tuple_element_type.induct; erule tuple_element_type.cases; auto)
*)
(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred object_type .
code_pred collection_type .
code_pred map_type .
code_pred map_type' .
code_pred tuple_type .
code_pred tuple_type' .
code_pred is_collection_type .
code_pred to_single_type .
code_pred inner_element_type .
code_pred update_element_type .
code_pred to_unique_collection_type .
code_pred to_nonunique_collection_type .
code_pred to_ordered_collection_type .

values "{(x, y, n). map_type (Map (Boolean[\<^bold>1] :: nat type\<^sub>N) Integer[\<^bold>?])[1] x y n}"
values "{(x, y, n). map_type (Map (Boolean[\<^bold>1] :: nat type\<^sub>N) Integer[\<^bold>?])[1!] x y n}"
values "{(x, y, n). map_type (Map (Boolean[\<^bold>1] :: nat type\<^sub>N) Integer[\<^bold>?])[?] x y n}"
values "{x. map_type' x (Boolean[1] :: nat type\<^sub>N\<^sub>E) Integer[?] False}"
values "{x. map_type' x (Boolean[1] :: nat type\<^sub>N\<^sub>E) Integer[?] True}"
values "{x. map_type' x (Boolean[1!] :: nat type\<^sub>N\<^sub>E) Integer[?!] True}"
values "{x. map_type' x (Boolean[1] :: nat type\<^sub>N\<^sub>E) Integer[?!] True}"

values "{(k, x, n). collection_type (Set (Boolean[\<^bold>1] :: nat type\<^sub>N))[1] k x n}"
values "{(k, x, n). collection_type (Set (Boolean[\<^bold>1] :: nat type\<^sub>N))[?!] k x n}"
values "{x. collection_type x BagKind (Boolean[?] :: nat type\<^sub>N\<^sub>E) False}"
values "{x. collection_type x SetKind (Boolean[1!] :: nat type\<^sub>N\<^sub>E) True}"

values "{x. tuple_type' x (fmempty(STR ''a'' \<mapsto>\<^sub>f Boolean[1] :: nat type\<^sub>N\<^sub>E)
  (STR ''b'' \<mapsto>\<^sub>f Real[1] :: nat type\<^sub>N\<^sub>E)) False}"
values "{x. tuple_type' x (fmempty(STR ''a'' \<mapsto>\<^sub>f Boolean[1!] :: nat type\<^sub>N\<^sub>E)
  (STR ''b'' \<mapsto>\<^sub>f Real[?] :: nat type\<^sub>N\<^sub>E)) False}"
values "{(x, n). tuple_type (Tuple (fmap_of_list
  [(STR ''a'', Boolean[\<^bold>1] :: nat type\<^sub>N), (STR ''b'', Real[\<^bold>1])]))[1] x n}"
values "{(x, n). tuple_type (Tuple (fmap_of_list
  [(STR ''a'', Boolean[\<^bold>1] :: nat type\<^sub>N), (STR ''b'', Real[\<^bold>1])]))[?!] x n}"

end

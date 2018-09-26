theory EboolTest
  imports Main "~~/src/HOL/Library/Adhoc_Overloading"
begin

notation
  bot ("\<bottom>")

class opt = bot +
  fixes null :: "'a" ("\<epsilon>")

declare [[coercion_enabled]]

(* ebool *)

typedef ebool = "UNIV :: bool option set" ..

definition ebool :: "bool \<Rightarrow> ebool" where
  "ebool b = Abs_ebool (Some b)"

declare [[coercion "ebool :: bool \<Rightarrow> ebool"]]

instantiation ebool :: bot
begin
definition "\<bottom> \<equiv> Abs_ebool None"
instance ..
end

free_constructors case_ebool for
  ebool
| "\<bottom> :: ebool"
  apply (metis Rep_ebool_inverse bot_ebool_def ebool_def not_Some_eq)
  apply (smt Abs_ebool_inverse ebool_def iso_tuple_UNIV_I option.inject)
  by (simp add: Abs_ebool_inject bot_ebool_def ebool_def)

lemmas ebool2_cases = ebool.exhaust[case_product ebool.exhaust]
lemmas ebool3_cases = ebool.exhaust[case_product ebool.exhaust ebool.exhaust]

fun ebool_and :: "ebool \<Rightarrow> ebool \<Rightarrow> ebool" (infixr "\<^bold>\<and>" 35) where
  "ebool_and a b = (a \<and> b)"
| "ebool_and False _ = False"
| "ebool_and _ False = False"
| "ebool_and \<bottom> _ = \<bottom>"
| "ebool_and _ \<bottom> = \<bottom>"

(* bool *)

typedef obool = "UNIV :: ebool option set" ..

definition obool :: "bool \<Rightarrow> obool" where
  "obool b = Abs_obool (Some (ebool b))"

instantiation obool :: opt
begin
definition "\<bottom> = Abs_obool (Some \<bottom>)"
definition "\<epsilon> = Abs_obool None"
instance ..
end

fun ebool_to_obool :: "ebool \<Rightarrow> obool" where
  "ebool_to_obool \<bottom> = \<bottom>"
| "ebool_to_obool (ebool b) = obool b"

(* Если использовать такие конструкторы, то obool создается напрямую из bool
   При этом во всех функциях придется переопределять логику для bool и \<bottom> *)
(*
free_constructors case_obool for
  obool
| "\<bottom> :: obool"
| "\<epsilon> :: obool"
  apply (metis Rep_obool_inverse bot_obool_def ebool_to_obool.cases not_Some_eq obool_def void_obool_def)
  apply (metis Abs_obool_inverse UNIV_I ebool.inject obool_def option.sel)
  apply (metis Abs_obool_inverse UNIV_I bot_obool_def ebool.distinct(1) obool_def option.sel)
  apply (metis Abs_obool_inverse UNIV_I obool_def option.distinct(1) void_obool_def)
  by (metis Abs_obool_inverse UNIV_I bot_obool_def option.distinct(1) void_obool_def)
*)

(* Такие конструкторы позволяют повторно использовать функции, определенные для ebool *)

free_constructors case_obool for
  ebool_to_obool
| "\<epsilon> :: obool"
  apply (metis Abs_obool_cases bot_obool_def ebool_def ebool_to_obool.elims null_obool_def obool_def option.collapse)
  apply (metis Abs_obool_inverse bot_obool_def ebool_to_obool.elims iso_tuple_UNIV_I obool_def option.inject)
  by (metis Abs_obool_inverse UNIV_I bot_obool_def ebool_to_obool.elims null_obool_def obool_def option.distinct(1))

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name obool} |> Option.map #ctrs\<close>

lemmas obool2_cases = obool.exhaust[case_product obool.exhaust]
lemmas obool3_cases = obool.exhaust[case_product obool.exhaust obool.exhaust]

declare [[coercion "obool :: bool \<Rightarrow> obool"]]
declare [[coercion "ebool_to_obool :: ebool \<Rightarrow> obool"]]

fun obool_and :: "obool \<Rightarrow> obool \<Rightarrow> obool" (infixr "\<^bold>\<and>" 35) where
  "obool_and a b = ebool_and a b"
| "obool_and \<epsilon> _ = \<epsilon>"
| "obool_and _ \<epsilon> = \<epsilon>"

lemma q:
  "obool_and \<bottom> \<epsilon> = \<bottom>"

(*
no_notation HOL.conj (infixr "\<and>" 35)
consts "(\<and>)" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
adhoc_overloading "(\<and>)" HOL.conj
adhoc_overloading "(\<and>)" ebool_and
*)

value "(True::obool) \<^bold>\<and> (False::obool)"
value "True \<^bold>\<and> \<bottom>"
value "\<bottom> \<^bold>\<and> False"

value "True \<and> False"

end

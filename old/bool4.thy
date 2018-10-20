theory bool4
  imports Main
begin

typedef bool3 = "UNIV :: bool option set" ..

definition bool3 :: "bool \<Rightarrow> bool3" where
  "bool3 b = Abs_bool3 (Some b)"

notation bot ("\<bottom>")

instantiation bool3 :: bot
begin
definition "\<bottom> \<equiv> Abs_bool3 None"
instance ..
end

free_constructors case_bool3 for
  bool3
| "\<bottom> :: bool3"
  apply (metis Rep_bool3_inverse bot_bool3_def bool3_def not_Some_eq)
  apply (smt Abs_bool3_inverse bool3_def iso_tuple_UNIV_I option.inject)
  by (simp add: Abs_bool3_inject bot_bool3_def bool3_def)


typedef bool4 = "UNIV :: bool3 option set" ..

definition bool4 :: "bool3 \<Rightarrow> bool4" where
  "bool4 b = Abs_bool4 (Some b)"

class opt = bot +
  fixes void :: "'a" ("\<epsilon>")

instantiation bool4 :: opt
begin
definition "\<bottom> = Abs_bool4 (Some \<bottom>)"
definition "\<epsilon> = Abs_bool4 None"
instance ..
end

free_constructors case_bool4 for
  bool4
| "\<epsilon> :: bool4"
  apply (metis Abs_bool4_cases bool4_def not_None_eq void_bool4_def)
  apply (metis Abs_bool4_inverse UNIV_I bool4_def option.inject)
  by (simp add: Abs_bool4_inject bool4_def void_bool4_def)


declare [[coercion_enabled]]
declare [[coercion "bool3 :: bool \<Rightarrow> bool3"]]
declare [[coercion "bool4 :: bool3 \<Rightarrow> bool4"]]

fun bool3_and :: "bool3 \<Rightarrow> bool3 \<Rightarrow> bool3" where
  "bool3_and a b = (a \<and> b)"
| "bool3_and False _ = False"
| "bool3_and _ False = False"
| "bool3_and \<bottom> _ = \<bottom>"
| "bool3_and _ \<bottom> = \<bottom>"

fun bool4_and :: "bool4 \<Rightarrow> bool4 \<Rightarrow> bool4" where
  "bool4_and a b = bool3_and a b"
| "bool4_and \<epsilon> _ = \<epsilon>"
| "bool4_and _ \<epsilon> = \<epsilon>"

lemma bool3_and_eq_bool4_and:
  "(bool3_and a b = c) =
   (bool4_and a b = c)"
  by simp
 

end

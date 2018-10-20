theory ErrorableTest
  imports Main
begin
(*
notation
  bot ("\<bottom>")

typedef 'a errorable ("_\<^sub>\<bottom>" [21] 21) = "UNIV :: 'a option set" ..

definition errorable :: "'a \<Rightarrow> 'a errorable" ("_\<^sub>\<bottom>" [1000] 1000) where
  "errorable x = Abs_errorable (Some x)"

instantiation errorable :: (type) bot
begin
definition "\<bottom> \<equiv> Abs_errorable None"
instance ..
end

free_constructors case_errorable for
  errorable
| "\<bottom> :: 'a errorable"
  apply (metis Rep_errorable_inverse bot_errorable_def errorable_def not_Some_eq)
  apply (metis Abs_errorable_inverse UNIV_I errorable_def option.inject)
  by (simp add: Abs_errorable_inject bot_errorable_def errorable_def)
*)

instantiation option :: (plus) plus
begin

fun plus_option where
  "(Some a) + (Some b) = Some (a + b)"
| "_ + _ = None"

print_theorems

instance ..
end

thm plus_option.cases

lemma plus_option_simp [code, simp]:
  shows "(Some a) + (Some b) = Some (a + b)"
    and "None + b = None"
    and "a + None = None"




value "Some (1::nat) + Some (2::nat)"
value "Some (1::nat) + None"

end

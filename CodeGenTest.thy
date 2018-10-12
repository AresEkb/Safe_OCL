theory CodeGenTest
  imports Main
begin

datatype t = A | B | C

inductive less_t :: "t \<Rightarrow> t \<Rightarrow> bool" where
  "less_t A B"
| "less_t B C"

code_pred [show_modes] less_t .

fun less_t_fun :: "t \<Rightarrow> t \<Rightarrow> bool" where
  "less_t_fun A A = False"
| "less_t_fun A B = True"
| "less_t_fun A C = True"
| "less_t_fun B C = True"
| "less_t_fun B _ = False"
| "less_t_fun C _ = False"

term tranclp

lemma tancl_less_t_code:
  "less_t\<^sup>+\<^sup>+ x y \<longleftrightarrow> less_t_fun x y"
  apply (rule iffI)
  apply (erule tranclp_trans_induct)
  apply (erule less_t.cases; simp)
  apply (metis less_t_fun.elims(2) less_t_fun.simps(3) t.simps(4))
  apply (induct rule: less_t_fun.induct; simp)
  using less_t.intros apply auto
  done

lemma tancl_less_t_code' [code_abbrev]:
  "less_t_fun x y \<longleftrightarrow> less_t\<^sup>+\<^sup>+ x y"
  by (simp add: tancl_less_t_code)

print_codeproc

(*
lemma tancl_less_t_code' [simp]:
  "less_t_fun x y \<longleftrightarrow> less_t\<^sup>+\<^sup>+ x y"
  by (simp add: tancl_less_t_code)
*)
value "less_t A B"
value "less_t_fun A C"
value "less_t\<^sup>+\<^sup>+ A C"

end
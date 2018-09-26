theory ProgLang
  imports Main "~~/src/HOL/Library/Adhoc_Overloading"
    "~~/src/HOL/Library/Finite_Map"
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65)

type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)

definition denorm :: "('a \<rightharpoonup>\<^sub>f 'b) \<Rightarrow> ('a \<times> 'b) fset" where
  "denorm m \<equiv> (\<lambda> k. (k, the (fmlookup m k))) |`| fmdom m"

definition flatten :: "('a \<times> 'b fset) fset \<Rightarrow> ('a \<times> 'b) fset" where
  "flatten s \<equiv> ffUnion ((\<lambda>(x,y). (\<lambda>z. (x,z)) |`| y) |`| s)"

definition denorm3 :: "('a \<rightharpoonup>\<^sub>f 'b \<rightharpoonup>\<^sub>f 'c) \<Rightarrow> ('a \<times> 'b \<times> 'c) fset" where
  "denorm3 m \<equiv> flatten ((\<lambda>k. (k, denorm (the (fmlookup m k)))) |`| fmdom m)"

locale type_system =
  type: semilattice_sup ts tle tl + val: order vle vl
    for ts  :: "'type \<Rightarrow> 'type \<Rightarrow> 'type" (infixl "\<squnion>" 65)
    and tle :: "'type \<Rightarrow> 'type \<Rightarrow> bool" ("(_/ \<le> _)"  [51, 51] 50)
    and tl  :: "'type \<Rightarrow> 'type \<Rightarrow> bool" ("(_/ < _)"  [51, 51] 50)
    and vle :: "'val \<Rightarrow> 'val \<Rightarrow> bool" ("(_/ as _)"  [51, 51] 50)
    and vl  :: "'val \<Rightarrow> 'val \<Rightarrow> bool" ("(_/ as! _)"  [51, 51] 50) +
  fixes type_of_val :: "'val \<Rightarrow> 'type" ("\<T> _" [75] 75)
(*  fixes cast_either :: "('val \<times> 'val) \<Rightarrow> ('val \<times> 'val) \<Rightarrow> bool" (infix "as*" 55)*)
  assumes type_of_val_eq:
    "x = y \<Longrightarrow> \<T> x = \<T> y"
  assumes type_of_val_less_eq:
    "x as y \<Longrightarrow> \<T> x \<le> \<T> y"
  assumes type_of_val_less:
    "x as! y \<Longrightarrow> \<T> x < \<T> y"
  assumes type_of_val_eq_rev:
    "\<T> x = t \<Longrightarrow> \<exists>y. \<T> y = t \<and> x = y"
  assumes type_of_val_less_eq_rev:
    "\<T> x \<le> t \<Longrightarrow> \<exists>y. \<T> y = t \<and> x as y"
  assumes type_of_val_less_rev:
    "\<T> x < t \<Longrightarrow> \<exists>y. \<T> y = t \<and> x as! y"
begin
(*
inductive cast_either :: "'val \<times> 'val \<Rightarrow> 'val \<times> 'val \<Rightarrow> bool" (infix "as*" 55) where
(*  "x as* x"*)
  "a = x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"
| "a = x \<Longrightarrow> b as! y \<Longrightarrow> (a, b) as* (x, y)"
| "a as! x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"
*)
(*
definition cast_either :: "'val \<times> 'val \<Rightarrow> 'val \<times> 'val \<Rightarrow> bool" (infix "as*" 55) where
  "cast_either x y \<equiv> (case (x,y) of ((a,b),(c,d)) \<Rightarrow>
    a = c \<and> b = d \<or> a = c \<and> b as! d \<or> a as! c \<and> b = d)"

lemma cast_either_perm:
  "(a, b) as* (x, y) = (b, a) as* (y, x)"
  apply (auto simp add: cast_either_def)
  (*apply (auto; erule cast_either.cases; elim Pair_inject)
  using cast_either.intros(1) apply auto[1]
  using cast_either.intros(3) apply auto[1]
  using cast_either.intros(2) apply auto[1]
  using cast_either.intros(1) apply auto[1]
  using cast_either.intros(3) apply auto[1]
  using cast_either.intros(2) apply auto[1]*)
  done

lemma type_of_pair_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   \<T> x \<squnion> \<T> y = \<tau>"
  apply (auto simp add: cast_either_def)
  (*apply (erule cast_either.cases; elim Pair_inject)*)
  apply (metis type.sup_idem)
  apply (metis type.sup.strict_order_iff type_of_val_less)
  apply (metis type.sup.strict_order_iff type_of_val_less type.sup_commute)
  done

lemma type_of_pair_less_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b"
  apply (auto simp add: cast_either_def)
  (*apply (erule cast_either.cases; elim Pair_inject; auto)*)
  using type.sup.mono type_of_val_less_eq val.dual_order.strict_implies_order apply blast
  using type.sup.mono type_of_val_less_eq val.dual_order.strict_implies_order apply blast
  done  
*)
end

type_synonym vname = "string"
type_synonym 'a env = "vname \<rightharpoonup> 'a"

consts
  type_of_val :: "'val \<Rightarrow> 'type"
  typing :: "'type env \<Rightarrow> 'exp \<Rightarrow> 'type \<Rightarrow> bool"
  big_step :: "'exp \<times> 'val env \<Rightarrow> 'val \<Rightarrow> bool"
  etyping :: "'type env \<Rightarrow> 'val env \<Rightarrow> bool"
  (*cast :: "'val \<Rightarrow> 'val \<Rightarrow> bool"
  cast_eq :: "'val \<Rightarrow> 'val \<Rightarrow> bool"
  cast_either :: "('val \<times> 'val) \<Rightarrow> ('val \<times> 'val) \<Rightarrow> bool"*)

locale prog_lang =
  fixes type_of_val :: "'val \<Rightarrow> 'type" ("\<T> _" [55] 55)
  fixes typing :: "'type env \<Rightarrow> 'exp \<Rightarrow> 'type \<Rightarrow> bool" ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
  fixes big_step :: "'exp \<times> 'val env \<Rightarrow> 'val \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
  fixes etyping :: "'type env \<Rightarrow> 'val env \<Rightarrow> bool" (infix "\<turnstile>" 50)
  (*fixes cast :: "'val \<Rightarrow> 'val \<Rightarrow> bool" (infix "as!" 55)
  fixes cast_eq :: "'val \<Rightarrow> 'val \<Rightarrow> bool" (infix "as" 55)
  fixes cast_either :: "('val \<times> 'val) \<Rightarrow> ('val \<times> 'val) \<Rightarrow> bool" (infix "as*" 55)*)
  assumes typing_is_fun:
    "\<Gamma> \<turnstile> exp : \<tau>\<^sub>1 \<Longrightarrow>
     \<Gamma> \<turnstile> exp : \<tau>\<^sub>2 \<Longrightarrow>
     \<tau>\<^sub>1 = \<tau>\<^sub>2"
  assumes big_step_is_fun:
    "(exp, env) \<Rightarrow> v\<^sub>1 \<Longrightarrow>
     (exp, env) \<Rightarrow> v\<^sub>2 \<Longrightarrow>
     v\<^sub>1 = v\<^sub>2"
  assumes type_preservation:
    "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow>
     (exp1, env) \<Rightarrow> v \<Longrightarrow>
     \<Gamma> \<turnstile> env \<Longrightarrow>
     \<T> v = \<tau>"
  assumes type_system_is_sound:
    "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow>
     \<Gamma> \<turnstile> env \<Longrightarrow>
     \<exists>v. (exp1, env) \<Rightarrow> v"
  assumes type_system_is_complete:
    "(exp1, env) \<Rightarrow> v \<Longrightarrow>
     \<Gamma> \<turnstile> env \<Longrightarrow>
     \<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>"
begin
  adhoc_overloading ProgLang.typing typing
  adhoc_overloading ProgLang.big_step big_step
  adhoc_overloading ProgLang.etyping etyping
  (*adhoc_overloading ProgLang.cast cast
  adhoc_overloading ProgLang.cast_eq cast_eq
  adhoc_overloading ProgLang.cast_either cast_either*)
  no_notation type_of_val ("\<T> _" [75] 75)
  no_notation typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
  no_notation big_step (infix "\<Rightarrow>" 55)
  no_notation etyping (infix "\<turnstile>" 50)
  (*no_notation cast (infix "as!" 55)
  no_notation cast_eq (infix "as" 55)
  no_notation cast_either (infix "as*" 55)*)
end
(*
notation ProgLang.typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
notation ProgLang.big_step (infix "\<Rightarrow>" 55)
notation ProgLang.etyping (infix "\<turnstile>" 50)
notation ProgLang.cast (infix "as!" 55)
notation ProgLang.cast_eq (infix "as" 55)
notation ProgLang.cast_either (infix "as*" 55)
*)

(*
locale ord_preserv =
  nat: ord nle nl + str: ord sle sl
    for nle :: "'n \<Rightarrow> 'n \<Rightarrow> bool" ("(_/ \<sqsubseteq> _)"  [51, 51] 50)
    and nl  :: "'n \<Rightarrow> 'n \<Rightarrow> bool" ("(_/ \<sqsubset> _)"  [51, 51] 50)
    and sle :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_/ \<preceq> _)"  [51, 51] 50)
    and sl  :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_/ \<prec> _)"  [51, 51] 50) +
  fixes nat_to_str :: "'n \<Rightarrow> 's"
  assumes type_of_val_less:
    "x \<sqsubseteq> y \<Longrightarrow>
     (nat_to_str x) \<preceq> (nat_to_str y)"
begin
end
*)
end

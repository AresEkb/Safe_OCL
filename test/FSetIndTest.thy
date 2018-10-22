theory FSetIndTest
  imports Main "~~/src/HOL/Library/FSet"
begin

datatype val1 = A | B
datatype val2 = C | D

inductive cast_val :: "val1 \<Rightarrow> val2 \<Rightarrow> bool" where
  "cast_val A C"
| "cast_val B D"

code_pred [show_modes] cast_val .

fun cast_val_fun :: "val1 \<Rightarrow> val2" where
  "cast_val_fun A = C"
| "cast_val_fun B = D"

fun cast_val_fun_inv :: "val2 \<Rightarrow> val1" where
  "cast_val_fun_inv C = A"
| "cast_val_fun_inv D = B"

(* 1 *)

inductive cast_fset1 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset1 {||} {||}"
| "cast_val x y \<Longrightarrow> cast_fset1 xs ys \<Longrightarrow>
   cast_fset1 (finsert x xs) (finsert y ys)"

lemma cast_fset1_left [code_pred_intro]:
  "fimage cast_val_fun xs = ys \<Longrightarrow> cast_fset1 xs ys"
  apply (induct xs arbitrary: ys)
  apply (simp add: cast_fset1.intros(1))
  by (metis (full_types) cast_fset1.intros(2) cast_val.intros(1) cast_val.intros(2) cast_val_fun.simps(1) cast_val_fun.simps(2) fimage_finsert val1.exhaust)

lemma cast_fset1_left_inv:
  "cast_fset1 xs ys \<Longrightarrow>
   fimage cast_val_fun xs = ys"
  apply (induct rule: cast_fset1.induct)
  apply simp
  using cast_val.simps by auto

code_pred [show_modes] cast_fset1
  by (simp add: cast_fset1_left_inv)

values "{x. cast_fset1 {|A, B|} x}"

(* 2 *)

inductive cast_fset2 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset2 {||} {||}"
| "cast_val x y \<Longrightarrow> cast_fset2 xs ys \<Longrightarrow>
   cast_fset2 (finsert x xs) (finsert y ys)"

lemma cast_fset2_code [code_pred_intro]:
  "fimage cast_val_fun_inv ys = xs \<Longrightarrow> cast_fset2 xs ys"
  apply (induct ys arbitrary: xs)
  apply (simp add: cast_fset2.intros(1))
  by (smt cast_fset2.intros(2) cast_val.intros(1) cast_val.intros(2) cast_val_fun_inv.elims cast_val_fun_inv.simps(1) fimage_finsert)

lemma cast_fset2_code_inv:
  "cast_fset2 xs ys \<Longrightarrow> fimage cast_val_fun_inv ys = xs"
  apply (induct rule: cast_fset2.induct)
  apply simp
  using cast_val.simps by auto

code_pred [show_modes] cast_fset2
  by (simp add: cast_fset2_code_inv(1))

lemma cast_fset1_eq_cast_fset2:
  "cast_fset1 x y = cast_fset2 x y"
  apply auto
  apply (induct rule: cast_fset1.induct)
  apply (simp add: cast_fset2.intros(1))
  apply (simp add: cast_fset2.intros(2))
  apply (induct rule: cast_fset2.induct)
  apply (simp add: cast_fset1.intros(1))
  apply (simp add: cast_fset1.intros(2))
  done

end

theory FSetIndTest
  imports Main "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Library/Multiset"
begin

datatype val1 = A | B
datatype val2 = C | D

inductive cast_val :: "val1 \<Rightarrow> val2 \<Rightarrow> bool" where
  "cast_val A C"
| "cast_val B D"

code_pred [show_modes] cast_val .

(*
definition cast_val_fun where
  "cast_val_fun \<equiv> Predicate.the \<circ> cast_val_i_o"

definition cast_val_fun_inv where
  "cast_val_fun_inv \<equiv> Predicate.the \<circ> cast_val_o_i"

value "cast_val_fun A"
*)

fun cast_val_fun :: "val1 \<Rightarrow> val2" where
  "cast_val_fun A = C"
| "cast_val_fun B = D"

fun cast_val_fun_inv :: "val2 \<Rightarrow> val1" where
  "cast_val_fun_inv C = A"
| "cast_val_fun_inv D = B"



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


inductive cast_fset2 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset2 {||} {||}"
| "cast_val x y \<Longrightarrow> cast_fset2 xs ys \<Longrightarrow>
   cast_fset2 (finsert x xs) (finsert y ys)"

lemma cast_fset2_code [code_pred_intro]:
  "fimage cast_val_fun xs = ys \<Longrightarrow> cast_fset2 xs ys"
  "fimage cast_val_fun_inv ys = xs \<Longrightarrow> cast_fset2 xs ys"
  apply (auto)
  apply (induct xs arbitrary: ys)
  apply (simp add: cast_fset2.intros(1))
  apply (metis (full_types) cast_fset2.intros(2) cast_val.intros(1) cast_val.intros(2) cast_val_fun.simps(1) cast_val_fun.simps(2) fimage_finsert val1.exhaust)
  apply (induct ys arbitrary: xs)
  apply (simp add: cast_fset2.intros(1))
  by (smt cast_fset2.intros(2) cast_val.intros(1) cast_val.intros(2) cast_val_fun_inv.elims cast_val_fun_inv.simps(1) fimage_finsert)

lemma cast_fset2_code_inv:
  "cast_fset2 xs ys \<Longrightarrow> fimage cast_val_fun xs = ys"
  "cast_fset2 xs ys \<Longrightarrow> fimage cast_val_fun_inv ys = xs"
  apply (induct rule: cast_fset2.induct)
  apply simp
  apply simp
  using cast_val.simps cast_val_fun.simps(1) apply auto[1]
  using cast_val.simps by auto

code_pred [show_modes] cast_fset2
  by (simp add: cast_fset2_code_inv(1))


inductive cast_fset3 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset3 {||} {||}"
| "cast_val x y \<Longrightarrow> cast_fset3 xs ys \<Longrightarrow>
   cast_fset3 (finsert x xs) (finsert y ys)"

lemma cast_fset3_left:
  "fimage cast_val_fun xs = ys \<Longrightarrow> cast_fset3 xs ys"
  apply (induct xs arbitrary: ys)
  apply (simp add: cast_fset3.intros(1))
  by (metis (full_types) cast_fset3.intros(2) cast_val.intros(1) cast_val.intros(2) cast_val_fun.simps(1) cast_val_fun.simps(2) fimage_finsert val1.exhaust)

lemma cast_fset3_left_inv:
  "cast_fset3 xs ys \<Longrightarrow>
   fimage cast_val_fun xs = ys"
  apply (induct rule: cast_fset3.induct)
  apply simp
  using cast_val.simps by auto

lemma cast_fset3_left_code [code]:
  "fimage cast_val_fun xs = ys \<longleftrightarrow>
   cast_fset3 xs ys"
  using cast_fset3_left cast_fset3_left_inv by blast

code_pred [show_modes] cast_fset3 .

print_theorems

values 2 "{x. cast_fset3 {|A, B|} x}"


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

lemma cast_fset1_right [code_pred_intro]:
  "fimage cast_val_fun_inv ys = xs \<Longrightarrow> cast_fset1 xs ys"
  apply (induct ys arbitrary: xs)
  apply (simp add: cast_fset1.intros(1))
  by (smt cast_fset1.intros(2) cast_val.intros(1) cast_val.intros(2) cast_val_fun_inv.elims cast_val_fun_inv.simps(1) fimage_finsert)

lemma cast_fset1_right_inv:
  "cast_fset1 xs ys \<Longrightarrow> fimage cast_val_fun_inv ys = xs"
  apply (induct rule: cast_fset1.induct)
  apply simp
  using cast_val.simps by auto
(*
lemma q127 [code]:
  "fimage cast_val_fun_inv ys = xs \<longleftrightarrow>
   cast_fset1 xs ys"
  using q125 q126 by blast
*)
code_pred [show_modes] cast_fset1
  by (simp add: cast_fset1_left_inv)

values "{x. cast_fset1 {|A, B|} x}"







inductive cast_list :: "val1 list \<Rightarrow> val2 list \<Rightarrow> bool" where
  "cast_list [] []"
| "cast_val x y \<Longrightarrow> cast_list xs ys \<Longrightarrow> cast_list (x#xs) (y#ys)"

code_pred [show_modes] cast_list .

print_theorems

values "{x. cast_list [A, B] x}"
values "{x. cast_list x [C, D]}"

(*
inductive cast_mset :: "val1 multiset \<Rightarrow> val2 multiset \<Rightarrow> bool" where
  "cast_mset {#} {#}"
| "cast_val x y \<Longrightarrow> cast_mset xs ys \<Longrightarrow> cast_mset (add_mset x xs) ys"
*)
term "rel_mset cast_val"
term "rel_fset"

code_pred [show_modes] rel_fset .

values 2 "{x. (rel_fset cast_val) {|A, B|} x}"

code_pred [show_modes] rel_mset' .

values 2 "{x. (rel_mset' cast_val) {#A, B#} x}"

inductive cast_mset :: "val1 multiset \<Rightarrow> val2 multiset \<Rightarrow> bool" where
  "cast_mset {#} {#}"
| "cast_list (x#xs) ys \<Longrightarrow> cast_mset (add_mset x (mset xs)) (mset ys)"

code_pred [show_modes] cast_mset .

print_theorems

values 2 "{x. cast_mset {#A, B#} x}"




(*
definition ListFSet :: "'a list \<Rightarrow> 'a fset" where
  "ListFSet = fset_of_list"

code_datatype ListFSet

lemma fempty_ListFSet [code]:
  "fempty = ListFSet []"
  by (simp add: ListFSet_def)

lemma finsert_ListFSet [code]:
  "finsert x (ListFSet xs) = ListFSet (x#xs)"
  by (simp add: ListFSet_def)

definition fset_list :: "'a fset \<Rightarrow> 'a list" where
  "fset_list (ListFSet xs) = xs"

lemma [code abstype]:
  "fset_of_list (list_fset)"
*)

code_pred [show_modes] cast_fset1 .

code_thms cast_fset1

print_theorems

values 2 "{x. cast_fset1 {|A, B|} x}"


inductive cast_fset2 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset2 {||} {||}"
| "\<And>x y. x |\<in>| xs \<Longrightarrow> y |\<in>| ys \<Longrightarrow> cast_val x y \<Longrightarrow>  cast_fset2 xs ys"

print_theorems

code_pred [show_modes] cast_fset2 .

lemma cast_fset1_imp_2:
  "cast_fset1 xs ys \<Longrightarrow> cast_fset2 xs ys"
  apply (induct rule: cast_fset1.induct)
  apply (simp add: cast_fset2.intros(1))
  using cast_fset2.simps by auto

lemma cast_fset2_imp_1:
  "cast_fset2 xs ys \<Longrightarrow> cast_fset1 xs ys"
  apply (induct rule: cast_fset2.induct)
  apply (simp add: cast_fset1.intros(1))
  apply (rule cast_fset1.cases)

inductive cast_fset3 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset3 x (fimage cast_val_fun x)"
| "cast_fset3 (fimage cast_val_fun_inv y) y"

code_pred [show_modes] cast_fset3 .

print_theorems

value "cast_fset3 {|A, B|} {|C, D|}"

values "{x. cast_fset3 {|A, B|} x}"


inductive cast_fset4 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset4 {||} {||}"
| "cast_list xs ys \<Longrightarrow>
   cast_fset4 (fset_of_list xs) (fset_of_list ys)"

print_theorems

lemma q11 [code_pred_intro]:
  "cast_list (x#xs) ys \<Longrightarrow>
   cast_fset4 (fset_of_list (x#xs)) (fset_of_list ys)"
  using cast_fset4.intros(2) by blast

lemma q13:
  "\<not> List.member xs x \<Longrightarrow> distinct ys \<Longrightarrow> fset_of_list (x # xs) =
       fset_of_list xsa \<Longrightarrow>
       fset_of_list ys =
       fset_of_list ysa \<Longrightarrow>
       cast_list xsa ysa \<Longrightarrow>
       cast_list (x # xs) ys"

lemma q12:
  "cast_fset4 (fset_of_list (x#xs)) (fset_of_list ys) \<Longrightarrow>
   cast_list (x#xs) ys"
  apply (erule cast_fset4.cases)
  apply simp

lemma q12:
  "\<not> {||} = fset_of_list (x # xs)"
  by auto

lemma q13:
  "
        xa = fset_of_list (x # xs) \<Longrightarrow>
        xb = fset_of_list ys \<Longrightarrow>
        cast_list (x # xs) ys \<Longrightarrow>
        cast_fset4 xa xb"
  using cast_fset4.intros(2) by blast

lemma q15:
  "(Q \<Longrightarrow> P) \<Longrightarrow> (R \<Longrightarrow> Q) \<Longrightarrow> (R \<Longrightarrow> P)"

lemma q14:
  "
    (
        xa = fset_of_list (x # xs) \<Longrightarrow>
        xb = fset_of_list ys \<Longrightarrow>
        cast_list (x # xs) ys \<Longrightarrow>
        thesis) \<Longrightarrow>
    (cast_fset4 xa xb \<Longrightarrow> thesis)"
  apply (induct rule: cast_fset4.induct)

lemma q16:
  "cast_fset4 xa xb \<Longrightarrow>
    (\<And>x xs ys.
        xa = fset_of_list (x # xs) \<Longrightarrow>
        xb = fset_of_list ys \<Longrightarrow>
        cast_list (x # xs) ys)"

code_pred [show_modes] cast_fset4
  apply (induct rule: cast_fset4.induct)


lemma q12:
  "cast_fset1 xs ys \<Longrightarrow>
   cast_fset4 xs ys"
  apply (induct rule: cast_fset1.induct)
  apply (simp add: cast_fset4.intros(1))
  apply (rule cast_fset4.intros(2))

lemma q13:
  "cast_val x y \<Longrightarrow>
    cast_fset4 (fset_of_list xs)
     (fset_of_list ys) \<Longrightarrow>
    cast_fset4
     (finsert x (fset_of_list xs))
     (finsert y (fset_of_list ys))"

lemma q:
  "cast_val x y \<Longrightarrow>
   cast_fset4 (fset_of_list (xs)) (fset_of_list (ys)) \<Longrightarrow>
   cast_fset4 (fset_of_list (x#xs)) (fset_of_list (y#ys))"
  apply (simp)

lemma:
  "P x \<Longrightarrow> Q"

inductive cast_fset8 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset8 {||} {||}"
| "cast_val x y \<Longrightarrow> cast_fset8 (fset_of_list (xs)) (fset_of_list (ys)) \<Longrightarrow>
   cast_fset8 (fset_of_list (x#xs)) (fset_of_list (y#ys))"

code_pred [show_modes] cast_fset8 .

lemma [code_pred_intro]:
  "cast_val x y \<Longrightarrow> cast_fset4 (fset_of_list (xs)) (fset_of_list (ys)) \<Longrightarrow>
   cast_fset4 (fset_of_list (x#xs)) (fset_of_list (y#ys))"
  apply (induct xs arbitrary: x y ys)
  apply (metis cast_fset4.simps cast_list.intros(1) cast_list.intros(2) finsert_not_fempty fset_of_list_simps(1) fset_of_list_simps(2))


code_pred [show_modes] cast_fset4
  apply (induct rule: cast_fset4.induct)

print_theorems

values 15 "{x. cast_fset4 {|A, B|} x}"


inductive cast_fset5 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset5 {||} {||}"
| "cast_val x y \<Longrightarrow> x |\<notin>| xs \<Longrightarrow> y |\<notin>| ys \<Longrightarrow> cast_fset5 (xs |-| {|x|}) (ys |-| {|y|}) \<Longrightarrow>
   cast_fset5 xs ys"

lemma cast_fset4_code [code]:
  "cast_fset1 xs ys = cast_fset3 xs ys"

code_pred [show_modes] cast_fset5 .


(*values "{x. cast_fset5 {|A, B|} x}"*)

inductive cast_fset6 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset6 {||} {||}"
| "cast_val x y \<Longrightarrow> ffold (\<lambda>x s. finsert (cast_val_fun x) s) {||} xs = ys \<Longrightarrow>
   cast_fset6 xs ys"

code_pred [show_modes] cast_fset6 .

values "{x. cast_fset6 {|A, B|} x}"

inductive cast_fset7 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset7 {||} {||}"
| "fBall  cast_val x y \<Longrightarrow> ffold (\<lambda>x s. finsert (cast_val_fun x) s) xs = ys \<Longrightarrow>
   cast_fset7 xs ys"

code_pred [show_modes] cast_fset7 .

(*values "{x. cast_fset6 {|A, B|} x}"*)


(*
instantiation val1 :: linorder
begin

fun less_val1 :: "val1 \<Rightarrow> val1 \<Rightarrow> bool" where
  "less_val1 A B = True"
| "less_val1 _ _ = False"

fun less_eq_val1 :: "val1 \<Rightarrow> val1 \<Rightarrow> bool" where
  "less_eq_val1 A _ = True"
| "less_eq_val1 _ B = True"
| "less_eq_val1 _ _ = False"

instance
  apply intro_classes
  apply (metis less_eq_val1.elims(3) less_eq_val1.simps(3) less_val1.elims(2) less_val1.simps(1) val1.distinct(1))
  using less_eq_val1.elims(3) apply fastforce
  using less_eq_val1.elims(2) apply fastforce
  apply (metis less_eq_val1.elims(2))
  using less_eq_val1.elims(3) by blast

end

instantiation val2 :: linorder
begin

fun less_val2 :: "val2 \<Rightarrow> val2 \<Rightarrow> bool" where
  "less_val2 C D = True"
| "less_val2 _ _ = False"

fun less_eq_val2 :: "val2 \<Rightarrow> val2 \<Rightarrow> bool" where
  "less_eq_val2 C _ = True"
| "less_eq_val2 _ D = True"
| "less_eq_val2 _ _ = False"

instance
  apply intro_classes
  apply (metis less_eq_val2.elims(3) less_eq_val2.simps(3) less_val2.elims(2) less_val2.simps(1) val2.distinct(1))
  using less_eq_val2.elims(3) apply fastforce
  using less_eq_val2.elims(2) apply fastforce
  apply (metis less_eq_val2.elims(2))
  using less_eq_val2.elims(3) by blast

end

value "sorted_list_of_fset {|A, B|}"
*)



end
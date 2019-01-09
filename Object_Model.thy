(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Object Model\<close>
theory Object_Model
  imports OCL_Types "HOL-Library.Extended_Nat" "HOL-Library.Finite_Map"
begin

type_synonym 'a attrs = "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
type_synonym 'a assoc_end = "'a \<times> nat \<times> enat"
type_synonym 'a assocs = "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
type_synonym 'a model = "'a attrs \<times> 'a assocs"

definition assoc_end_class :: "'a assoc_end \<Rightarrow> 'a" where
  "assoc_end_class \<equiv> fst"

definition assoc_end_min :: "'a assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd"

definition assoc_end_max :: "'a assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd"

definition assoc_end_type :: "'a assoc_end \<Rightarrow> 'a type" where
  "assoc_end_type end \<equiv>
    let cls = assoc_end_class end in
    if assoc_end_max end \<le> 1 then
      if assoc_end_min end = 0
        then (ObjectType cls)[?]
        else (ObjectType cls)[1]
    else Set (ObjectType cls)[1]"

definition assoc_end_min_le_max :: "'a assoc_end \<Rightarrow> bool" where
  "assoc_end_min_le_max end \<equiv> assoc_end_min end \<le> assoc_end_max end"

definition assoc_refer_role :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_role ends role \<equiv> fmlookup ends role \<noteq> None"

(* from нужен для N-арных ассоциаций, в которых у исходного класса больше одной роли
   С другой стороны, не очень понятно зачем. Для определения типа не нужен,
   нужен для вычисления значения  *)

definition assoc_refer_class :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a \<Rightarrow> bool" where
  "assoc_refer_class ends cls \<equiv>
    fBex (fmdom ends) (\<lambda>role. assoc_end_class (the (fmlookup ends role)) = cls)"

definition find_assocs :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> 'a assocs" where
  "find_assocs assocs cls role \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class (fmdrop role ends) cls \<and> assoc_refer_role ends role) assocs"

definition find_assoc_end :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> 'a assoc_end option" where
  "find_assoc_end assocs cls role \<equiv>
    let found = fmran (find_assocs assocs cls role) in
    if fcard found = 1 then fmlookup (fthe_elem found) role else None"

(*
inductive find_association where
  "(*cls \<le> cls2 \<Longrightarrow>*)
   assoc \<in> fmdom' assocs \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   assoc_refer_class (fmdrop name ends) cls \<Longrightarrow>
   fmlookup ends name = Some end \<Longrightarrow>
   find_association (fmupd assoc ends assocs) cls name end"
*)

(*
lemma find_association_code [code_pred_intro]:
  "fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class (fmdrop name ends) cls \<and> assoc_refer_role ends name) assocs = a1 \<Longrightarrow>
   fmlookup a1 assoc = Some ends \<Longrightarrow>
   assoc_refer_class (fmdrop name ends) cls \<Longrightarrow>
   fmlookup ends name = Some end \<Longrightarrow>
   find_association assocs cls name end"
  by (metis (no_types, lifting) find_association.intros fmdom'_notD fmlookup_filter option.distinct(1))
*)

(*** Test Cases *************************************************************)

section \<open>Test Cases\<close>

definition "attrs1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (STR ''name'', String[1] :: classes1 type)]),
  (Employee, fmap_of_list [
    (STR ''name'', Integer[1] :: classes1 type),
    (STR ''position'', String[1])]),
  (Customer, fmap_of_list [
    (STR ''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (STR ''name'', String[1]),
    (STR ''cost'', Real[?])]),
  (Task, fmap_of_list [
    (STR ''description'', String[1])])]"
(*
lemma subclass1_code [code_pred_intro]:
  "(cls :: classes1) \<le> cls"
  "subclass1 cls cls2 \<Longrightarrow>
   cls \<le> cls2"
  by (simp_all add: less_classes1_def less_eq_classes1_def)
*)
(*
lemma find_attribute_code [code_pred_intro]:
  "fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs name = Some \<tau> \<Longrightarrow>
   find_attribute attrs cls name cls \<tau>"
  "subclass1 cls cls2 \<Longrightarrow>
   fmlookup attrs cls2 = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs name = Some \<tau> \<Longrightarrow>
   find_attribute attrs cls name cls2 \<tau>"
  by (simp_all add: find_attribute.intros less_classes1_def less_eq_classes1_def)
*)
(*
datatype ty = A | B | C

inductive lty where
  "lty A C"
| "lty B C"

instantiation ty :: order
begin

definition "(<) \<equiv> lty"
definition "x \<le> y \<equiv> x = y \<or> lty x y"

instance
  apply intro_classes
  using less_eq_ty_def less_ty_def lty.simps by auto

end

inductive pred1 where
  "x \<le> y \<Longrightarrow>
   pred1 x y"

lemma pred1_ty_code [code_pred_intro]:
  "x = y \<Longrightarrow>
   pred1 x y"
  "lty x y \<Longrightarrow>
   pred1 x y"
  by (simp_all add: less_eq_ty_def pred1.intros r_into_rtranclp)

code_pred [show_modes] pred1
  using less_eq_ty_def pred1.simps by blast

values "{x. pred1 A x}"


inductive pred2 where
  "pred1 x y \<Longrightarrow>
   pred2 x y"

(*
lemma pred2_ty_code [code_pred_intro]:
  "pred1 x y \<Longrightarrow>
   pred2 x y"
  by (simp_all add: pred1_ty_code pred2.intros)

code_pred [show_modes] pred2
  using pred2.cases by blast
*)
lemma pred2_ty_code [code_pred_intro]:
  "x = y \<Longrightarrow>
   pred2 x y"
  "lty x y \<Longrightarrow>
   pred2 x y"
  by (simp_all add: pred1_ty_code pred2.intros)

code_pred [show_modes] pred2
  using less_eq_ty_def pred1.cases pred2.simps by blast

values "{x. pred2 A x}"





datatype ty = A | B | C | D

inductive lty where
  "lty A C"
| "lty B C"
| "lty C D"

inductive_cases lty_x_A [elim!]: "lty x A"
inductive_cases lty_x_B [elim!]: "lty x B"
inductive_cases lty_x_C [elim!]: "lty x C"
inductive_cases lty_x_D [elim!]: "lty x D"

code_pred [show_modes] lty .

instantiation ty :: order
begin

definition "(<) \<equiv> lty\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> lty\<^sup>*\<^sup>*"

lemma ty_less_le_not_le:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)"
  for x y :: ty
  unfolding less_ty_def less_eq_ty_def
  apply auto
  apply (metis Nitpick.rtranclp_unfold lty.cases lty_x_A lty_x_B lty_x_C tranclp.cases tranclpD)
  by (metis rtranclpD)

instance
  apply intro_classes
  apply (simp add: ty_less_le_not_le)
  apply (simp add: less_eq_ty_def)
  apply (metis less_eq_ty_def rtranclp_trans)
  by (metis (mono_tags, lifting) less_eq_ty_def less_ty_def rtranclpD ty_less_le_not_le)

end

inductive pred1 where
  "x \<le> y \<Longrightarrow>
   pred1 x y"

inductive pred2 where
  "pred1 x y \<Longrightarrow>
   pred2 x y"

lemma pred1_ty_code [code_pred_intro]:
  "x = y \<Longrightarrow>
   pred1 x y"
  "lty x y \<Longrightarrow>
   pred1 x y"
  by (simp_all add: less_eq_ty_def pred1.intros r_into_rtranclp)

code_pred [show_modes] pred1
  apply (erule pred1.cases)
*)
(*
code_pred [show_modes] find_attribute
  by (metis find_attribute.cases less_classes1_def less_eq_classes1_def)
*)

inductive find_attribute where
  "cls \<le> cls2 \<Longrightarrow>
   fmlookup attrs cls2 = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs name = Some \<tau> \<Longrightarrow>
   find_attribute attrs cls name cls2 \<tau>"

code_pred [show_modes] find_attribute .

values "{(c, t). find_attribute attrs1 Employee (STR ''name'') c t}"
values "{(c, t). find_attribute attrs1 Employee (STR ''position'') c t}"
(*
inductive elems where
  "x |\<in>| xs \<Longrightarrow>
   elems xs x"

primrec elems_fun where
  "elems_fun "

term "set_of_pred"
term subclass1_i_o
value "set_of_pred (subclass1_i_o Employee)"

code_pred [show_modes] elems .

values "{x. elems {|1::nat,2,3|} x}"

lemma find_assoc1_code [code_pred_intro]:
  "find_assoc1 assocs (fmdom assocs)"
*)

definition assocs1 :: "classes1 assocs" where
  "assocs1 \<equiv> fmap_of_list [
  (STR ''ProjectPerson'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, 5)),
    (STR ''person'', (Person, 0, 1))]),
  (STR ''ProjectManager'', fmap_of_list [
    (STR ''projects'', (Project, 0::nat, \<infinity>)),
    (STR ''manager'', (Employee, 1, 1))]),
  (STR ''ProjectMember'', fmap_of_list [
    (STR ''member_of'', (Project, 0, \<infinity>)),
    (STR ''members'', (Employee, 1, 20))]),
  (STR ''ManagerEmployee'', fmap_of_list [
    (STR ''line_manager'', (Employee, 0::nat, 1)),
    (STR ''project_manager'', (Employee, 0::nat, \<infinity>)),
    (STR ''employees'', (Employee, 3, 7))]),
  (STR ''ProjectCustomer'', fmap_of_list [
    (STR ''projects'', (Project, 0, \<infinity>)),
    (STR ''customer'', (Customer, 1, 1))]),
  (STR ''ProjectTask'', fmap_of_list [
    (STR ''project'', (Project, 1, 1)),
    (STR ''tasks'', (Task, 0, \<infinity>))]),
  (STR ''SprintTaskAssignee'', fmap_of_list [
    (STR ''sprint'', (Sprint, 0, 10)),
    (STR ''tasks'', (Task, 0, 5)),
    (STR ''assignee'', (Employee, 0, 1))])]"

lemma fmember_code_predI [code_pred_intro]:
  "Predicate_Compile.contains (fset xs) x \<Longrightarrow> x |\<in>| xs"
  by (meson Predicate_Compile.containsE notin_fset)

code_pred [show_modes] fmember
  by (simp add: Predicate_Compile.containsI fmember.rep_eq)

value "{x. x \<in> fmdom' assocs1}"
values "{x. x |\<in>| fmdom assocs1}"
(*
inductive find_assoc where
  "a |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs a = Some assoc \<Longrightarrow>
   fmlookup assoc name = Some end \<Longrightarrow>
   find_assoc assocs cls name end"

code_pred [show_modes] find_assoc .
*)
(*
definition "fset_of_assocs assocs \<equiv>
  ffold (\<lambda>(a, r, e) y. ffold (\<lambda>x z. finsert (a, r, x) z) fempty e) fempty
    (fset_of_fmap (fmmap_keys (\<lambda>k v. (k, fset_of_fmap v)) assocs))"
*)
(*
definition "sorted_list_of_assocs assocs \<equiv>
  concat (fold (\<lambda>(a, r) y. (fold (\<lambda>x z. (a, x) # z) r []) # y)
    (sorted_list_of_fmap (fmmap sorted_list_of_fmap assocs)) [])"
*)
(*
primrec product_lists :: "'a list list \<Rightarrow> 'a list list" where
"product_lists [] = [[]]" |
"product_lists (xs # xss) = concat (map (\<lambda>x. map (Cons x) (product_lists xss)) xs)"
*)
(*
value "sorted_list_of_fmap (fmmap (\<lambda>xm. map (\<lambda>x. fmdrop x xm) (sorted_list_of_fset (fmdom xm))) assocs)"
term map

value "(sorted_list_of_fmap (fmmap (\<lambda>xm. map (\<lambda>x. sorted_list_of_fmap (fmdrop x xm)) (sorted_list_of_fset (fmdom xm))) assocs1))"

type_synonym 'a binary_assoc = "assoc \<times> role \<times> 'a assoc_end \<times> role \<times> 'a assoc_end"

definition "from_role \<equiv> fst \<circ> snd"
definition "from_assoc_end \<equiv> fst \<circ> snd \<circ> snd"
definition "to_role \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "to_assoc_end \<equiv> snd \<circ> snd \<circ> snd \<circ> snd"

definition sorted_list_of_assocs :: "'a assocs \<Rightarrow> 'a binary_assoc list" where
  "sorted_list_of_assocs assocs \<equiv> concat (concat (
    map (\<lambda>(assoc, roles).
      map (\<lambda>(from, ends).
        map (\<lambda>end. (assoc, end)) ends) roles)
      (sorted_list_of_fmap (fmmap (\<lambda>xm.
        (sorted_list_of_fmap (fmmap_keys (\<lambda>x v. map (\<lambda>y. (x, v, y))
          (sorted_list_of_fmap (fmdrop x xm))) xm))) assocs))))"

definition "roles xs \<equiv> map (\<lambda>assoc. (assoc_end_class (from_assoc_end assoc), assoc)) xs"

value "roles (sorted_list_of_assocs assocs1)"
value "sorted_list_of_assocs assocs1"
*)
(*
definition "sorted_list_of_assocs assocs \<equiv>
   (fold (\<lambda>(a, r) y. y @ [fold (\<lambda>(x, y) z. z @ [(a, y)]) r []])
    (sorted_list_of_fmap (fmmap (\<lambda>xm.
      sorted_list_of_fmap (fmmap_keys (\<lambda>x v. map (\<lambda>y. (x, v, y)) (sorted_list_of_fmap (fmdrop x xm)))
          xm))
      assocs)) [])"

definition "sorted_list_of_assocs assocs \<equiv>
   (fold (\<lambda>(a, r) y. y @ [fold (\<lambda>x z. z @ [(a, x)]) r []])
    (sorted_list_of_fmap (fmmap (\<lambda>xm.
      map (\<lambda>x. map (\<lambda>y. (x, y)) (sorted_list_of_fmap (fmdrop x xm)))
          (sorted_list_of_fset (fmdom xm)))
      assocs)) [])"
*)
(*
value "let x = fmap_of_list [
    (STR ''manages'', (Project, 0::nat, 2::nat)),
    (STR ''manager'', (Employee, 1, 1))] in
  map (\<lambda>x. (x, fmdrop x xm)) (sorted_list_of_fset (fmdom xm))"

term "fmdrop"

value "fmmap sorted_list_of_fmap assocs1"

definition "sorted_list_of_assocs assocs \<equiv>
   (fold (\<lambda>(a, r) y. y @ [fold (\<lambda>x z. z @ [(a, x)]) r []])
    (sorted_list_of_fmap (fmmap sorted_list_of_fmap assocs)) [])"

value "assocs1"

term fmmap
term "(fmmap_keys (\<lambda>k v. (k, sorted_list_of_fmap v)) assocs1)"
term "(sorted_list_of_fmap (fmmap_keys (\<lambda>k v. (sorted_list_of_fmap v)) assocs1))"

value "[[1::nat,2],[3,4,5],[6,7]]"
(*
value "fold (\<lambda>x y. product_lists [y,y]) [[1::nat,2],[3,4,5],[6,7]] ([] :: nat list)"
*)
value "product [[1::nat,2],[3,4,5],[6,7]]"
term "product"
value "subseqs [1::nat, 2, 3]"
value "product_lists [[1::nat,2,3],[4,5,6]]"
value "product_lists [[1::nat,2],[3,4,5],[6,7]]"
value "List.n_lists 3 [1::nat,2,3]"

(*
primrec n_lists :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"n_lists 0 xs = [[]]" |
"n_lists (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) xs) (n_lists n xs))"
*)
(*
primrec n_lists :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
"n_lists 0 xs = [[]]" |
"n_lists (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) xs) (n_lists n xs))"
*)
term filter
value "n_lists 2 [1::nat,2,3]"
value "shuffle [1::nat,2] [3,4]"

primrec perm :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "perm xs [] = [xs]"
| "perm xs (y # ys) = (perm (y # xs) ys)"

value "perm ([] :: nat list) [1::nat,2,3]"

term "fold (\<lambda>x y. y) [[1::nat,2],[3,4,5],[6,7]] []"
value "fold (\<lambda>x y. fold (\<lambda>p q. (x, p) # q) x []) [[1::nat,2],[3,4,5],[6,7]] []"

term "(fold (\<lambda>(a, r, e) y. (fold (\<lambda>x z. (a, r, x) # z) e []) # y)
    (sorted_list_of_fmap (fmmap_keys (\<lambda>k v. (k, sorted_list_of_fmap v)) assocs1)) [])"

term "sorted_list_of_assocs assocs1"
term sorted_list_of_fmap
term prod

value "sorted_list_of_assocs assocs1"

term "ffold (\<lambda>(a, r, e) y. ffold (\<lambda>x z. finsert (a, r, x) z) fempty e) fempty
  (fset_of_fmap (fmmap_keys (\<lambda>k v. (k, fset_of_fmap v)) assocs1))"

term "fset_of_fmap (fmmap_keys (\<lambda>k v. (k, fset_of_fmap v)) assocs1)"
*)
(*
inductive find_assoc where
  "a |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs a = Some assoc \<Longrightarrow>
   fmlookup assoc name = Some end \<Longrightarrow>
   find_assoc assocs cls name end"
*)
(*
inductive find_association where
  "cls \<le> cls2 \<Longrightarrow>
   find_assoc_end assocs cls2 name = Some end \<Longrightarrow>
   find_association assocs cls name cls2 end"

lemma find_association_code [code_pred_intro]:
  "find_assoc_end assocs cls name = Some end \<Longrightarrow>
   find_association assocs cls name cls end"
  "subclass1 cls cls2 \<Longrightarrow>
   find_assoc_end assocs cls2 name = Some end \<Longrightarrow>
   find_association assocs cls name cls2 end"
  by (simp_all add: find_association.intros less_eq_classes1_def less_classes1_def)

code_pred [show_modes] find_association
  by (metis find_association.cases less_classes1_def less_eq_classes1_def)
*)

(*
definition find_assocs :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> 'a assocs" where
  "find_assocs assocs cls role \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class (fmdrop role ends) cls \<and> assoc_refer_role ends role) assocs"

definition find_assoc_end :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> 'a assoc_end option" where
  "find_assoc_end assocs cls role \<equiv>
    let found = fmran (find_assocs assocs cls role) in
    if fcard found = 1 then fmlookup (fthe_elem found) role else None"
*)

inductive find_association where
  "cls \<le> cls2 \<Longrightarrow>
   assoc_name |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc_name = Some assoc \<Longrightarrow>
   fmlookup assoc name = Some end \<Longrightarrow>
(*   find_assoc_end assocs cls2 name = Some end \<Longrightarrow>*)
   find_association assocs cls name cls2 end"

code_pred [show_modes] find_association .

values "{(c, e). find_association assocs1 Employee STR ''projects'' c e}"
values "{(c, e). find_association assocs1 Customer STR ''projects'' c e}"
values "{(c, e). find_association assocs1 Project STR ''manager1'' c e}"

value "find_assocs assocs1 Project STR ''manager''"
value "find_assocs assocs1 Employee STR ''tasks''"
value "find_assoc_end assocs1 Project STR ''manager''"
value "find_assoc_end assocs1 Employee STR ''tasks''"

value "find_assocs assocs1 Project STR ''manager1''"
value "find_assoc_end assocs1 Project STR ''manager1''"







definition "model1 \<equiv> (attrs1, assocs1)"

subsection \<open>Positive Cases\<close>

value "find_assocs assocs1 Project STR ''manager''"
value "find_assocs assocs1 Employee STR ''tasks''"
value "find_assoc_end assocs1 Project STR ''manager''"
value "find_assoc_end assocs1 Employee STR ''tasks''"

subsection \<open>Negative Cases\<close>

value "find_assocs assocs1 Project STR ''manager1''"
value "find_assoc_end assocs1 Project STR ''manager1''"

end

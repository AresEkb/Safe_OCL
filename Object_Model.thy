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

inductive find_attribute where
  "cls \<le> cls2 \<Longrightarrow>
   fmlookup attrs cls2 = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs name = Some \<tau> \<Longrightarrow>
   find_attribute attrs cls name cls2 \<tau>"

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

inductive q where
  "q (fmupd a b xs) a"

code_pred [show_modes] q .


term "fset_of_fmap (a :: 'a assocs)"

term fset_of_fmap


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

lemma find_attribute_code [code_pred_intro]:
  "fmlookup attrs cls2 = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs name = Some \<tau> \<Longrightarrow>
   cls = cls2 \<Longrightarrow>
   find_attribute attrs cls name cls2 \<tau>"
  "fmlookup attrs cls2 = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs name = Some \<tau> \<Longrightarrow>
   subclass1 cls cls2 \<Longrightarrow>
   find_attribute attrs cls name cls2 \<tau>"
  by (simp_all add: find_attribute.intros dual_order.strict_implies_order less_classes1_def)

code_pred [show_modes] find_attribute
  by (metis find_attribute.cases le_neq_trans less_classes1_def)

values "{(c, t). find_attribute attrs1 Employee (STR ''name'') c t}"
values "{(c, t). find_attribute attrs1 Employee (STR ''position'') c t}"

definition assocs1 :: "classes1 assocs" where
  "assocs1 \<equiv> fmap_of_list [
  (STR ''ProjectManager'', fmap_of_list [
    (STR ''manages'', (Project, 0::nat, \<infinity>)),
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

term ffold
term finsert

definition "fset_of_assocs assocs \<equiv>
  ffold (\<lambda>(a, r, e) y. ffold (\<lambda>x z. finsert (a, r, x) z) fempty e) fempty
    (fset_of_fmap (fmmap_keys (\<lambda>k v. (k, fset_of_fmap v)) assocs))"
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
    (sorted_list_of_fmap (fmmap
      (\<lambda>xm. sorted_list_of_fmap (fmmap_keys
        (\<lambda>x v. map (\<lambda>y. (x, v, y)) (sorted_list_of_fmap (fmdrop x xm))) xm))
      assocs))))"

definition "roles xs \<equiv> map (\<lambda>assoc. (assoc_end_class (from_assoc_end assoc), assoc)) xs"

value "roles (sorted_list_of_assocs assocs1)"
value "sorted_list_of_assocs assocs1"

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

value "fold (\<lambda>x y. product_lists [y,y]) [[1::nat,2],[3,4,5],[6,7]] ([] :: nat list)"

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
primrec n_lists :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
"n_lists 0 xs = [[]]" |
"n_lists (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) xs) (n_lists n xs))"

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





inductive find_association where
  "(*cls \<le> cls2 \<Longrightarrow>*)
   (*find_assocs assocs cls name = a1 \<Longrightarrow>*)
   fset_of_fmap assocs = a1 \<Longrightarrow>
   (*assoc_refer_class (fmdrop name ends) cls \<Longrightarrow>
   fmlookup ends name = Some end \<Longrightarrow>
   assocs = (fmupd assoc ends assocs2) \<Longrightarrow>*)
   find_association assocs cls name a1"

code_pred [show_modes] find_association .

values "{x. find_association assocs1 Project ''manager'' x}"
values "{x. find_association assocs1 Project ''manager1'' x}"

value "find_assocs assocs1 Project ''manager''"
value "find_assocs assocs1 Employee ''tasks''"
value "find_assoc_end assocs1 Project ''manager''"
value "find_assoc_end assocs1 Employee ''tasks''"

value "find_assocs assocs1 Project ''manager1''"
value "find_assoc_end assocs1 Project ''manager1''"







definition "model1 \<equiv> (attrs1, assocs1)"

subsection \<open>Positive Cases\<close>

value "find_assocs assocs1 Project ''manager''"
value "find_assocs assocs1 Employee ''tasks''"
value "find_assoc_end assocs1 Project ''manager''"
value "find_assoc_end assocs1 Employee ''tasks''"

subsection \<open>Negative Cases\<close>

value "find_assocs assocs1 Project ''manager1''"
value "find_assoc_end assocs1 Project ''manager1''"

end

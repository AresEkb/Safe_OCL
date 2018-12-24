(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* Object Model *}
theory Object_Model
  imports OCL_Types "HOL-Library.Extended_Nat" "HOL-Library.Finite_Map"
begin

type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)
(*
definition denorm :: "('a \<rightharpoonup>\<^sub>f 'b) \<Rightarrow> ('a \<times> 'b) fset" where
  "denorm m \<equiv> (\<lambda> k. (k, the (fmlookup m k))) |`| fmdom m"

definition flatten :: "('a \<times> 'b fset) fset \<Rightarrow> ('a \<times> 'b) fset" where
  "flatten s \<equiv> ffUnion ((\<lambda>(x,y). (\<lambda>z. (x,z)) |`| y) |`| s)"

definition denorm3 :: "('a \<rightharpoonup>\<^sub>f 'b \<rightharpoonup>\<^sub>f 'c) \<Rightarrow> ('a \<times> 'b \<times> 'c) fset" where
  "denorm3 m \<equiv> flatten ((\<lambda>k. (k, denorm (the (fmlookup m k)))) |`| fmdom m)"
*)

(*type_synonym cls = "string"*)
type_synonym attr = "string"
type_synonym assoc = "string"
type_synonym role = "string"
type_synonym oid = "string"

(*type_synonym 'a class_set = "'a fset"*)
type_synonym 'a attrs = "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 'a type"
type_synonym 'a assoc_end = "'a \<times> nat \<times> enat"
type_synonym 'a assocs = "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
type_synonym 'a model = "'a attrs \<times> 'a assocs"

definition assoc_end_class :: "'a assoc_end \<Rightarrow> 'a" where
  "assoc_end_class \<equiv> fst"
(*
definition assoc_end_role :: "assoc_end \<Rightarrow> role" where
  "assoc_end_role \<equiv> fst \<circ> snd"

definition assoc_end_min :: "assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd \<circ> snd"

definition assoc_end_max :: "assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd \<circ> snd"
*)
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

definition assoc_classes :: "'a assoc_end list \<Rightarrow> 'a fset" where
  "assoc_classes \<equiv> fset_of_list \<circ> (map assoc_end_class)"

definition associates :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a fset" where
  "associates ends \<equiv>  assoc_end_class |`| fmran ends"
(*
definition find_assocs :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs assocs cls \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of Some ends \<Rightarrow>
      cls |\<in>| associates ends) assocs"
*)

definition assoc_refer_class :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a \<Rightarrow> bool" where
  "assoc_refer_class ends cls \<equiv>
    fBex (fmdom ends) (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end)"

definition find_assocs :: "'a assocs \<Rightarrow> 'a \<Rightarrow> 'a assocs" where
  "find_assocs assocs cls \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      assoc_refer_class ends cls) assocs"

definition participating :: "'a assocs \<Rightarrow> 'a \<Rightarrow> assoc fset" where
  "participating assocs cls \<equiv> fmdom (find_assocs assocs cls)"
(*
term "fmran (find_assocs assocs1 cls1)"
definition find_assoc_end :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end" where
  "find_assoc_end assocs cls role \<equiv> fmran (find_assocs assocs cls)"
*)
(*
definition find_assocs2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs2 assocs cls role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls) (find_assocs assocs cls))"
*)
definition find_assocs2 :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs2 assocs cls role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      (case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls)) (find_assocs assocs cls))"
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc" where
  "find_assoc assocs cls role \<equiv> fthe_elem (find_assocs2 assocs cls role)"
*)


definition assoc_refer_class2 :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a \<Rightarrow> nat" where
  "assoc_refer_class2 ends cls \<equiv>
    fcard (fmdom (fmfilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end) ends))"

definition assoc_refer_class3 :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a \<Rightarrow> (role \<rightharpoonup>\<^sub>f 'a assoc_end)" where
  "assoc_refer_class3 ends cls \<equiv>
    fmfilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls \<noteq> assoc_end_class end) ends"

definition q :: "'a \<Rightarrow> (role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f 'a assoc_end)" where
  "q cls ends \<equiv> case assoc_refer_class2 ends cls
      of 0 \<Rightarrow> fmempty
       | (Suc 0) \<Rightarrow> assoc_refer_class3 ends cls
       | (Suc (Suc 0)) \<Rightarrow> ends"

(* Example *)

(*definition classes1 :: "'a fset" where
  "classes1 \<equiv> {|''Person'',''Car'',''Company''|}"*)

definition "attrs1 \<equiv> fmap_of_list [
  (Person, fmap_of_list [
    (''name'', String[1] :: classes1 type)]),
  (Employee, fmap_of_list [
    (''position'', String[1])]),
  (Customer, fmap_of_list [
    (''vip'', Boolean[1])]),
  (Project, fmap_of_list [
    (''name'', String[1]),
    (''cost'', Real[?])]),
  (Task, fmap_of_list [
    (''description'', String[1])])]"

definition assocs1 :: "classes1 assocs" where
  "assocs1 \<equiv> fmap_of_list [
  (''ProjectManager'', fmap_of_list [
    (''manages'', (Project, 0::nat, \<infinity>)),
    (''manager'', (Employee, 1, 1))]),
  (''ProjectMember'', fmap_of_list [
    (''member_of'', (Project, 0, \<infinity>)),
    (''members'', (Employee, 1, 20))]),
  (''ManagerEmployee'', fmap_of_list [
    (''manager'', (Employee, 0::nat, 1)),
    (''employees'', (Employee, 0, \<infinity>))]),
  (''ProjectCustomer'', fmap_of_list [
    (''projects'', (Project, 0, \<infinity>)),
    (''customer'', (Customer, 1, 1))]),
  (''ProjectTask'', fmap_of_list [
    (''project'', (Project, 1, 1)),
    (''tasks'', (Task, 0, \<infinity>))]),
  (''SprintTaskAssignee'', fmap_of_list [
    (''sprint'', (Sprint, 0, \<infinity>)),
    (''tasks'', (Task, 0, \<infinity>)),
    (''assignee'', (Employee, 0, 1))])]"

(* TODO: Уточнить множественность для N-арных ассоциаций *)

definition "model1 \<equiv> (attrs1, assocs1)"


definition find_assocs3 :: "'a assocs \<Rightarrow> 'a \<Rightarrow> 'a assocs" where
  "find_assocs3 assocs cls \<equiv> fmmap (q cls) assocs"

definition find_assocs4 :: "'a assocs \<Rightarrow> role \<Rightarrow> 'a assocs" where
  "find_assocs4 assocs role \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        (case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> True)) assocs"

definition assoc_refer_class5 :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_class5 ends cls role \<equiv>
    case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
      cls = assoc_end_class end"
(*
definition assoc_refer_class5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_class5 ends cls role \<equiv>
    (map_option assoc_end_class \<circ> fmlookup ends) role = Some cls"
*)
definition assoc_refer_role5 :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_role5 ends role \<equiv> fmlookup ends role \<noteq> None"

(* from нужен для N-арных ассоциаций, в которых у исходного класса больше одной роли
   С другой стороны, не очень понятно зачем  *)
definition find_assocs5 :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> role \<Rightarrow> 'a assocs" where
  "find_assocs5 assocs cls from to \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class5 ends cls from \<and> assoc_refer_role5 ends to) assocs"

definition assoc_refer_class7 :: "(role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> 'a \<Rightarrow> bool" where
  "assoc_refer_class7 ends cls \<equiv>
    fBex (fmdom ends) (\<lambda>role. assoc_end_class (the (fmlookup ends role)) = cls)"

(* TODO: remove from argument *)
definition find_assocs7 :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> role \<Rightarrow> 'a assocs" where
  "find_assocs7 assocs cls from to \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class7 (fmdrop to ends) cls \<and> assoc_refer_role5 ends to) assocs"

definition find_assoc_end :: "'a assocs \<Rightarrow> 'a \<Rightarrow> role \<Rightarrow> 'a assoc_end option" where
  "find_assoc_end assocs cls role \<equiv>
    let found = fmran (find_assocs7 assocs cls '''' role) in
    if fcard found = 1 then fmlookup (fthe_elem found) role else None"
(*
definition find_assocs4 :: "assocs \<Rightarrow> cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "find_assocs4 assocs cls \<equiv> ffold fmadd fmempty (fmran (find_assocs3 assocs cls))"
*)
value "find_assocs7 assocs1 Project ''projects'' ''manager''"
value "find_assocs7 assocs1 Project ''projects'' ''manager1''"
value "find_assocs7 assocs1 Employee ''assignee'' ''tasks''"

value "find_assoc_end assocs1 Project ''manager''"
value "find_assoc_end assocs1 Project ''manager1''"
value "find_assoc_end assocs1 Employee ''tasks''"
(*
value "fmadd
  (fmap_of_list [(1::nat,2::nat)])
  (fmap_of_list [(2::nat,3::nat)])"

value "ffold fmadd fmempty {|
  fmap_of_list [(1::nat,2::nat)],
  fmap_of_list [(2::nat,3::nat)]|}"
*)

term fmmap
term fmfilter
(*
definition find_assocs3 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs3 assocs cls role \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls) (fmdom (find_assocs assocs cls))"
*)

(*
definition navends :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role fset" where
  "navends ends cls \<equiv> fmfilter (\<lambda>role.
    case fmlookup ends role of Some end \<Rightarrow>
      ) ends"
*)

(*
primrec findnn :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat option" where
  "findnn _ [] _ = None"
| "findnn P (x#xs) n = (if P x then Some n else findnn P xs (n+1))"

definition findn :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "findn P xs \<equiv> findnn P xs 0"

definition find_assoc_end :: "assoc_end list \<Rightarrow> role \<Rightarrow> nat option" where
  "find_assoc_end ends role \<equiv> findn (\<lambda>x. assoc_end_role x = role) ends"
*)
(*
definition find_assoc_end :: "assoc_end list \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc_end ends role \<equiv> find (\<lambda>x. assoc_end_role x = role) ends"

definition assoc_roles_distinct :: "assoc_end list \<Rightarrow> bool" where
  "assoc_roles_distinct \<equiv> distinct \<circ> (map assoc_end_role)"

definition assoc_is_ok :: "assoc_end list \<Rightarrow> bool" where
  "assoc_is_ok assoc \<equiv> assoc_roles_distinct assoc \<and> list_all assoc_end_min_le_max assoc"
*)


(*
definition assoc_is_ok2 :: "class_set \<Rightarrow> assoc_end \<Rightarrow> bool" where
  "assoc_is_ok2 classes end \<equiv> assoc_end_class end |\<in>| classes \<and> assoc_end_min_le_max end"

definition assoc_is_ok :: "class_set \<Rightarrow> (role \<rightharpoonup>\<^sub>f 'a assoc_end) \<Rightarrow> bool" where
  "assoc_is_ok classes role \<equiv> fBall (fmran role) (assoc_is_ok2 classes)"

inductive model_is_ok :: "'a model \<Rightarrow> bool" where
  "\<comment> \<open>Attributes defined for existing classes\<close>
   fmdom attrs |\<subseteq>| classes \<Longrightarrow>
   \<comment> \<open>Associations defined for existing classes\<close>
   (*fBall (fmran assocs) (\<lambda>x. assoc_classes x |\<subseteq>| classes) \<Longrightarrow>*)
   \<comment> \<open>Associations defined for existing classes and min \<le> max\<close>
   fBall (fmran assocs) (assoc_is_ok classes) \<Longrightarrow>
   (* TODO: Unique names in full descriptor *)
   model_is_ok (classes, attrs, assocs)"

code_pred [show_modes] model_is_ok .
*)
end

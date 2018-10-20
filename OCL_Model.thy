theory OCL_Model
  imports
    Main
    OCL_Common
    OCL_Types
    "~~/src/HOL/Library/Extended_Nat"
    "~~/src/HOL/Library/FSet"
    "~~/src/HOL/Library/Finite_Map"
begin

type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)

definition denorm :: "('a \<rightharpoonup>\<^sub>f 'b) \<Rightarrow> ('a \<times> 'b) fset" where
  "denorm m \<equiv> (\<lambda> k. (k, the (fmlookup m k))) |`| fmdom m"

definition flatten :: "('a \<times> 'b fset) fset \<Rightarrow> ('a \<times> 'b) fset" where
  "flatten s \<equiv> ffUnion ((\<lambda>(x,y). (\<lambda>z. (x,z)) |`| y) |`| s)"

definition denorm3 :: "('a \<rightharpoonup>\<^sub>f 'b \<rightharpoonup>\<^sub>f 'c) \<Rightarrow> ('a \<times> 'b \<times> 'c) fset" where
  "denorm3 m \<equiv> flatten ((\<lambda>k. (k, denorm (the (fmlookup m k)))) |`| fmdom m)"


type_synonym class_set = "cls fset"
type_synonym attrs = "cls \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f type"
(*type_synonym assoc_end = "cls \<times> role \<times> nat \<times> enat"*)
type_synonym assoc_end = "cls \<times> nat \<times> enat"
(* Плюс такого представления ещё и в том, что имена ролей уникальные *)
type_synonym assocs = "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f assoc_end"
type_synonym model = "class_set \<times> attrs \<times> assocs"

definition assoc_end_class :: "assoc_end \<Rightarrow> cls" where
  "assoc_end_class \<equiv> fst"
(*
definition assoc_end_role :: "assoc_end \<Rightarrow> role" where
  "assoc_end_role \<equiv> fst \<circ> snd"

definition assoc_end_min :: "assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd \<circ> snd"

definition assoc_end_max :: "assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd \<circ> snd"
*)
definition assoc_end_min :: "assoc_end \<Rightarrow> nat" where
  "assoc_end_min \<equiv> fst \<circ> snd"

definition assoc_end_max :: "assoc_end \<Rightarrow> enat" where
  "assoc_end_max \<equiv> snd \<circ> snd"

definition assoc_end_min_le_max :: "assoc_end \<Rightarrow> bool" where
  "assoc_end_min_le_max x \<equiv> assoc_end_min x \<le> assoc_end_max x"

definition assoc_classes :: "assoc_end list \<Rightarrow> cls fset" where
  "assoc_classes \<equiv> fset_of_list \<circ> (map assoc_end_class)"

definition associates :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls fset" where
  "associates ends \<equiv>  assoc_end_class |`| fmran ends"
(*
definition find_assocs :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs assocs cls \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of Some ends \<Rightarrow>
      cls |\<in>| associates ends) assocs"
*)

definition assoc_refer_class :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> bool" where
  "assoc_refer_class ends cls \<equiv>
    fBex (fmdom ends) (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end)"

definition find_assocs :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs assocs cls \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      assoc_refer_class ends cls) assocs"

definition participating :: "assocs \<Rightarrow> cls \<Rightarrow> assoc fset" where
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
definition find_assocs2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_assocs2 assocs cls role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        assoc_end_class end \<noteq> cls) (find_assocs assocs cls))"
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc" where
  "find_assoc assocs cls role \<equiv> fthe_elem (find_assocs2 assocs cls role)"
*)


definition assoc_refer_class2 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> nat" where
  "assoc_refer_class2 ends cls \<equiv>
    fcard (fmdom (fmfilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end) ends))"

definition assoc_refer_class3 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "assoc_refer_class3 ends cls \<equiv>
    fmfilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls \<noteq> assoc_end_class end) ends"

definition q :: "cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "q cls ends \<equiv> case assoc_refer_class2 ends cls
      of 0 \<Rightarrow> fmempty
       | (Suc 0) \<Rightarrow> assoc_refer_class3 ends cls
       | (Suc (Suc 0)) \<Rightarrow> ends"

(* Example *)

definition classes1 :: "cls fset" where
  "classes1 \<equiv> {|''Person'',''Car'',''Company''|}"

definition attrs1 :: "attrs" where
  "attrs1 = fmap_of_list [
    (''Person'', fmap_of_list [
      (''name'', String[1])]),
    (''Car'', fmap_of_list [
      (''color'', String[1])]),
    (''Company'', fmap_of_list [
      (''name'', String[?])])]"

definition assocs1 :: "assocs" where
  "assocs1 \<equiv> fmap_of_list [
    (''PersonCar'', fmap_of_list [
      (''driver'', (''Person'',1,1)),
      (''car'', (''Car'',1,3))]),
    (''Employment2'', fmap_of_list [
      (''employer'', (''Person'',0,1)),
      (''employee'', (''Person'',1,20))]),
    (''Employment'', fmap_of_list [
      (''company'', (''Company'',0,2)),
      (''employee'', (''Person'',1,\<infinity>))])]"

definition model1 :: "model" where
  "model1 \<equiv> (classes1, attrs1, assocs1)"


definition find_assocs3 :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs3 assocs cls \<equiv> fmmap (q cls) assocs"

definition find_assocs4 :: "assocs \<Rightarrow> role \<Rightarrow> assocs" where
  "find_assocs4 assocs role \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> True) assocs"

definition assoc_refer_class5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_class5 ends cls role \<equiv>
    case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
      cls = assoc_end_class end"
(*
definition assoc_refer_class5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_class5 ends cls role \<equiv>
    (map_option assoc_end_class \<circ> fmlookup ends) role = Some cls"
*)
definition assoc_refer_role5 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> role \<Rightarrow> bool" where
  "assoc_refer_role5 ends role \<equiv> fmlookup ends role \<noteq> None"

definition find_assocs5 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> role \<Rightarrow> assocs" where
  "find_assocs5 assocs cls from to \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        assoc_refer_class5 ends cls from \<and> assoc_refer_role5 ends to) assocs"
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc assocs cls role \<equiv>
    fmlookup (fthe_elem (fmran (find_assocs5 assocs cls role))) role"
*)
(*
definition find_assocs4 :: "assocs \<Rightarrow> cls \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end)" where
  "find_assocs4 assocs cls \<equiv> ffold fmadd fmempty (fmran (find_assocs3 assocs cls))"
*)
value "find_assocs5 assocs1 ''Person'' ''driver'' ''car''"
value "find_assocs5 assocs1 ''Person'' ''driver'' ''car1''"
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
definition assoc_is_ok2 :: "class_set \<Rightarrow> assoc_end \<Rightarrow> bool" where
  "assoc_is_ok2 classes end \<equiv> assoc_end_class end |\<in>| classes \<and> assoc_end_min_le_max end"

definition assoc_is_ok :: "class_set \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> bool" where
  "assoc_is_ok classes role \<equiv> fBall (fmran role) (assoc_is_ok2 classes)"

inductive model_is_ok :: "model \<Rightarrow> bool" where
  "(* Attributes defined for existing classes *)
   fmdom attrs |\<subseteq>| classes \<Longrightarrow>
   (* Associations defined for existing classes *)
   (*fBall (fmran assocs) (\<lambda>x. assoc_classes x |\<subseteq>| classes) \<Longrightarrow>*)
   (* Associations defined for existing classes and min \<le> max *)
   fBall (fmran assocs) (assoc_is_ok classes) \<Longrightarrow>
   (* TODO: Unique names in full descriptor *)
   model_is_ok (classes, attrs, assocs)"

code_pred [show_modes] model_is_ok .

end

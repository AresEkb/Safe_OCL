theory Assoc_Test
  imports "HOL-Library.Finite_Map"
begin

nonterminal fmaplets and fmaplet

syntax
  "_fmaplet"  :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /\<mapsto>\<^sub>f/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /[\<mapsto>\<^sub>f]/ _")
  ""          :: "fmaplet \<Rightarrow> fmaplets"              ("_")
  "_FMaplets" :: "[fmaplet, fmaplets] \<Rightarrow> fmaplets"  ("_,/ _")
  "_FMapUpd"  :: "['a \<rightharpoonup> 'b, fmaplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_FMap"     :: "fmaplets \<Rightarrow> 'a \<rightharpoonup> 'b"             ("(1[_])")

syntax (ASCII)
  "_fmaplet"  :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /|->f/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /[|->f]/ _")

translations
  "_FMapUpd m (_FMaplets xy ms)"      \<rightleftharpoons> "_FMapUpd (_FMapUpd m xy) ms"
  "_FMapUpd m (_fmaplet  x y)"        \<rightleftharpoons> "CONST fmupd x y m"
  "_FMap ms"                          \<rightleftharpoons> "_FMapUpd (CONST fmempty) ms"
  "_FMap (_FMaplets ms1 ms2)"         \<leftharpoondown> "_FMapUpd (_FMap ms1) ms2"
  "_FMaplets ms1 (_FMaplets ms2 ms3)" \<leftharpoondown> "_FMaplets (_FMaplets ms1 ms2) ms3"

datatype classes1 =
  Object | Person | Employee | Customer | Project | Task | Sprint

abbreviation "associations \<equiv> [
  STR ''ProjectManager'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0::nat, 100::nat),
    STR ''manager'' \<mapsto>\<^sub>f (Employee, 1, 1)],
  STR ''ProjectMember'' \<mapsto>\<^sub>f [
    STR ''member_of'' \<mapsto>\<^sub>f (Project, 0, 100),
    STR ''members'' \<mapsto>\<^sub>f (Employee, 1, 20)],
  STR ''ManagerEmployee'' \<mapsto>\<^sub>f [
    STR ''line_manager'' \<mapsto>\<^sub>f (Employee, 0, 1),
    STR ''project_manager'' \<mapsto>\<^sub>f (Employee, 0, 100),
    STR ''employees'' \<mapsto>\<^sub>f (Employee, 3, 7)],
  STR ''ProjectCustomer'' \<mapsto>\<^sub>f [
    STR ''projects'' \<mapsto>\<^sub>f (Project, 0, 100),
    STR ''customer'' \<mapsto>\<^sub>f (Customer, 1, 1)],
  STR ''ProjectTask'' \<mapsto>\<^sub>f [
    STR ''project'' \<mapsto>\<^sub>f (Project, 1, 1),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, 100)],
  STR ''SprintTaskAssignee'' \<mapsto>\<^sub>f [
    STR ''sprint'' \<mapsto>\<^sub>f (Sprint, 0, 10),
    STR ''tasks'' \<mapsto>\<^sub>f (Task, 0, 5),
    STR ''assignee'' \<mapsto>\<^sub>f (Employee, 0, 1)]]"

lemma fmember_code_predI [code_pred_intro]:
  "x |\<in>| xs" if "Predicate_Compile.contains (fset xs) x"
  using that by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

code_pred fmember
  by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

definition "assoc_end_class \<equiv> fst"

inductive assoc_refer_class where
  "role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = \<C> \<Longrightarrow>
   assoc_refer_class ends \<C> role"

code_pred [show_modes] assoc_refer_class .

inductive class_roles where
  "assoc |\<in>| fmdom assocs \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   assoc_refer_class ends \<C> from \<Longrightarrow>
   role |\<in>| fmdom ends \<Longrightarrow>
   (*fmlookup ends role = Some end \<Longrightarrow>*)
   role \<noteq> from \<Longrightarrow>
   class_roles assocs \<C> assoc from role"

code_pred [show_modes] class_roles .

values "{(x, y, z, a). class_roles associations x y z a}"


lemma fmupd_to_rhs:
  "fmupd k x xm = y \<longleftrightarrow> y = fmupd k x xm"
  by auto

lemma class_roles_unique:
  "class_roles associations Employee assoc1 from role \<Longrightarrow>
   class_roles associations Employee assoc2 from role \<Longrightarrow> assoc1 = assoc2"
  apply (erule class_roles.cases; erule class_roles.cases;
     erule assoc_refer_class.cases; erule assoc_refer_class.cases)
  unfolding fmupd_to_rhs
  apply (simp)
  apply (elim disjE)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  done

end

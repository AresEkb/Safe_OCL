theory OCLType
  imports
    Complex_Main
    "~~/src/HOL/Library/Extended_Nat"
    ProgLang
begin

(*** Kinds ******************************************************************************)

type_synonym cls = "string"
type_synonym attr = "string"
type_synonym assoc = "string"
type_synonym role = "string"
type_synonym oid = "string"

(*** Types ******************************************************************************)

datatype simple_type =
  OclAny
(*| OclInvalid*)
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType cls

(* TODO: Min and max occurs in collections *)
(* Зачем SupType? По спецификации вроде все типы соответствуют OclAny или нет? 
   В 11.2.1 написано, что OclAny - это супер-тип для всех остальных типов
   В A.2.6 Special Types написано, что OclAny не является супер-типом для коллекций

   OclVoid и OclInvalid являются подтипами и для коллекций тоже
   Хотя в A.2.5.1 для коллекций ничего не сказано про \<epsilon>
   Но в A.2.6 говорится, что всё таки это подтипы для всех типов и без оговорок
*)
(* Для упрощения можно запретить вложенные коллекции *)
datatype type =
  SupType
| OclVoid
| OclInvalid
| Required simple_type ("_[1]")
| Optional simple_type ("_[?]")
| Collection type
| Set type
| OrderedSet type
| Bag type
| Sequence type


term "Real[?]"
term "Real[1]"
(*
declare [[coercion "ST :: simple_type \<Rightarrow> type"]]
declare [[coercion "CT :: complex_type \<Rightarrow> type"]]
*)
(*
datatype type =
  OclAny
| OclVoid
| OclInvalid
| Boolean
| Real
| Integer
| UnlimitedNatural
| String
| ObjectType cls
| Collection type
| Set type
| OrderedSet type
| Bag type
| Sequence type
| SupType
*)

(*Tuple, Enum*)
(*
inductive less_type2 (infix "<:" 55) where
  "\<tau> \<noteq> OclAny \<Longrightarrow>
   \<nexists>\<sigma>. \<tau> = Collection \<sigma> \<Longrightarrow>
   \<nexists>\<sigma>. \<tau> = Set \<sigma> \<Longrightarrow>
   \<nexists>\<sigma>. \<tau> = OrderedSet \<sigma> \<Longrightarrow>
   \<nexists>\<sigma>. \<tau> = Bag \<sigma> \<Longrightarrow>
   \<nexists>\<sigma>. \<tau> = Sequence \<sigma> \<Longrightarrow>
   \<tau> <: OclAny"
| "\<tau> \<noteq> OclInvalid \<Longrightarrow>
   \<tau> \<noteq> OclVoid \<Longrightarrow>
   OclVoid <: \<tau>"
| "\<tau> \<noteq> OclInvalid \<Longrightarrow>
   OclInvalid <: \<tau>"
| "Integer <: Real"
| "UnlimitedNatural <: Integer"
| "UnlimitedNatural <: Real"
| "\<tau> <: \<sigma> \<Longrightarrow> Set \<tau> <: Collection \<sigma>"
| "\<tau> <: \<sigma> \<Longrightarrow> OrderedSet \<tau> <: Collection \<sigma>"
| "\<tau> <: \<sigma> \<Longrightarrow> Bag \<tau> <: Collection \<sigma>"
| "\<tau> <: \<sigma> \<Longrightarrow> Sequence \<tau> <: Collection \<sigma>"
(*| "(\<tau> :: type) < \<sigma> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> < \<rho>"*)

code_pred [show_modes] less_type2 .
*)
(*
inductive less_type2 (infix "<:" 55) where
  "\<tau> \<noteq> OclAny \<Longrightarrow>
   \<tau> \<noteq> Collection \<sigma> \<Longrightarrow>
   \<tau> \<noteq> Set \<sigma> \<Longrightarrow>
   \<tau> \<noteq> OrderedSet \<sigma> \<Longrightarrow>
   \<tau> \<noteq> Bag \<sigma> \<Longrightarrow>
   \<tau> \<noteq> Sequence \<sigma> \<Longrightarrow>
   \<tau> < OclAny"
| "\<tau> \<noteq> OclInvalid \<Longrightarrow>
   \<tau> \<noteq> OclVoid \<Longrightarrow>
   OclVoid < \<tau>"
| "\<tau> \<noteq> OclInvalid \<Longrightarrow>
   OclInvalid < \<tau>"
| "Integer < Real"
| "UnlimitedNatural < Integer"
| "UnlimitedNatural < Real"
| "\<tau> < \<sigma> \<Longrightarrow> Set \<tau> < Collection \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> OrderedSet \<tau> < Collection \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Bag \<tau> < Collection \<sigma>"
| "\<tau> < \<sigma> \<Longrightarrow> Sequence \<tau> < Collection \<sigma>"
(*| "(\<tau> :: type) < \<sigma> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> < \<rho>"*)
*)

(* Иерархия типов описана в A.2.7 Type Hierarchy *)

(* Верхняя полурешетка для простых типов *)

instantiation simple_type :: semilattice_sup
begin

(* Почему не индуктивное определение? *)
(*
function less_simple_type where
  "OclAny < \<tau> = False"
| "Boolean < \<tau> = (\<tau> = OclAny)"
| "Real < \<tau> = (\<tau> = OclAny)"
| "Integer < \<tau> = (\<tau> = Real \<or> \<tau> = OclAny)"
| "UnlimitedNatural < \<tau> = (\<tau> = Integer \<or> \<tau> = Real \<or> \<tau> = OclAny)"
| "String < \<tau> = (\<tau> = OclAny)"
| "ObjectType cls < \<tau> = (\<tau> = OclAny)"
  by pat_completeness auto
  termination by lexicographic_order
*)
fun less_simple_type where
  "OclAny < \<tau> = False"
(*| "OclInvalid < \<tau> = (\<tau> \<noteq> OclInvalid) "*)
| "Boolean < \<tau> = (\<tau> = OclAny)"
| "Real < \<tau> = (\<tau> = OclAny)"
| "Integer < \<tau> = (\<tau> = Real \<or> \<tau> = OclAny)"
| "UnlimitedNatural < \<tau> = (\<tau> = Integer \<or> \<tau> = Real \<or> \<tau> = OclAny)"
| "String < \<tau> = (\<tau> = OclAny)"
| "ObjectType cls < \<tau> = (\<tau> = OclAny)"

definition "\<tau> \<le> \<sigma> \<equiv> \<tau> = \<sigma> \<or> \<tau> < \<sigma>" for \<tau> \<sigma> :: simple_type

(* С таким определением удобно доказывать теоремы? *)

definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"

lemma less_le_not_le_simple_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: simple_type
  apply (rule iffI; auto simp add: less_eq_simple_type_def)
  apply (cases \<tau>; simp)
  apply (induct \<tau> arbitrary: \<sigma>; auto)
(*  using less_simple_type.elims(2) apply blast*)
  done

lemma order_refl_simple_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: simple_type
  by (simp add: less_eq_simple_type_def)

lemma order_trans_simple_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: simple_type
  apply (auto simp add: less_eq_simple_type_def)
  apply (erule notE)
  apply (induct \<tau> arbitrary: \<sigma> \<rho>; auto)
(*  using less_simple_type.elims(2) apply blast*)
  done

lemma antisym_simple_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: simple_type
  by (simp add: less_eq_simple_type_def; auto simp add: less_le_not_le_simple_type)

lemma sup_ge1_simple_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: simple_type
  by (induct \<tau>; simp add: less_eq_simple_type_def sup_simple_type_def)

lemma sup_commut_simple_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: simple_type
  by (simp add: sup_simple_type_def antisym_simple_type)

lemma sup_least_simple_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: simple_type
  by (induct \<tau>; induct \<sigma>; auto simp add: less_eq_simple_type_def sup_simple_type_def)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_simple_type)
  apply (simp)
  using order_trans_simple_type apply blast
  apply (simp add: antisym_simple_type)
  using less_eq_simple_type_def sup_ge1_simple_type sup_simple_type_def apply auto[1]
  using less_eq_simple_type_def sup_commut_simple_type sup_ge1_simple_type sup_simple_type_def apply auto[1]
  by (simp add: sup_least_simple_type)

end

inductive conforms_to (infix "<:" 50) where
Any_conforms_to_SupType: "\<tau> \<noteq> SupType \<Longrightarrow> \<tau> <: SupType"
|Void_conforms_to_Optional: "OclVoid <: Optional \<tau>"
|Invalid_conforms_to_Any: "\<tau> \<noteq> OclInvalid \<Longrightarrow> OclInvalid <: \<tau>"
|Required_conforms_to_Required: "\<tau> < \<sigma> \<Longrightarrow> Required \<tau> <: Required \<sigma>"
|Required_conforms_to_Optional: "\<tau> = \<sigma> \<or> \<tau> < \<sigma> \<Longrightarrow> Required \<tau> <: Optional \<sigma>"
|Optional_conforms_to_Optional: "\<tau> < \<sigma> \<Longrightarrow> Optional \<tau> <: Optional \<sigma>"
|Collection_conforms_to_Collection: "\<tau> <: \<sigma> \<Longrightarrow> Collection \<tau> <: Collection \<sigma>"
|Set_conforms_to_Set: "\<tau> <: \<sigma> \<Longrightarrow> Set \<tau> <: Set \<sigma>"
|OrderedSet_conforms_to_OrderedSet: "\<tau> <: \<sigma> \<Longrightarrow> OrderedSet \<tau> <: OrderedSet \<sigma>"
|Bag_conforms_to_Bag: "\<tau> <: \<sigma> \<Longrightarrow> Bag \<tau> <: Bag \<sigma>"
|Sequence_conforms_to_Sequence: "\<tau> <: \<sigma> \<Longrightarrow> Sequence \<tau> <: Sequence \<sigma>"
|Set_conforms_to_Collection: "\<tau> = \<sigma> \<or> \<tau> <: \<sigma> \<Longrightarrow> Set \<tau> <: Collection \<sigma>"
|OrderedSet_conforms_to_Collection: "\<tau> = \<sigma> \<or> \<tau> <: \<sigma> \<Longrightarrow> OrderedSet \<tau> <: Collection \<sigma>"
|Bag_conforms_to_Collection: "\<tau> = \<sigma> \<or> \<tau> <: \<sigma> \<Longrightarrow> Bag \<tau> <: Collection \<sigma>"
|Sequence_conforms_to_Collection: "\<tau> = \<sigma> \<or> \<tau> <: \<sigma> \<Longrightarrow> Sequence \<tau> <: Collection \<sigma>"

code_pred [show_modes] conforms_to .

inductive_cases less_sup_elim[elim!]: "\<tau> <: SupType"
inductive_cases sup_less_elim[elim!]: "SupType <: \<tau>"
inductive_cases void_less_elim[elim!]: "OclVoid <: \<tau>"
inductive_cases less_void_elim[elim!]: "\<tau> <: OclVoid"
inductive_cases invalid_less_elim[elim!]: "OclInvalid <: \<tau>"
inductive_cases less_invalid_elim[elim!]: "\<tau> <: OclInvalid"
inductive_cases required_less_required_elim[elim!]: "Required \<tau> <: Required \<sigma>"
inductive_cases required_less_elim[elim!]: "Required \<tau> <: \<sigma>"
inductive_cases less_required_elim[elim!]: "\<tau> <: Required \<sigma>"
inductive_cases required_less_optional_elim[elim!]: "Required \<tau> <: Optional \<sigma>"
inductive_cases optional_less_optional_elim[elim!]: "Optional \<tau> <: Optional \<sigma>"
inductive_cases optional_less_elim[elim!]: "Optional \<tau> <: \<sigma>"
inductive_cases less_optional_elim[elim!]: "\<tau> <: Optional \<sigma>"
inductive_cases collection_less_collection_elim[elim!]: "Collection \<tau> <: Collection \<sigma>"
inductive_cases collection_less_elim[elim!]: "Collection \<tau> <: \<sigma>"
inductive_cases less_collection_elim[elim!]: "\<tau> <: Collection \<sigma>"
inductive_cases set_less_set_elim[elim!]: "Set \<tau> <: Set \<sigma>"
inductive_cases set_less_elim[elim!]: "Set \<tau> <: \<sigma>"
inductive_cases less_set_elim[elim!]: "\<tau> <: Set \<sigma>"
inductive_cases ordered_set_less_ordered_set_elim[elim!]: "OrderedSet \<tau> <: OrderedSet \<sigma>"
inductive_cases ordered_set_less_elim[elim!]: "OrderedSet \<tau> <: \<sigma>"
inductive_cases less_ordered_set_elim[elim!]: "\<tau> <: OrderedSet \<sigma>"
inductive_cases bag_less_bag_elim[elim!]: "Bag \<tau> <: Bag \<sigma>"
inductive_cases bag_less_elim[elim!]: "Bag \<tau> <: \<sigma>"
inductive_cases less_bag_elim[elim!]: "\<tau> <: Bag \<sigma>"
inductive_cases sequence_less_sequence_elim[elim!]: "Sequence \<tau> <: Sequence \<sigma>"
inductive_cases sequence_less_elim[elim!]: "Sequence \<tau> <: \<sigma>"
inductive_cases less_sequence_elim[elim!]: "\<tau> <: Sequence \<sigma>"
thm collection_less_elim

thm required_less_required_elim required_less_elim less_required_elim

value "Set (Required Integer) <: Collection (Optional Real)"
(*
function max_type_code (infix "\<squnion>" 51) where
  "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OclVoid \<squnion> \<sigma> = (if \<sigma> = OclInvalid then OclVoid else \<sigma>)"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "SupType \<squnion> \<sigma> = SupType"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Required \<tau>
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Optional \<tau>
     | _ \<Rightarrow> SupType)"
  by pat_completeness auto
  termination by lexicographic_order
(*
lemma q:
  "max_type_code \<tau> \<sigma> = max_type_code \<sigma> \<tau>"
*)
no_notation max_type_code (infix "\<squnion>" 51)
*)
(*
inductive max_type :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"
  ("_ \<squnion> _ = _") where
(*  "\<sigma> \<squnion> \<tau> = \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> = (\<rho> :: type)"
|*)
  "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Set \<tau> \<squnion> Collection \<sigma> = Collection \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Set \<tau> \<squnion> Set \<sigma> = Set \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Set \<tau> \<squnion> OrderedSet \<sigma> = Collection \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Set \<tau> \<squnion> Bag \<sigma> = Collection \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Set \<tau> \<squnion> Sequence \<sigma> = Collection \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Required \<tau> \<squnion> Required \<sigma> = Required \<rho>"
| "\<tau> \<squnion> \<sigma> = \<rho> \<Longrightarrow> Required \<tau> \<squnion> Optional \<sigma> = Optional \<rho>"

no_notation max_type ("_ \<squnion> _ = _")

lemma max_type_impl:
  "max_type \<tau> \<sigma> \<rho> \<Longrightarrow> max_type_code \<tau> \<sigma> = \<rho>"
  apply (induct rule: max_type.induct)

  done


code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as max_type_eval) max_type .
value "max_type_eval (Set (Required (Real))) (Set (Required (Real)))"
*)
(*| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OclVoid \<squnion> \<sigma> = (if \<sigma> = OclInvalid then OclVoid else \<sigma>)"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "SupType \<squnion> \<sigma> = SupType"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Required \<tau>
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Optional \<tau>
     | _ \<Rightarrow> SupType)"
*)


(* Дальше идет очень длинное доказательство того, что вся система типов OCL
   включая коллекции и опциональные типы образует верхнюю полурешетку.
   Было бы не плохо её нарисовать. Ещё как-то обосновать ввод SupType *)

instantiation type :: semilattice_sup
begin

definition less_type where "less_type \<equiv> conforms_to"
(*
function less_type where
  "SupType < \<tau> = False"
| "OclVoid < \<tau> = (\<tau> \<noteq> OclInvalid \<and> \<tau> \<noteq> OclVoid)"
| "OclInvalid < \<tau> = (\<tau> \<noteq> OclInvalid)"
| "Required \<tau> < \<sigma> = (case \<sigma> of Required \<rho> \<Rightarrow> \<tau> < \<rho> | Optional \<rho> \<Rightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
| "Optional \<tau> < \<sigma> = (case \<sigma> of Optional \<rho> \<Rightarrow> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
| "Collection \<tau> < \<sigma> = (case \<sigma> of Collection \<rho> \<Rightarrow> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
| "Set \<tau> < \<sigma> = (case \<sigma> of Set \<rho> \<Rightarrow> \<tau> < \<rho> | Collection \<rho> \<Rightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
| "OrderedSet \<tau> < \<sigma> = (case \<sigma> of OrderedSet \<rho> \<Rightarrow> \<tau> < \<rho> | Collection \<rho> \<Rightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
| "Bag \<tau> < \<sigma> = (case \<sigma> of Bag \<rho> \<Rightarrow> \<tau> < \<rho> | Collection \<rho> \<Rightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
| "Sequence \<tau> < \<sigma> = (case \<sigma> of Sequence \<rho> \<Rightarrow> \<tau> < \<rho> | Collection \<rho> \<Rightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> | SupType \<Rightarrow> True | _ \<Rightarrow> False)"
  by pat_completeness auto
  termination by lexicographic_order
*)
(*
lemma collection_less_alt_def:
  "Collection \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Collection \<rho> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)
*)
(*code_pred [show_modes] less_type .
*)
value "Integer < Real"
value "Collection (Required Integer) < Collection (Optional Real)"
value "Set (Required Integer) < Collection (Required Real)"
value "Collection (Required Integer) < Collection (Required Integer)"

definition "\<tau> \<le> \<sigma> \<equiv> \<tau> = \<sigma> \<or> \<tau> < \<sigma>" for \<tau> \<sigma> :: type
(*
definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else SupType))"

value "Real \<squnion> Boolean"
value "Real[1] \<squnion> Boolean[?]"
*)
(*definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"*)
(*
definition sup_type where
  "\<tau> \<squnion> \<sigma> \<equiv> (case (\<tau>, \<sigma>) of (ST \<tau>, ST \<sigma>) \<Rightarrow>
    ST (if ST \<tau> \<le> ST \<sigma> then \<sigma> else (if ST \<sigma> \<le> ST \<tau> then \<tau> else OclAny))
    | (CT \<tau>, CT \<sigma>) \<Rightarrow>
     CT (if CT \<tau> \<le> CT \<sigma> then \<sigma> else (if CT \<sigma> \<le> CT \<tau> then \<tau> else Collection (ST Real))))"
*)
(*
definition sup_simple_type where
 "sup_simple_type \<tau> \<sigma> \<equiv> (if ST \<tau> \<le> ST \<sigma> then \<sigma> else (if ST \<sigma> \<le> ST \<tau> then \<tau> else OclAny))"
*)
(*
fun sup_simple_type where
  "sup_simple_type OclAny _ = OclAny"
| "sup_simple_type _ OclAny = OclAny"
| "sup_simple_type OclInvalid \<tau> = \<tau>"
| "sup_simple_type \<tau> OclInvalid = \<tau>"
| "sup_simple_type OclVoid \<tau> = \<tau>"
| "sup_simple_type \<tau> OclVoid = \<tau>"
| "sup_simple_type Boolean Boolean = Boolean"
| "sup_simple_type Boolean _ = OclAny"
| "sup_simple_type _ Boolean = OclAny"
| "sup_simple_type String String = String"
| "sup_simple_type String _ = OclAny"
| "sup_simple_type _ String = OclAny"
| "sup_simple_type Real Real = Real"
| "sup_simple_type Real Integer = Real"
| "sup_simple_type Real UnlimitedNatural = Real"
| "sup_simple_type Real _ = OclAny"
| "sup_simple_type Integer Real = Real"
| "sup_simple_type Integer Integer = Integer"
| "sup_simple_type Integer UnlimitedNatural = Integer"
| "sup_simple_type Integer _ = OclAny"
| "sup_simple_type UnlimitedNatural Real = Real"
| "sup_simple_type UnlimitedNatural Integer = Integer"
| "sup_simple_type UnlimitedNatural UnlimitedNatural = UnlimitedNatural"
| "sup_simple_type UnlimitedNatural _ = OclAny"
| "sup_simple_type _ Real = OclAny"
| "sup_simple_type _ Integer = OclAny"
| "sup_simple_type _ UnlimitedNatural = OclAny"
| "sup_simple_type _ _ = OclAny"

fun sup_type and sup_collection_type where
  "sup_type (ST \<tau>) (ST \<sigma>) = ST (sup_simple_type \<tau> \<sigma>)"
| "sup_type (CT \<tau>) (CT \<sigma>) = CT (sup_collection_type \<tau> \<sigma>)"
| "sup_type _ _ = ET"
| "sup_collection_type (Set \<tau>) (Set \<sigma>) = Set (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Set \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (OrderedSet \<sigma>) = OrderedSet (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (OrderedSet \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Bag \<sigma>) = Bag (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Bag \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Sequence \<sigma>) = Sequence (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Sequence \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Set \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (OrderedSet \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Bag \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Sequence \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
| "sup_collection_type (Collection \<tau>) (Collection \<sigma>) = Collection (\<tau> \<squnion> \<sigma>)"
*)
(*
lemma collection_not_less_self[iff]:
  "\<not> Collection \<tau> < Collection \<tau>" by (induct; simp)

lemma set_not_less_self[iff]:
  "\<not> Set \<tau> < Set \<tau>" by (induct; simp)

lemma ordered_set_not_less_self[iff]:
  "\<not> OrderedSet \<tau> < OrderedSet \<tau>" by (induct; simp)

lemma bag_not_less_self[iff]:
  "\<not> Bag \<tau> < Bag \<tau>" by (induct; simp)

lemma sequence_not_less_self[iff]:
  "\<not> Sequence \<tau> < Sequence \<tau>" by (induct; simp)

lemma required_less_ex:
  "Required \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Required \<rho> \<or> \<sigma> = Optional \<rho> \<or> \<sigma> = Optional \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma set_less_ex:
  "Set \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Set \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma ordered_set_less_ex:
  "OrderedSet \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = OrderedSet \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma bag_less_ex:
  "Bag \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Bag \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma sequence_less_ex:
  "Sequence \<tau> < \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> < \<rho> \<and> \<sigma> = Sequence \<rho> \<or> \<sigma> = Collection \<rho> \<or> \<sigma> = Collection \<tau> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp)

lemma not_less_invalid [iff]:
  "\<not> \<tau> < OclInvalid"
  by (induct \<tau>; simp)

lemma invalid_less_void [simp]:
  "\<tau> < OclVoid \<Longrightarrow> \<tau> = OclInvalid"
  by (induct \<tau>; simp)
*)
(*inductive_cases e2[elim!]: "\<tau> <: SupType"*)

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: type
  by (rule iffI; auto simp add: less_eq_type_def less_type_def;
      induct \<tau> arbitrary: \<sigma>; auto)

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: type
  by (simp add: less_eq_type_def)

lemma conforms_to_optional:
  "\<tau>[?] <: \<rho> \<Longrightarrow> OclVoid <: \<rho>"
  apply (induct; auto)
  apply (simp add: Any_conforms_to_SupType)
  by (simp add: conforms_to.intros(2))

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (auto simp add: less_eq_type_def less_type_def)
  apply (erule notE)
  apply (induct \<tau> \<sigma> arbitrary: \<rho> rule: conforms_to.induct)
  apply auto[1]
  apply (simp add: conforms_to_optional)
  apply (metis Invalid_conforms_to_Any less_invalid_elim)
  using Any_conforms_to_SupType Required_conforms_to_Required Required_conforms_to_Optional apply force
  apply (erule optional_less_elim; simp add: conforms_to.intros)
  using Required_conforms_to_Optional dual_order.strict_trans apply blast
  using Any_conforms_to_SupType Optional_conforms_to_Optional order.strict_trans1 apply auto[1]
  using Any_conforms_to_SupType Collection_conforms_to_Collection apply auto[1]
  apply (erule set_less_elim; auto simp add: conforms_to.intros)
  apply (erule ordered_set_less_elim; auto simp add: conforms_to.intros)
  apply (erule bag_less_elim; auto simp add: conforms_to.intros)
  apply (erule sequence_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  apply (erule collection_less_elim; auto simp add: conforms_to.intros)
  done

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: type
  by (simp add: less_eq_type_def; auto simp add: less_le_not_le_type)

(*
fun sup_type where
  "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "\<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> SupType
     | OrderedSet \<rho> \<Rightarrow> SupType
     | Bag \<rho> \<Rightarrow> SupType
     | Sequence \<rho> \<Rightarrow> SupType
     | Collection \<rho> \<Rightarrow> SupType
     | _ \<Rightarrow> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny)))"
*)
(*definition sup_simple_type where
  "sup_simple_type \<tau> \<sigma> \<equiv> (case \<sigma>
    of Set \<rho> \<Rightarrow> SupType
     | OrderedSet \<rho> \<Rightarrow> SupType
     | Bag \<rho> \<Rightarrow> SupType
     | Sequence \<rho> \<Rightarrow> SupType
     | Collection \<rho> \<Rightarrow> SupType
     | _ \<Rightarrow> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny)))"
*)

(*
datatype type =
  SupType
| OclVoid
| OclInvalid
| Required simple_type ("_[1]")
| Optional simple_type ("_[?]")
| Collection type
| Set type
| OrderedSet type
| Bag type
| Sequence type
*)

function sup_type where
  "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Set \<tau>
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> OrderedSet \<tau>
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Bag \<tau>
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Sequence \<tau>
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Collection \<tau>
     | _ \<Rightarrow> SupType)"
| "OclVoid \<squnion> \<sigma> = (case \<sigma>
    of OclVoid \<Rightarrow> OclVoid
     | OclInvalid \<Rightarrow> OclVoid
     | Required \<rho> \<Rightarrow> Optional \<rho>
     | Optional \<rho> \<Rightarrow> Optional \<rho>
     | _ \<Rightarrow> SupType)"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "SupType \<squnion> \<sigma> = SupType"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Required \<tau>
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Optional \<tau>
     | _ \<Rightarrow> SupType)"
  by pat_completeness auto
  termination by lexicographic_order

(*
function sup_type where
  "SupType \<squnion> \<sigma> = SupType"
| "\<tau> \<squnion> SupType = SupType"
| "OclVoid \<squnion> \<sigma> = \<sigma>"
| "\<tau> \<squnion> OclVoid = \<tau>"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "\<tau> \<squnion> OclInvalid = \<tau>"
| "Required \<tau> \<squnion> Required \<sigma> = Required (\<tau> \<squnion> \<sigma>)"
| "Required \<tau> \<squnion> Optional \<sigma> = Optional (\<tau> \<squnion> \<sigma>)"
| "Optional \<tau> \<squnion> Required \<sigma> = Optional (\<tau> \<squnion> \<sigma>)"
| "Optional \<tau> \<squnion> Optional \<sigma> = Optional (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Set \<sigma> = Set (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Set \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> OrderedSet \<sigma> = OrderedSet (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "OrderedSet \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Bag \<sigma> = Bag (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Bag \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Sequence \<sigma> = Sequence (\<tau> \<squnion> \<sigma>)"
| "Sequence \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Set \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> OrderedSet \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Bag \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Sequence \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
| "Collection \<tau> \<squnion> Collection \<sigma> = Collection (\<tau> \<squnion> \<sigma>)"
  apply pat_completeness
*)
(*(case \<sigma>
    of Set \<rho> \<Rightarrow> Set (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OrderedSet \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Bag \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Sequence \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "Collection \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion> \<rho>)
     | _ \<Rightarrow> SupType)"
| "OclVoid \<squnion> \<sigma> = (if \<sigma> = OclInvalid then OclVoid else \<sigma>)"
| "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "SupType \<squnion> \<sigma> = SupType"
| "Required \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Required \<tau>
     | _ \<Rightarrow> SupType)"
| "Optional \<tau> \<squnion> \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion> \<rho>)
     | OclVoid \<Rightarrow> Optional \<tau>
     | OclInvalid \<Rightarrow> Optional \<tau>
     | _ \<Rightarrow> SupType)"
  by pat_completeness auto
  termination by lexicographic_order
*)

value "Required Integer \<squnion> Optional Real"
value "(Set (Required Integer)) \<squnion> (Set (Required Real))"
value "(Set (Required Integer)) \<squnion> (Bag (Optional Boolean))"
value "(Set (Required Integer)) \<squnion> Optional Real"
(*
lemma collection_less_eq_alt_def:
  "Collection \<tau> \<le> \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> \<le> \<rho> \<and> \<sigma> = Collection \<rho> \<or> \<sigma> = SupType"
  by (induct \<sigma>; simp add: less_eq_type_def)

lemma collection_less_eq_elim:
  "Collection \<tau> \<le> \<sigma> \<Longrightarrow> (\<exists>\<rho>. \<tau> \<le> \<rho> \<and> \<sigma> = Collection \<rho> \<or> \<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct \<sigma>; simp add: less_eq_type_def)

lemma q:
  "\<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow>
   \<exists>\<tau>. \<tau> \<le> \<tau> \<squnion> \<sigma>"
  by (metis less_eq_type_def less_type.simps(1))

lemma q2:
  "(\<And>\<tau>. \<tau> \<le> \<tau> \<squnion> \<sigma> \<Longrightarrow>
             Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>) \<Longrightarrow>
       \<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow>

       Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma> \<Longrightarrow>

       Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  apply auto

lemma q:
  "Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>"

lemma q1:
  "(\<And>\<tau>. \<tau> \<le> \<tau> \<squnion> Collection \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  by blast

lemma q2:
  "(\<And>\<sigma>. Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  by blast

lemma q:
  "\<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow> \<exists>\<rho>. \<tau> = Collection \<rho> \<or> \<tau> = SupType"

value "Collection SupType < SupType"
value "Collection SupType < Collection SupType"
value "Collection SupType < Collection (Collection SupType)"
value "Collection (Collection SupType) < Collection SupType"

lemma q:
  "Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"
  apply (induct \<sigma> arbitrary: \<tau>)

lemma q:
  "(\<And>\<tau>. \<tau> \<le> \<tau> \<squnion> \<sigma> \<Longrightarrow> Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   \<tau> \<le> \<tau> \<squnion> Collection \<sigma> \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"

lemma q:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma> \<Longrightarrow> \<tau> \<le> \<tau> \<squnion> Collection \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma> \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> Collection \<sigma>"

thm collection_less_alt_def
*)
(*
lemma q:
  "(\<not> P \<Longrightarrow> Q) \<Longrightarrow> (P \<Longrightarrow> \<not> Q)"
*)


lemma void_less_eq_sup:
  "OclVoid \<le> OclVoid \<squnion> \<sigma>"
  by (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)

lemma required_less_eq_sup:
  "Required \<tau> \<le> Required \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Required_conforms_to_Required less_eq_simple_type_def sup_ge1_simple_type apply blast
  using Required_conforms_to_Optional less_eq_simple_type_def sup_ge1_simple_type apply auto
  done

lemma optional_less_eq_sup:
  "Optional \<tau> \<le> Optional \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Optional_conforms_to_Optional less_eq_simple_type_def sup_ge1_simple_type apply blast
  using Optional_conforms_to_Optional less_eq_simple_type_def sup_ge1_simple_type apply blast
  done

lemma collection_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Collection_conforms_to_Collection apply auto
  done

lemma set_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Set \<tau> \<le> Set \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Set_conforms_to_Set apply auto
  done

lemma ordered_set_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   OrderedSet \<tau> \<le> OrderedSet \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using OrderedSet_conforms_to_OrderedSet apply auto
  done

lemma bag_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Bag \<tau> \<le> Bag \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Bag_conforms_to_Bag apply auto
  done

lemma sequence_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Sequence \<tau> \<le> Sequence \<tau> \<squnion> \<sigma>"
  apply (induct \<sigma>; simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Sequence_conforms_to_Sequence apply auto
  done

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: type
  apply (induct \<tau> arbitrary: \<sigma>)
  apply simp
  using void_less_eq_sup apply auto[1]
  apply (metis (mono_tags, lifting) conforms_to.intros(3) less_eq_type_def less_type_def)
  using required_less_eq_sup apply auto[1]
  using optional_less_eq_sup apply auto[1]
  using collection_less_eq_sup apply auto[1]
  using set_less_eq_sup apply auto[1]
  using ordered_set_less_eq_sup apply auto[1]
  using bag_less_eq_sup apply auto[1]
  using sequence_less_eq_sup apply auto[1]
  done

lemma sup_sup_commut:
  "SupType \<squnion> \<sigma> = \<sigma> \<squnion> SupType"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma void_sup_commut:
  "OclVoid \<squnion> \<sigma> = \<sigma> \<squnion> OclVoid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma invalid_sup_commut:
  "OclInvalid \<squnion> \<sigma> = \<sigma> \<squnion> OclInvalid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma required_sup_commut:
  "Required \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Required \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma optional_sup_commut:
  "Optional \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Optional \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma collection_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Collection \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Collection \<tau>"
  by (cases \<sigma>; simp)

lemma set_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Set \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Set \<tau>"
  by (cases \<sigma>; simp)

lemma ordered_set_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   OrderedSet \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> OrderedSet \<tau>"
  by (cases \<sigma>; simp)

lemma bag_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Bag \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Bag \<tau>"
  by (cases \<sigma>; simp)

lemma sequence_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Sequence \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Sequence \<tau>"
  by (cases \<sigma>; simp)

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: type
  apply (induct \<tau> arbitrary: \<sigma>)
  using sup_sup_commut apply auto[1]
  using void_sup_commut apply auto[1]
  using invalid_sup_commut apply auto[1]
  using required_sup_commut apply auto[1]
  using optional_sup_commut apply auto[1]
  using collection_sup_commut apply auto[1]
  using set_sup_commut apply auto[1]
  using ordered_set_sup_commut apply auto[1]
  using bag_sup_commut apply auto[1]
  using sequence_sup_commut apply auto[1]
  done
(*
lemma less_le_not_le_type2:
  "\<tau> < \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: type
  using less_le_not_le_type by auto

lemma less_eq_type_code [code]:
  "\<tau> \<le> \<sigma> \<equiv> \<tau> = \<sigma> \<or> \<tau> < \<sigma>"
  for \<tau> \<sigma> :: type
  by (simp add: less_eq_type_def)

lemma sup_type_code [code]:
  "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else OclAny))"
  by (simp add: sup_type_def)
*)
lemma sup_type_idem:
  "\<tau> \<squnion> \<tau> = \<tau>"
  for \<tau> :: type
  by (induct \<tau>; simp)

lemma sup_type_strict_order:
  "\<sigma> < \<tau> \<Longrightarrow> \<tau> \<squnion> \<sigma> = \<tau>"
  for \<tau> \<sigma> :: type
  apply (simp only: less_type_def)
  apply (induct rule: conforms_to.induct)
  apply auto[1]
  apply auto[1]
  using sup_commut_type sup_type.simps(7) apply auto[1]
  apply (simp add: sup.strict_order_iff)
  using sup.absorb1 apply auto[1]
  apply (simp add: sup.strict_order_iff)
  apply simp
  apply simp
  apply simp
  apply simp
  apply simp
  using sup_type_idem apply auto[1]
  using sup_type_idem apply auto[1]
  using sup_type_idem apply auto[1]
  using sup_type_idem apply auto[1]
  done

lemma sup_less_then_self_eq_self2:
  "\<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> < \<sigma> \<or> \<sigma> < \<tau> \<Longrightarrow> \<tau> \<squnion> \<sigma> < \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (auto simp only: less_eq_type_def less_type_def)
  apply (simp add: less_type_def sup_commut_type sup_type_strict_order)
  apply (simp add: less_type_def sup_type_strict_order)
  done

lemma sup_less_eq_sup:
  "\<tau> < SupType \<Longrightarrow> \<sigma> < SupType \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> SupType"
  using conforms_to.intros(1) less_eq_type_def less_type_def by auto

lemma sup_less_eq_void:
  "\<tau> < OclVoid \<Longrightarrow> \<sigma> < OclVoid \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> OclVoid"
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def less_void_elim sup_type_idem)

lemma sup_less_eq_invalid:
  "\<tau> < OclInvalid \<Longrightarrow> \<sigma> < OclInvalid \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> OclInvalid"
  using less_type_def by auto

lemma sup_less_eq_required:
  "\<tau> < Required \<rho> \<Longrightarrow> \<sigma> < Required \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> Required \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_required_elim)
  apply (simp add: conforms_to.intros(3) less_eq_type_def less_type_def)
  apply (simp add: conforms_to.intros(4) less_eq_type_def less_type_def)
  apply (simp add: conforms_to.intros(4) less_eq_type_def less_type_def)
proof -
  fix \<tau>' :: simple_type and \<tau>'' :: simple_type
  assume a1: "\<tau>' < \<rho>"
  assume a2: "\<tau>'' < \<rho>"
  assume a3: "\<tau> = \<tau>'[1]"
  assume a4: "\<sigma> = \<tau>''[1]"
  then have "(<:) \<tau>' \<squnion> \<tau>''[1] = (<) (\<tau> \<squnion> \<sigma>)"
    using a3 less_type_def by auto
  moreover
    { assume "\<tau>' \<squnion> \<tau>'' = \<rho> \<squnion> \<tau>'"
      then have ?thesis
        using a4 a3 a1 by (simp add: sup.strict_order_iff) }
    ultimately show ?thesis
      using a2 a1 by (metis conforms_to.intros(4) less_eq_type_def sup.strict_order_iff sup_assoc)
  qed

(*  by (smt conforms_to.intros(4) le_neq_trans less_eq_type_def less_type_def sup.orderI sup.strict_order_iff sup_assoc sup_type.simps(9) type.inject(1) type.simps(101))*)

lemma sup_less_eq_optional:
  "\<tau> < Optional \<rho> \<Longrightarrow> \<sigma> < Optional \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> Optional \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_optional_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Required_conforms_to_Optional less_eq_simple_type_def sup_least_simple_type apply auto[1]
  apply (meson Optional_conforms_to_Optional eq_refl less_imp_le order.not_eq_order_implies_strict sup_least_simple_type)
  using Optional_conforms_to_Optional apply auto[1]
  apply (metis (no_types, lifting) Required_conforms_to_Optional sup.idem sup.strict_order_iff sup_assoc)
  apply (metis (no_types, lifting) Optional_conforms_to_Optional sup.left_commute sup.strict_order_iff sup_commut_simple_type)
  apply (metis (no_types, lifting) Optional_conforms_to_Optional sup.strict_order_iff sup_commut_simple_type sup_left_commute)
  apply (metis conforms_to.intros(6) sup.assoc sup.strict_order_iff)
  done

lemma sup_less_eq_collection:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Collection \<rho> \<Longrightarrow>
   \<sigma> < Collection \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Collection \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_collection_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Collection_conforms_to_Collection apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_strict_order apply auto[1]
  using Set_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using OrderedSet_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Bag_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Collection_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  using Sequence_conforms_to_Collection less_type_def sup_commut_type sup_type_idem sup_type_strict_order apply auto[1]
  done

lemma sup_less_eq_set:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Set \<rho> \<Longrightarrow>
   \<sigma> < Set \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Set \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_set_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Set_conforms_to_Set by auto

lemma sup_less_eq_ordered_set:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < OrderedSet \<rho> \<Longrightarrow>
   \<sigma> < OrderedSet \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> OrderedSet \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_ordered_set_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using OrderedSet_conforms_to_OrderedSet by auto

lemma sup_less_eq_bag:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Bag \<rho> \<Longrightarrow>
   \<sigma> < Bag \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Bag \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_bag_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Bag_conforms_to_Bag by auto

lemma sup_less_eq_sequence:
  "(\<And>\<tau> \<sigma>. \<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>) \<Longrightarrow>
   \<tau> < Sequence \<rho> \<Longrightarrow>
   \<sigma> < Sequence \<rho> \<Longrightarrow>
   \<tau> \<squnion> \<sigma> \<le> Sequence \<rho>"
  apply (simp add: less_type_def)
  apply (elim less_sequence_elim;
         simp add: conforms_to.intros less_eq_type_def less_type_def)
  using Sequence_conforms_to_Sequence by auto

lemma sup_type_strict_order2:
  "\<tau> < \<rho> \<Longrightarrow> \<sigma> < \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (induct \<rho> arbitrary: \<tau> \<sigma>)
  apply (simp add: sup_less_eq_sup)
  apply (simp add: sup_less_eq_void)
  apply (simp add: sup_less_eq_invalid)
  apply (simp add: sup_less_eq_required)
  apply (simp add: sup_less_eq_optional)
  apply (simp add: sup_less_eq_collection)
  apply (simp add: sup_less_eq_set)
  apply (simp add: sup_less_eq_ordered_set)
  apply (simp add: sup_less_eq_bag)
  apply (simp add: sup_less_eq_sequence)
  done

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (simp add: less_eq_type_def)
  apply (elim disjE)
  using sup_type_idem apply auto[1]
  apply (simp add: sup_type_strict_order)
  apply (simp add: sup_type_strict_order sup_commut_type)
  using less_eq_type_def sup_type_strict_order2 apply auto
  done

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end

(*** Values *****************************************************************************)

(* errorable *)

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

(* nullable *)

(* В этом классе нет смысла, нужно заменить его на optional
   Если для None нужна специальная нотация, то можно её объявить
   Так же как она фактически для bot сейчас объявляется *)

class opt =
  fixes null :: "'a" ("\<epsilon>")

typedef 'a nullable ("_\<^sub>\<box>" [21] 21) = "UNIV :: 'a option set" ..

definition nullable :: "'a \<Rightarrow> 'a nullable" ("_\<^sub>\<box>" [1000] 1000) where
  "nullable x = Abs_nullable (Some x)"

instantiation nullable :: (type) opt
begin
definition "\<epsilon> \<equiv> Abs_nullable None"
instance ..
end
(*
instantiation nullable :: (bot) bot
begin
definition "\<bottom> \<equiv> \<bottom>\<^sub>\<box>"
instance ..
end

instantiation errorable :: (opt) opt
begin
definition "\<epsilon> \<equiv> \<epsilon>\<^sub>\<bottom>"
instance ..
end
*)
free_constructors case_nullable for
  nullable
| "\<epsilon> :: 'a nullable"
  apply (metis Rep_nullable_inverse null_nullable_def nullable_def option.collapse)
  apply (simp add: Abs_nullable_inject nullable_def)
  by (metis Abs_nullable_inverse UNIV_I null_nullable_def nullable_def option.distinct(1))

declare [[coercion "errorable :: bool \<Rightarrow> bool\<^sub>\<bottom>"]]
declare [[coercion "(\<lambda>x. nullable (errorable x)) :: bool \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box>"]]
(*
type_synonym 'a nullable_errorable = "'a\<^sub>\<bottom>\<^sub>\<box>"

definition nullable_errorable :: "'a \<Rightarrow> 'a\<^sub>\<bottom>\<^sub>\<box>" where "nullable_errorable \<equiv> nullable \<circ> errorable"

free_constructors case_nullable_errorable for
  nullable_errorable
| "\<bottom> :: 'a\<^sub>\<bottom>\<^sub>\<box>"
| "\<epsilon> :: 'a\<^sub>\<bottom>\<^sub>\<box>"
*)
(*
fun en_to_ne :: "'a\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> 'a\<^sub>\<box>\<^sub>\<bottom>" where
  "en_to_ne (x\<^sub>\<bottom>\<^sub>\<box>) = x\<^sub>\<box>\<^sub>\<bottom>"
| "en_to_ne (\<bottom>\<^sub>\<box>) = \<bottom>"
| "en_to_ne \<epsilon> = \<epsilon>\<^sub>\<bottom>"

fun ne_to_en :: "'a\<^sub>\<box>\<^sub>\<bottom> \<Rightarrow> 'a\<^sub>\<bottom>\<^sub>\<box>" where
  "ne_to_en (x\<^sub>\<box>\<^sub>\<bottom>) = x\<^sub>\<bottom>\<^sub>\<box>"
| "ne_to_en (\<epsilon>\<^sub>\<bottom>) = \<epsilon>"
| "ne_to_en \<bottom> = \<bottom>\<^sub>\<box>"
*)

consts
  conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale logic =
  fixes conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<^bold>\<and>" 35)
  fixes not :: "'a \<Rightarrow> 'a" ("\<^bold>\<not> _" [40] 40)
  assumes conj_commutes: "(a \<^bold>\<and> b) = (b \<^bold>\<and> a)"
      and not_not: "(\<^bold>\<not> \<^bold>\<not> a) = a"
begin
adhoc_overloading OCLType.conj conj
no_notation conj (infixr "\<^bold>\<and>" 35)
end

notation conj (infixr "\<^bold>\<and>" 35)

fun ebool_and :: "bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom>" (infixr "\<and>\<^sub>\<bottom>" 35) where
  "(a\<^sub>\<bottom> \<and>\<^sub>\<bottom> b\<^sub>\<bottom>) = (a \<and> b)\<^sub>\<bottom>"
| "(False \<and>\<^sub>\<bottom> _) = False"
| "(_ \<and>\<^sub>\<bottom> False) = False"
| "(\<bottom> \<and>\<^sub>\<bottom> _) = \<bottom>"
| "(_ \<and>\<^sub>\<bottom> \<bottom>) = \<bottom>"

fun obool_and :: "bool\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box>" (infixr "\<and>\<^sub>\<bottom>\<^sub>\<box>" 35) where
  "(a\<^sub>\<bottom>\<^sub>\<box> \<and>\<^sub>\<bottom>\<^sub>\<box> b\<^sub>\<bottom>\<^sub>\<box>) = (a \<and> b)\<^sub>\<bottom>\<^sub>\<box>"
| "(False \<and>\<^sub>\<bottom>\<^sub>\<box> _) = False"
| "(_ \<and>\<^sub>\<bottom>\<^sub>\<box> False) = False"
| "(\<bottom>\<^sub>\<box> \<and>\<^sub>\<bottom>\<^sub>\<box> _) = \<bottom>\<^sub>\<box>"
| "(_ \<and>\<^sub>\<bottom>\<^sub>\<box> \<bottom>\<^sub>\<box>) = \<bottom>\<^sub>\<box>"
| "(\<epsilon> \<and>\<^sub>\<bottom>\<^sub>\<box> _) = \<epsilon>"
| "(_ \<and>\<^sub>\<bottom>\<^sub>\<box> \<epsilon>) = \<epsilon>"

fun ebool_not :: "bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom>" ("\<not>\<^sub>\<bottom> _" [40] 40) where
  "ebool_not (a\<^sub>\<bottom>) = (\<not>a)\<^sub>\<bottom>"
| "ebool_not \<bottom> = \<bottom>"

fun obool_not :: "bool\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box>" ("\<not>\<^sub>\<bottom>\<^sub>\<box> _" [40] 40) where
  "obool_not (a\<^sub>\<bottom>\<^sub>\<box>) = (\<not>a)\<^sub>\<bottom>\<^sub>\<box>"
| "obool_not (\<bottom>\<^sub>\<box>) = \<bottom>\<^sub>\<box>"
| "obool_not \<epsilon> = \<epsilon>"

lemma ebool_and_eq_obool_and:
  "(a\<^sub>\<bottom> \<and>\<^sub>\<bottom> b\<^sub>\<bottom>)\<^sub>\<box> = (a\<^sub>\<bottom>\<^sub>\<box> \<and>\<^sub>\<bottom>\<^sub>\<box> b\<^sub>\<bottom>\<^sub>\<box>)"
  by simp

lemma obool_and_conforms_to_spec:
  "obool_and False False = False"
  "obool_and False True = False"
  "obool_and True False = False"
  "obool_and True True = True"
  "obool_and False \<epsilon> = False"
  "obool_and True \<epsilon> = \<epsilon>"
  "obool_and False \<bottom>\<^sub>\<box> = False"
  "obool_and True \<bottom>\<^sub>\<box> = \<bottom>\<^sub>\<box>"
  "obool_and \<epsilon> False = False"
  "obool_and \<epsilon> True = \<epsilon>"
  "obool_and \<epsilon> \<epsilon> = \<epsilon>"
  "obool_and \<epsilon> \<bottom>\<^sub>\<box> = \<bottom>\<^sub>\<box>"
  "obool_and \<bottom>\<^sub>\<box> False = False"
  "obool_and \<bottom>\<^sub>\<box> True = \<bottom>\<^sub>\<box>"
  "obool_and \<bottom>\<^sub>\<box> \<epsilon> = \<bottom>\<^sub>\<box>"
  "obool_and \<bottom>\<^sub>\<box> \<bottom>\<^sub>\<box> = \<bottom>\<^sub>\<box>"
  by (simp_all)

lemma ebool_and_commut:
  "(a \<and>\<^sub>\<bottom> b) = (b \<and>\<^sub>\<bottom> a)"
  by (induct a b rule: ebool_and.induct; simp add: conj_commute)

lemma ebool_not_not [simp]:
  "(\<not>\<^sub>\<bottom> \<not>\<^sub>\<bottom> a) = a"
  by (induct a rule: ebool_not.induct; simp)

lemma obool_and_commut:
  "(a \<and>\<^sub>\<bottom>\<^sub>\<box> b) = (b \<and>\<^sub>\<bottom>\<^sub>\<box> a)"
  by (induct a b rule: obool_and.induct; simp add: conj_commute ebool_and_commut)

lemma obool_not_not [simp]:
  "(\<not>\<^sub>\<bottom>\<^sub>\<box> \<not>\<^sub>\<bottom>\<^sub>\<box> a) = a"
  by (induct a rule: obool_not.induct; simp)

interpretation ebool_logic: logic ebool_and ebool_not
  apply standard
  apply (simp add: ebool_and_commut)
  apply (simp)
  done

interpretation obool_logic: logic obool_and obool_not
  apply standard
  apply (simp add: obool_and_commut)
  apply (simp)
  done

adhoc_overloading OCLType.conj obool_and
adhoc_overloading OCLType.conj ebool_and

value "True\<^sub>\<bottom> \<^bold>\<and> \<bottom>"
value "False\<^sub>\<bottom>\<^sub>\<box> \<^bold>\<and> \<epsilon>"

(*** UnlimitedNatural ***)

(*declare [[coercion "errorable :: enat \<Rightarrow> enat\<^sub>\<bottom>"]]
declare [[coercion "(\<lambda>x. nullable (errorable x)) :: enat \<Rightarrow> enat\<^sub>\<bottom>\<^sub>\<box>"]]*)

(* Для бесконечности правила указаны явно, хотя можно было бы упростить.
   Но просто это не очень тривиально, обычно результат бесконечность, а не ошибка.
   Чтобы было явно видно *)

typedef unat = "UNIV :: nat option set" ..

definition "unat x \<equiv> Abs_unat (Some x)"

instantiation unat :: infinity
begin
definition "\<infinity> \<equiv> Abs_unat None"
instance ..
end

free_constructors cases_unat for
  unat
| "\<infinity> :: unat"
  apply (metis Abs_unat_cases infinity_unat_def option.exhaust unat_def)
  apply (metis Abs_unat_inverse iso_tuple_UNIV_I option.inject unat_def)
  by (simp add: Abs_unat_inject infinity_unat_def unat_def)

fun eunat_plus :: "unat\<^sub>\<bottom> \<Rightarrow> unat\<^sub>\<bottom> \<Rightarrow> unat\<^sub>\<bottom>" (infixl "+\<^sub>\<bottom>" 65) where
  "(unat x)\<^sub>\<bottom> +\<^sub>\<bottom> (unat y)\<^sub>\<bottom> = (unat (x + y))\<^sub>\<bottom>"
| "\<infinity>\<^sub>\<bottom> +\<^sub>\<bottom> _ = \<bottom>"
| "_ +\<^sub>\<bottom> \<infinity>\<^sub>\<bottom> = \<bottom>"
| "\<bottom> +\<^sub>\<bottom> _ = \<bottom>"
| "_ +\<^sub>\<bottom> \<bottom> = \<bottom>"

instantiation errorable :: (plus) plus
begin

fun plus_errorable where
  "plus_errorable a\<^sub>\<bottom> b\<^sub>\<bottom> = (a + b)\<^sub>\<bottom>"
| "plus_errorable _ _ = \<bottom>"

instance ..
end

instantiation nullable :: (bot) plus
begin

fun plus_nullable where
  "plus_nullable a\<^sub>\<box> b\<^sub>\<box> = (a + b)\<^sub>\<box>"
| "plus_nullable _ _ = \<bottom>\<^sub>\<box>"

instance ..
end

typedef eunat = "UNIV :: unat option set" ..

definition "eunat x \<equiv> Abs_eunat (Some (unat x))"

instantiation eunat :: infinity
begin
definition "\<infinity> \<equiv> Abs_eunat (Some \<infinity>)"
instance ..
end

instantiation eunat :: bot
begin
definition "\<bottom> \<equiv> Abs_eunat None"
instance ..
end

free_constructors cases_eunat for
  eunat
| "\<infinity> :: eunat"
| "\<bottom> :: eunat"
  apply (metis Rep_eunat_inverse bot_eunat_def eunat_def infinity_eunat_def not_None_eq unat.exhaust)
  apply (metis Abs_eunat_inverse eunat_def iso_tuple_UNIV_I option.inject unat.inject)
  apply (metis Abs_eunat_inverse eunat_def infinity_eunat_def iso_tuple_UNIV_I option.inject unat.distinct(1))
  apply (metis Abs_eunat_inverse bot_eunat_def eunat_def iso_tuple_UNIV_I option.simps(3))
  by (metis Abs_eunat_inverse UNIV_I bot_eunat_def infinity_eunat_def option.distinct(1))

instantiation eunat :: plus
begin
fun plus_eunat :: "eunat \<Rightarrow> eunat \<Rightarrow> eunat" where
  "plus_eunat (eunat x) (eunat y) = eunat (x + y)"
| "plus_eunat \<infinity> _ = \<bottom>"
| "plus_eunat _ \<infinity> = \<bottom>"
| "plus_eunat \<bottom> _ = \<bottom>"
| "plus_eunat _ \<bottom> = \<bottom>"
instance ..
end

value "(eunat 1) + \<infinity>"
value "(eunat 1) + (eunat 2)"
value "(eunat 1) + \<bottom>"

value "(eunat 1) + \<infinity>"
value "(eunat 1) + (eunat 2)"

value "(eunat 1)\<^sub>\<box> + (eunat 2)\<^sub>\<box>"
value "(eunat 1)\<^sub>\<box> + \<epsilon>"
value "(\<infinity>::eunat)\<^sub>\<box> + \<epsilon>"
value "(eunat 1)\<^sub>\<box> + (\<infinity>::eunat)\<^sub>\<box>"

(* Real *)

value "real 1 + real 2"
value "(real 1)\<^sub>\<bottom> + (real 2)\<^sub>\<bottom>"
value "(real 1)\<^sub>\<bottom>\<^sub>\<box> + (real 3 / real 2)\<^sub>\<bottom>\<^sub>\<box>"

value "int 1 + int 2"
value "(int 1)\<^sub>\<bottom> + (int 2)\<^sub>\<bottom>"
value "(int 1)\<^sub>\<bottom>\<^sub>\<box> + (int 2)\<^sub>\<bottom>\<^sub>\<box>"

(* Any *)

datatype any = (*Invalid |*) BoolVal "bool\<^sub>\<bottom>" | UnlimNatVal "eunat" | RealVal "real\<^sub>\<bottom>" | InvalidAny
(*
instantiation any :: bot
begin
definition "\<bottom> \<equiv> Invalid"
instance ..
end
*)
datatype oany = (*Null | OInvalid |*) OBoolVal "bool\<^sub>\<bottom>\<^sub>\<box>" | OUnlimNatVal "eunat\<^sub>\<box>" | ORealVal "real\<^sub>\<bottom>\<^sub>\<box>"
  | NullAny | OInvalidAny
(*
instantiation oany :: opt
begin
definition "\<epsilon> \<equiv> Null"
instance ..
end
*)
inductive any_oany :: "any \<Rightarrow> oany \<Rightarrow> bool" where
(*  "any_oany (Invalid) (OInvalid)"
|*) "any_oany (BoolVal x) (OBoolVal x\<^sub>\<box>)"
| "any_oany (UnlimNatVal x) (OUnlimNatVal x\<^sub>\<box>)"
| "any_oany (RealVal x) (ORealVal x\<^sub>\<box>)"
| "any_oany (InvalidAny) (OInvalidAny)"

fun any_to_oany :: "any \<Rightarrow> oany" where
(*  "any_to_oany (Invalid) = (OInvalid)"
|*) "any_to_oany (BoolVal x) = (OBoolVal x\<^sub>\<box>)"
| "any_to_oany (UnlimNatVal x) = (OUnlimNatVal x\<^sub>\<box>)"
| "any_to_oany (RealVal x) = (ORealVal x\<^sub>\<box>)"
| "any_to_oany (InvalidAny) = (OInvalidAny)"
(*
fun oany_to_any :: "oany \<Rightarrow> any" where
  "oany_to_any (OBoolVal x) = (BoolVal x\<^sub>\<box>)"
| "oany_to_any (OUnlimNatVal x) = (UnlimNatVal x\<^sub>\<box>)"
| "oany_to_any (ORealVal x) = (RealVal x\<^sub>\<box>)"
| "oany_to_any (OInvalidAny) = (InvalidAny)"
*)
(*
free_constructors cases_oany for
  any_to_oany
| "\<epsilon> :: oany"
*)
declare [[coercion any_to_oany]]

(* Set *)

typedef 'a myset = "UNIV :: 'a fset option set" ..

setup_lifting type_definition_myset

lift_definition myset :: "'a fset \<Rightarrow> 'a myset" is Some .

lift_definition mysetempty :: "'a myset" is "Some fempty" .

lift_definition mysetinsert :: "'a \<Rightarrow> 'a myset \<Rightarrow> 'a myset" is "map_option \<circ> finsert" .

value "(map_option \<circ> finsert) 3 (Some {|1::nat,2|})"
value "(map_option \<circ> finsert) (3::nat) (None)"

instantiation myset :: (type) bot
begin
lift_definition bot_myset :: "'a myset" is None .
instance ..
end


free_constructors case_myset for
  myset
| "\<bottom> :: 'a myset"
  apply (simp_all add: bot_myset_def myset_def)
  apply (metis Rep_myset_inverse option.collapse)
  apply (metis Abs_myset_inverse iso_tuple_UNIV_I option.inject)
  apply (metis Abs_myset_inverse iso_tuple_UNIV_I option.distinct(1))
  done

lift_definition map_myset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a myset \<Rightarrow> 'b myset" 
  is "map_option \<circ> fimage" .
thm map_myset_def

copy_bnf 'a myset

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name myset} |> Option.map #ctrs\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name fset} |> Option.map #ctrs\<close>

copy_bnf 'a errorable
copy_bnf 'a nullable



datatype val =
  RequiredVal any
| OptionalVal "oany"
| SetVal "val fset\<^sub>\<bottom>"

value "myset {|BoolVal True, BoolVal False|}"
value "myset {|RequiredVal (BoolVal True\<^sub>\<bottom>), RequiredVal (BoolVal False\<^sub>\<bottom>)|}"
value "myset {|RequiredVal (BoolVal True\<^sub>\<bottom>), OptionalVal (BoolVal False\<^sub>\<bottom>)|}"
value "myset {|OptionalVal (BoolVal True\<^sub>\<bottom>), OptionalVal (BoolVal False\<^sub>\<bottom>)|}"
(*
inductive cast_any :: "any \<Rightarrow> any \<Rightarrow> bool" where
  "cast_any_oany v = v\<^sub>\<box>"

fun cast_any_oany :: "any \<Rightarrow> any\<^sub>\<box>" where
  "cast_any_oany v = v\<^sub>\<box>"
*)
inductive cast_any :: "any \<Rightarrow> any \<Rightarrow> bool" where
(*  "cast_any \<bottom> (BoolVal \<bottom>)"
| "cast_any \<bottom> (UnlimNatVal \<bottom>)"
|*) "cast_any (UnlimNatVal \<bottom>) (RealVal \<bottom>)"
| "cast_any (UnlimNatVal (eunat x)) (RealVal (real x)\<^sub>\<bottom>)"
| "cast_any (UnlimNatVal \<infinity>) (RealVal \<bottom>)"
| "cast_any (BoolVal \<bottom>) InvalidAny"
| "cast_any (RealVal \<bottom>) InvalidAny"

inductive cast_oany :: "oany \<Rightarrow> oany \<Rightarrow> bool" where
   "cast_any x y \<Longrightarrow> any_oany x ox \<Longrightarrow> any_oany y oy \<Longrightarrow> cast_oany ox oy"
(*| "cast_oany (Invalid) (OInvalid)"
| "cast_oany (BoolVal x) (OBoolVal x\<^sub>\<box>)"
| "cast_oany (UnlimNatVal x) (OUnlimNatVal x\<^sub>\<box>)"
| "cast_oany (RealVal x) (ORealVal x\<^sub>\<box>)"
| "cast_oany (InvalidAny) (OInvalidAny)"*)
(*| "cast_oany \<epsilon> (OBoolVal \<epsilon>)"
| "cast_oany \<epsilon> (OUnlimNatVal \<epsilon>)"*)
| "cast_oany (OUnlimNatVal \<epsilon>) (ORealVal \<epsilon>)"
| "cast_oany (OBoolVal \<epsilon>) NullAny"
| "cast_oany (ORealVal \<epsilon>) NullAny"

code_pred [show_modes] cast_oany .

(* unat может быть скастован в int или real, поэтому это не функция.
   Хотя стоп, напрямую в real не должен, только через int.
   Всё-таки это не функция. Потому что \<bottom> кастуется в разные значения.
   Хотя если добавить сюда целевой тип, то это будет функция

   Это нужно будет заменить на явное перечисление типов, когда будут значения для всех типов:
   cast_any_fun Invalid _ = \<bottom>

   Непонятно что делать с кастом unat в real. Запретить его (разрешить только через int) или нет
   Если запрещать, то это тоже нужно запретить:
   cast_any_fun Invalid Real = (RealVal \<bottom>) *)

fun cast_any_fun :: "any \<Rightarrow> simple_type \<Rightarrow> any option" where
(*  "cast_any_fun Invalid OclInvalid = None"
| "cast_any_fun Invalid Boolean = Some (BoolVal \<bottom>)"
| "cast_any_fun Invalid UnlimitedNatural = Some (UnlimNatVal \<bottom>)"
| "cast_any_fun Invalid Real = Some (RealVal \<bottom>)"
| "cast_any_fun Invalid OclAny = Some InvalidAny"
| "cast_any_fun Invalid _ = None"

|*) "cast_any_fun (BoolVal \<bottom>) OclAny = Some InvalidAny"
| "cast_any_fun (UnlimNatVal \<bottom>) OclAny = Some InvalidAny"
| "cast_any_fun (RealVal \<bottom>) OclAny = Some InvalidAny"

| "cast_any_fun InvalidAny OclAny = None"
| "cast_any_fun (UnlimNatVal \<infinity>) OclAny = Some InvalidAny"
| "cast_any_fun x OclAny = Some x"

| "cast_any_fun InvalidAny _ = None"

| "cast_any_fun (BoolVal x) _ = None"
| "cast_any_fun (UnlimNatVal \<bottom>) Real = Some (RealVal \<bottom>)"
| "cast_any_fun (UnlimNatVal (eunat x)) Real = Some (RealVal (real x)\<^sub>\<bottom>)"
| "cast_any_fun (UnlimNatVal \<infinity>) Real = Some (RealVal \<bottom>)"
| "cast_any_fun (UnlimNatVal _) _ = None"
| "cast_any_fun (RealVal x) _ = None"

fun type_of_any :: "any \<Rightarrow> simple_type" where
(*  "type_of_any Invalid = OclInvalid"
|*) "type_of_any (BoolVal _) = Boolean"
| "type_of_any (UnlimNatVal v) = UnlimitedNatural"
| "type_of_any (RealVal v) = Real"
| "type_of_any (InvalidAny) = OclAny"
(*  "\<T> (NullVal) = OclVoid"
| "\<T> (BooleanVal _) = Boolean"
| "\<T> (RealVal _) = Real"
| "\<T> (IntegerVal _) = Integer"
| "\<T> (UnlimNatVal _) = UnlimitedNatural"
| "\<T> (StringVal _) = String"
| "\<T> (AnyVal) = OclAny"
| "\<T> (ObjectVal c _) = ObjectType c"
| "\<T> (ObjectVals c _) = ObjectType c"
*)

fun type_of_oany :: "oany \<Rightarrow> simple_type" where
  "type_of_oany (OBoolVal _) = Boolean"
| "type_of_oany (OUnlimNatVal v) = UnlimitedNatural"
| "type_of_oany (ORealVal v) = Real"
| "type_of_oany (OInvalidAny) = OclAny"
| "type_of_oany (NullAny) = OclAny"

lemma type_of_oany_eq_type_of_any:
  "type_of_oany (any_to_oany x) = type_of_any x"
  apply (cases x; simp)
  done

(*
  "cast_any x y \<Longrightarrow> any_oany x ox \<Longrightarrow> any_oany y oy \<Longrightarrow> cast_oany ox oy"
| "cast_oany (OUnlimNatVal \<epsilon>) (ORealVal \<epsilon>)"
| "cast_oany (OBoolVal \<epsilon>) NullAny"
| "cast_oany (ORealVal \<epsilon>) NullAny"
*)

fun cast_oany_fun :: "oany \<Rightarrow> simple_type \<Rightarrow> oany option" where
  "cast_oany_fun NullAny _ = None"
| "cast_oany_fun OInvalidAny _ = None"
| "cast_oany_fun (OBoolVal \<epsilon>) OclAny = Some NullAny"
| "cast_oany_fun (OBoolVal \<epsilon>) _ = None"
| "cast_oany_fun (OUnlimNatVal \<epsilon>) OclAny = Some NullAny"
| "cast_oany_fun (OUnlimNatVal \<epsilon>) Real = Some (ORealVal \<epsilon>)"
| "cast_oany_fun (OUnlimNatVal \<epsilon>) _ = None"
| "cast_oany_fun (ORealVal \<epsilon>) OclAny = Some NullAny"
| "cast_oany_fun (ORealVal \<epsilon>) _ = None"
| "cast_oany_fun (OBoolVal x\<^sub>\<box>) t = map_option any_to_oany (cast_any_fun (BoolVal x) t)"
| "cast_oany_fun (OUnlimNatVal x\<^sub>\<box>) t = map_option any_to_oany (cast_any_fun (UnlimNatVal x) t)"
| "cast_oany_fun (ORealVal x\<^sub>\<box>) t = map_option any_to_oany (cast_any_fun (RealVal x) t)"

thm "tranclp_induct"

lemma cast_any_implies_cast_any_fun:
  "cast_any x y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any_fun x t = Some y"
  apply (induct rule: cast_any.induct; simp)
  done
(*
lemma q13:
  "cast_any_fun x OclInvalid \<noteq> Some Invalid"
  apply (cases x; simp)
  done

lemma q14:
  "cast_any_fun x UnlimitedNatural = Some (UnlimNatVal \<bottom>) \<Longrightarrow> x = Invalid"
  apply (cases x; simp)
  done

lemma q15:
  "cast_any_fun x UnlimitedNatural = Some (UnlimNatVal xa) \<Longrightarrow> x = Invalid"
  apply (cases x; simp)
  done

lemma q16:
  "cast_any_fun x Boolean = Some (BoolVal \<bottom>) \<Longrightarrow> x = Invalid"
  apply (cases x; simp)
  done
*)
lemma q14 [simp]:
  "cast_any_fun x UnlimitedNatural \<noteq> Some (UnlimNatVal \<bottom>)"
  apply (cases x; simp)
  done

lemma q15 [simp]:
  "cast_any_fun x UnlimitedNatural \<noteq> Some (UnlimNatVal xa)"
  apply (cases x; simp)
  done

lemma q16 [simp]:
  "cast_any_fun x Boolean \<noteq> Some (BoolVal \<bottom>)"
  apply (cases x; simp)
  done

lemma q17:
  "cast_any_fun (UnlimNatVal x) Real = Some (RealVal \<bottom>) \<Longrightarrow> x = \<bottom> \<or> x = \<infinity>"
  apply (cases x; simp)
  done
(*
lemma q18:
  "cast_any_fun x Real = Some (RealVal \<bottom>) \<Longrightarrow> x = Invalid \<or> x = UnlimNatVal \<bottom> \<or> x = UnlimNatVal \<infinity>"
  apply (cases x; simp add: q17)
  done
*)
lemma q18:
  "cast_any_fun x Real = Some (RealVal \<bottom>) \<Longrightarrow> x = UnlimNatVal \<bottom> \<or> x = UnlimNatVal \<infinity>"
  apply (cases x; simp add: q17)
  done

lemma cast_any_implies_cast_any_fun2:
  "cast_any y z \<Longrightarrow>
   (\<And>t. type_of_any y = t \<Longrightarrow>
    cast_any_fun x t = Some y) \<Longrightarrow>
   type_of_any z = t \<Longrightarrow>
   cast_any_fun x t = Some z"
  apply (induct rule: cast_any.induct)
(*  using bot_any_def q13 apply auto[1]
  using bot_any_def q13 apply auto[1]*)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  using q18 by fastforce

lemma cast_any_closure_implies_cast_any_fun:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any_fun x t = Some y"
  apply (induct arbitrary: t rule: tranclp_induct)
  apply (simp add: cast_any_implies_cast_any_fun)
  using cast_any_implies_cast_any_fun2 by blast

lemma q21:
  "cast_any_fun (BoolVal x) OclAny = Some InvalidAny \<Longrightarrow> x = \<bottom>"
  apply (cases x; simp)
  done

lemma q22:
  "cast_any_fun (UnlimNatVal x) Real = Some (RealVal y) \<Longrightarrow>
   cast_any\<^sup>+\<^sup>+ (UnlimNatVal x) (RealVal y)"
  apply (cases x; cases y; simp)
  using cast_any.simps by auto

lemma q23:
  "cast_any_fun (UnlimNatVal x) OclAny = Some InvalidAny \<Longrightarrow>
   cast_any\<^sup>+\<^sup>+ (UnlimNatVal x) InvalidAny"
  apply (cases x; simp)
  using cast_any.intros(3) cast_any.intros(5) apply auto[1]
  using cast_any.intros(1) cast_any.intros(5) apply auto
  done

lemma q24:
  "cast_any_fun (RealVal x) OclAny = Some InvalidAny \<Longrightarrow> x = \<bottom>"
  apply (cases x; simp)
  done

lemma cast_any_fun_implies_cast_any_closure:
  "cast_any_fun x t = Some y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp)
  using cast_any.intros(4) q21 apply auto[1]
  apply (simp add: q22)
  apply (simp add: q23)
  using cast_any.intros(5) q24 apply auto
(*  using bot_any_def cast_any.intros(1) apply auto[1]
  using bot_any_def cast_any.intros apply auto[1]
  using bot_any_def cast_any.intros apply auto[1]
  using bot_any_def cast_any.intros apply auto[1]
  using cast_any.intros(6) q21 apply auto[1]
  apply (simp add: q22)
  apply (simp add: q23)
  using cast_any.intros(7) q24 apply auto[1]*)
  done

lemma cast_any_closure_eq_cast_any_fun:
  "cast_any\<^sup>+\<^sup>+ x y \<longleftrightarrow> cast_any_fun x (type_of_any y) = Some y"
  using cast_any_closure_implies_cast_any_fun cast_any_fun_implies_cast_any_closure by blast

lemma cast_oany_eq_cast_any:
  "cast_oany x y = cast_any x y"
  apply (cases x; cases y; simp add: any_oany.simps cast_oany.simps)
  done

lemma cast_oany_eq_cast_any2:
  "cast_oany x y \<Longrightarrow> cast_any x y"
  apply (cases x; cases y; simp add: any_oany.simps cast_oany.simps)
  done

lemma cast_oany_eq_cast_any3:
  "cast_any x y \<Longrightarrow> cast_oany x y"
  apply (cases x; cases y; simp add: any_oany.simps cast_oany.simps)
  done

lemma q31:
  "cast_any_fun (UnlimNatVal x) Real = Some (RealVal y) \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (OUnlimNatVal x\<^sub>\<box>) (ORealVal y\<^sub>\<box>)"
  apply (cases x; cases y; simp)
  using any_oany.intros(2) any_oany.intros(3) cast_any.intros(2) cast_oany.intros(1) apply blast
  using cast_any.intros(3) cast_oany_eq_cast_any3 apply fastforce
  using cast_any.intros(1) cast_oany_eq_cast_any3 by fastforce

lemma cast_oany_eq_cast_any1:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp add: cast_any_closure_eq_cast_any_fun)
  using cast_any.intros(4) cast_oany_eq_cast_any3 q21 apply fastforce
  apply (simp add: q31)
  apply (metis any.distinct(9) any_to_oany.simps(2) any_to_oany.simps(4) cast_any.intros(1) cast_any.intros(3) cast_any.intros(5) cast_any_fun.simps(7) cast_oany_eq_cast_any3 eunat.exhaust nullable.inject nullable_def tranclp.simps)
  using cast_any.intros(5) cast_oany_eq_cast_any3 q24 by fastforce

thm cast_any_fun_implies_cast_any_closure
(*
lemma cast_oany_eq_cast_any:
  "cast_oany\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp)
*)
(*
  apply (erule tranclp.cases)
  apply (simp add: cast_oany_eq_cast_any2 tranclp.r_into_trancl)
  apply (cases x; cases y; simp)
*)
(*
  apply (erule converse_tranclpE)
  apply (simp add: cast_oany_eq_cast_any)
  apply (rule_tac cast_any_fun_implies_cast_any_closure)
*)

(*
cast_any_fun x t = Some y \<Longrightarrow>
          x = InvalidAny \<Longrightarrow>
          y = BoolVal x1 \<Longrightarrow>
          cast_oany_fun (any_to_oany x) t =
          Some (any_to_oany y)
*)
(*
value "cast_any_fun InvalidAny Boolean"
value "cast_any_fun InvalidAny UnlimitedNatural"
value "cast_any_fun InvalidAny Real"
value "cast_any_fun InvalidAny OclAny"

value "cast_oany_fun InvalidAny Boolean"
value "cast_oany_fun InvalidAny UnlimitedNatural"
value "cast_oany_fun InvalidAny Real"
value "cast_oany_fun InvalidAny OclAny"
*)

lemma q41 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some (BoolVal y)"
  by (cases t; simp)

lemma q42 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some (UnlimNatVal y)"
  by (cases t; simp)

lemma q43 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some (RealVal y)"
  by (cases t; simp)

lemma q44 [simp]:
  "cast_any_fun InvalidAny t \<noteq> Some InvalidAny"
  by (cases t; simp)

lemma cast_any_fun_implies_cast_oany_fun:
  "cast_any_fun x t = Some y \<Longrightarrow> cast_oany_fun x t = Some y"
  apply (cases x; cases y; simp)
  done
(*
lemma cast_oany_fun_implies_cast_any_fun:
  "cast_oany_fun x t = Some y \<Longrightarrow> cast_any_fun x t = Some y"
  apply (cases x; cases y)
  done
*)

lemma any_oany_implies_any_to_oany:
  "any_oany x y \<Longrightarrow> any_to_oany x = y"
  by (induct rule: any_oany.induct; simp)

lemma any_to_oany_implies_any_oany:
  "any_to_oany x = y \<Longrightarrow> any_oany x y"
  apply (induct rule: any_to_oany.induct)
  using any_oany.intros apply auto
  done

lemma cast_oany_implies_cast_oany_fun:
  "cast_oany x y \<Longrightarrow> cast_oany_fun x (type_of_oany y) = Some y"
  apply (induct rule: cast_oany.induct)
  apply (metis any_oany_implies_any_to_oany cast_any_fun_implies_cast_oany_fun cast_any_implies_cast_any_fun type_of_oany_eq_type_of_any)
  apply simp_all
  done

lemma q51:
  "t \<noteq> OclAny \<Longrightarrow> cast_oany_fun (OBoolVal x) t = None"
  by (cases t; cases x; simp)

lemma q52:
  "cast_oany_fun (OBoolVal x) OclAny = Some NullAny \<Longrightarrow> x = \<epsilon>"
  apply (cases x; simp)
  by (metis any_to_oany.simps(1) any_to_oany.simps(4) cast_any_fun.simps(1) cast_any_fun.simps(6) ebool_not.cases oany.distinct(19) oany.distinct(5) option.inject)

lemma q53:
  "cast_oany_fun (OBoolVal x) OclAny = Some OInvalidAny \<Longrightarrow> x = \<bottom>\<^sub>\<box>"
  apply (cases x; simp)
  by (metis any_to_oany.simps(4) cast_any.intros(4) cast_any_closure_eq_cast_any_fun cast_oany_eq_cast_any cast_oany_eq_cast_any3 q21 tranclp.r_into_trancl type_of_oany_eq_type_of_any)

lemma q54:
  "cast_oany_fun (OUnlimNatVal x) Boolean = None"
  by (cases x; simp)

lemma q55:
  "cast_oany_fun (OUnlimNatVal x) UnlimitedNatural = None"
  by (cases x; simp)

lemma q56:
  "cast_oany_fun (OUnlimNatVal x) Real = Some (ORealVal y) \<Longrightarrow>
   cast_oany (OUnlimNatVal x) (ORealVal y)"
  apply (cases x; cases y; simp)
  apply (metis any.distinct(1) any_to_oany.simps(2) cast_any.cases cast_any_closure_eq_cast_any_fun cast_any_fun.simps(52) cast_oany_eq_cast_any converse_tranclpE option.simps(3) type_of_oany.simps(3) type_of_oany_eq_type_of_any)
  apply (metis any.distinct(1) any_to_oany.simps(2) cast_any.simps cast_any_closure_eq_cast_any_fun cast_any_fun.simps(52) cast_oany_eq_cast_any converse_tranclpE option.distinct(1) type_of_oany.simps(3) type_of_oany_eq_type_of_any)
  by (simp add: cast_oany.intros(2))

lemma q57:
  "cast_oany_fun (OUnlimNatVal x) OclAny = Some NullAny \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ (OUnlimNatVal x) NullAny"
  apply (cases x; simp)
  apply (metis any_to_oany.simps(4) cast_any_fun.simps(2) cast_any_fun.simps(5) cast_any_fun.simps(7) eunat.exhaust oany.distinct(19) option.inject simple_type.distinct(7) type_of_any.simps(2) type_of_oany.simps(5) type_of_oany_eq_type_of_any)
  using cast_oany.intros(2) cast_oany.intros(4) by auto

lemma q58:
  "cast_oany_fun (OUnlimNatVal x) OclAny = Some OInvalidAny \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (OUnlimNatVal x) OInvalidAny"
  apply (cases x; simp)
  by (metis any_to_oany.simps(2) cast_any_fun_implies_cast_any_closure cast_oany_eq_cast_any1 type_of_oany.simps(4) type_of_oany_eq_type_of_any)

lemma q59:
  "cast_oany_fun (ORealVal x) Boolean = None"
  by (cases x; simp)

lemma q60:
  "cast_oany_fun (ORealVal x) UnlimitedNatural = None"
  by (cases x; simp)

lemma q61:
  "cast_oany_fun (ORealVal x) Real = None"
  by (cases x; simp)

lemma q62:
  "cast_oany_fun (ORealVal x) OclAny = Some NullAny \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (ORealVal x) NullAny"
  apply (cases x; simp)
  apply (metis any_to_oany.simps(3) cast_any_fun_implies_cast_any_closure cast_oany_eq_cast_any1 type_of_oany.simps(5) type_of_oany_eq_type_of_any)
  by (simp add: cast_oany.intros(4) tranclp.r_into_trancl)

lemma q63:
  "cast_oany_fun (ORealVal x) OclAny = Some OInvalidAny \<Longrightarrow>
   cast_oany\<^sup>+\<^sup>+ (ORealVal x) OInvalidAny"
  apply (cases x; simp)
  by (metis any_to_oany.simps(3) cast_any_fun_implies_cast_any_closure cast_oany_eq_cast_any1 type_of_oany.simps(4) type_of_oany_eq_type_of_any)

lemma cast_oany_fun_implies_cast_oany:
  "cast_oany_fun x (type_of_oany y) = Some y \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ x y"
  apply (cases x; cases y; simp)
  apply (simp add: cast_oany.simps q51 q52)
  apply (simp add: cast_oany.simps q51 q52)
  apply (simp add: cast_oany.simps q51 q52)
  using cast_oany.intros(3) q52 apply auto[1]
  using cast_any.intros(4) cast_oany_eq_cast_any3 q53 apply fastforce
  apply (simp add: q54)
  apply (simp add: q55)
  apply (simp add: q56 tranclp.r_into_trancl)
  apply (simp add: q57)
  apply (simp add: q58)
  apply (simp add: q59)
  apply (simp add: q60)
  apply (simp add: q61)
  apply (simp add: q62)
  apply (simp add: q63)
  done

lemma q71:
  "cast_any y z \<Longrightarrow>
   cast_oany_fun x (type_of_oany y) = Some (any_to_oany y) \<Longrightarrow>
   cast_oany_fun x (type_of_oany z) = Some (any_to_oany z)"

lemma cast_oany_implies_cast_oany_fun2:
  "cast_oany y z \<Longrightarrow>
   cast_oany_fun x (type_of_oany y) = Some y \<Longrightarrow>
   cast_oany_fun x (type_of_oany z) = Some z"
  apply (induct rule: cast_oany.induct)


lemma cast_oany_closure_implies_cast_oany_fun:
  "cast_oany\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_oany_fun x (type_of_oany y) = Some y"
  apply (induct rule: tranclp_induct)
  apply (simp add: cast_oany_implies_cast_oany_fun)


(*

lemma cast_any_implies_cast_any_fun2:
  "cast_any y z \<Longrightarrow>
   (\<And>t. type_of_any y = t \<Longrightarrow>
    cast_any_fun x t = Some y) \<Longrightarrow>
   type_of_any z = t \<Longrightarrow>
   cast_any_fun x t = Some z"
  apply (induct rule: cast_any.induct)
(*  using bot_any_def q13 apply auto[1]
  using bot_any_def q13 apply auto[1]*)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  using q18 by fastforce

lemma cast_any_closure_implies_cast_any_fun:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> type_of_any y = t \<Longrightarrow> cast_any_fun x t = Some y"
  apply (induct arbitrary: t rule: tranclp_induct)
  apply (simp add: cast_any_implies_cast_any_fun)
  using cast_any_implies_cast_any_fun2 by blast


*)


lemma cast_oany_closure_eq_cast_oany_fun:
  "cast_oany\<^sup>+\<^sup>+ x y \<longleftrightarrow> cast_oany_fun x (type_of_oany y) = Some y"

(* Если добавить тип в качестве параметра, то из SetVal его можно убрать *)

(*
| "cast_oany (OBoolVal x) (OBoolVal y) \<Longrightarrow> cast_val (OptionalVal (OBoolVal x)) (OptionalVal (OBoolVal y))"
*)

inductive cast_val :: "val \<Rightarrow> val \<Rightarrow> bool" where
  "cast_any x y \<Longrightarrow> cast_val (RequiredVal x) (RequiredVal y)"
| "cast_oany x y \<Longrightarrow> cast_val (OptionalVal x) (OptionalVal y)"
| "cast_val (RequiredVal x) (OptionalVal x)"
| "rel_fset cast_val xs ys \<Longrightarrow>
   cast_val (SetVal xs\<^sub>\<bottom>) (SetVal ys\<^sub>\<bottom>)"

code_pred [show_modes] cast_val .

value "cast_val
         (SetVal (errorable
           {|RequiredVal (BoolVal True\<^sub>\<bottom>), RequiredVal (BoolVal False\<^sub>\<bottom>)|}))
         (SetVal (errorable
           {|OptionalVal (BoolVal False\<^sub>\<bottom>), OptionalVal (BoolVal True\<^sub>\<bottom>)|}))"
value "cast_val
         (SetVal (errorable
           {|RequiredVal (BoolVal True\<^sub>\<bottom>)|}))
         (SetVal (errorable
           {|OptionalVal (BoolVal True\<^sub>\<bottom>), OptionalVal (BoolVal False\<^sub>\<bottom>)|}))"
(*value "cast_val
         (SetVal (errorable
           {|RequiredVal (BoolVal True\<^sub>\<bottom>), RequiredVal (Invalid)|}))
         (SetVal (errorable
           {|OptionalVal (OInvalid), OptionalVal (BoolVal True\<^sub>\<bottom>)|}))"*)

term "Predicate.the (cast_oany_i_o x)"

definition "cast_any_fun2 x \<equiv> Predicate.the (cast_any_i_o x)"
definition "cast_oany_fun2 x \<equiv> Predicate.the (cast_oany_i_o x)"

term map_option
term "map_option RequiredVal"

fun cast_val_fun :: "val \<Rightarrow> type \<Rightarrow> val option" where
  "cast_val_fun (RequiredVal x) (Required t) = map_option RequiredVal (cast_any_fun x t)"
| "cast_val_fun (OptionalVal x) (Optional t) = map_option OptionalVal (cast_oany_fun2 x)"
| "cast_val_fun (RequiredVal x) (Optional t) = Some (OptionalVal (cast_oany_fun2 x))"
| "cast_val_fun (OptionalVal x) _ = None"
(*| "cast_val_fun (RequiredVal x) (Optional t) = OptionalVal (cast_any_fun x t)\<^sub>\<box>"

 "cast_any x y \<Longrightarrow> cast_val (OptionalVal x\<^sub>\<box>) (OptionalVal y\<^sub>\<box>)"
| "cast_val (RequiredVal x) (OptionalVal x\<^sub>\<box>)"
| "rel_fset cast_val xs ys \<Longrightarrow>
   cast_val (SetVal xs\<^sub>\<bottom>) (SetVal ys\<^sub>\<bottom>)"
*)

inductive cast :: "val \<Rightarrow> type \<Rightarrow> val \<Rightarrow> bool" where
  "cast (RequiredVal x) (Optional t) (OptionalVal (any_to_oany x))"
| "cast_myset x t1 t2 = y \<Longrightarrow> cast (SetVal t1 x) t2 (SetVal t2 y)"

code_pred [show_modes] cast .

inductive cast2 :: "val \<Rightarrow> val \<Rightarrow> bool" where
  "cast2 (RequiredVal x) (OptionalVal (any_to_oany x))"
| "cast (SetVal t1 x) t2 (SetVal t2 y) \<Longrightarrow> cast2 (SetVal t1 x) (SetVal t2 y)"

code_pred [show_modes] cast2 .


(* Тут была какая-то сложность в определении OclAny, что invalid и null определены
   для каждого типа отдельно, а реально одни и те же всегда.
   Цель всего этого вроде в том, чтобы определить операторы кастования.
   Например null может быть скастован в значение любого типа.
   И любое значение кроме коллекции может быть скастовано в OclAny

   null и invalid разные для разных типов! Например int null не может использоваться
   в логических выражениях *)
(*
typedef any_val1 = "UNIV :: (invalid + bool + real) set" ..
typedef any_val2 = "UNIV :: (invalid + ebool + ereal) set" ..
typedef any_val3 = "UNIV :: (bool + real) option set" ..

typedef oany_val1 = "UNIV :: (invalid + void + bool + real) set" ..
typedef oany_val2 = "UNIV :: (invalid + void + obool + oreal) set" ..
typedef oany_val3 = "UNIV :: any_val3 option set" ..

typedef any_val = "UNIV :: (bool + real) option set" ..

term "(Inr (Inr (Inl False)))"

instantiation any_val :: bot
begin
definition "\<bottom> = Abs_any_val None"
instance ..
end

fun invalid_any :: "invalid \<Rightarrow> any_val" where
  "invalid_any \<bottom> = \<bottom>"

definition bool_any :: "bool \<Rightarrow> any_val" where
  "bool_any b = Abs_any_val (Some (Inl b))"

fun ebool_any :: "ebool \<Rightarrow> any_val" where
  "ebool_any (ebool b) = Abs_any_val (Some (Inl b))"
| "ebool_any \<bottom> = \<bottom>"

definition real_any :: "real \<Rightarrow> any_val" where
  "real_any b = Abs_any_val (Some (Inr b))"

term "invalid_any \<bottom>"
term "bool_any True"
term "bool_any \<bottom>"
term "ebool_any \<bottom>"
term "real_any \<bottom>"


fun any_to_ebool :: "any_val \<Rightarrow> ebool" where
  "any_to_ebool (ebool _) = True"
| "any_to_ebool _ = \<bottom>"

typedef oany_val = "UNIV :: any_val option set" ..

instantiation oany_val :: opt
begin
definition "\<bottom> = Abs_oany_val (Some \<bottom>)"
definition "\<epsilon> = Abs_oany_val None"
instance ..
end

fun invalid_oany :: "invalid \<Rightarrow> oany_val" where
  "invalid_oany \<bottom> = \<bottom>"

fun void_oany :: "void \<Rightarrow> oany_val" where
  "void_oany \<bottom> = \<bottom>"
| "void_oany \<epsilon> = \<epsilon>"

definition any_oany :: "any_val \<Rightarrow> oany_val" where
  "any_oany b = Abs_oany_val (Some b)"

definition bool_oany :: "bool \<Rightarrow> oany_val" where
  "bool_oany b = Abs_oany_val (Some (bool_any b))"

fun ebool_oany :: "ebool \<Rightarrow> oany_val" where
  "ebool_oany (ebool b) = Abs_oany_val (Some (bool_any b))"
| "ebool_oany \<bottom> = \<bottom>"

fun obool_oany :: "obool \<Rightarrow> oany_val" where
  "obool_oany (obool b) = Abs_oany_val (Some (bool_any b))"
| "obool_oany \<bottom> = \<bottom>"
| "obool_oany \<epsilon> = \<epsilon>"
*)

typedef 'a ocl_set = "UNIV :: 'a set option set" ..

definition ocl_set :: "'a set \<Rightarrow> 'a ocl_set" where
  "ocl_set b = Abs_ocl_set (Some b)"

instantiation ocl_set :: (type) bot
begin
definition "\<bottom> = Abs_ocl_set None"
instance ..
end

free_constructors case_ocl_set for
  ocl_set
| "\<bottom> :: 'a ocl_set"
  apply (metis Rep_ocl_set_inverse bot_ocl_set_def ocl_set_def option.collapse)
  apply (metis Abs_ocl_set_inverse iso_tuple_UNIV_I ocl_set_def option.inject)
  by (metis Abs_ocl_set_inverse bot_ocl_set_def iso_tuple_UNIV_I ocl_set_def option.distinct(1))

term "ocl_set {1::int,2}"
term "ocl_set {1::real,2}"

(*
Collection - 
Set        - set
OrderedSet - list?
Bag        - multiset
Sequence   - list
*)
(*
fun ocl_set_to_ocl_set1 :: "ebool ocl_set \<Rightarrow> any_val ocl_set" where
  "ocl_set_to_ocl_set1 (ocl_set xs) = ocl_set xs"
| "ocl_set_to_ocl_set1 \<bottom> = \<bottom>"

fun ocl_set_to_ocl_set :: "'a ocl_set \<Rightarrow> 'b ocl_set" where
  "ocl_set_to_ocl_set (ocl_set xs) = ocl_set xs"
| "ocl_set_to_ocl_set \<bottom> = \<bottom>"
*)
(*
declare [[coercion "ebool :: bool \<Rightarrow> ebool"]]
declare [[coercion "obool :: bool \<Rightarrow> obool"]]
declare [[coercion "ebool_to_obool :: ebool \<Rightarrow> obool"]]
*)

datatype any =
  ErrorVal
| BooleanVal ebool
| RealVal real
| IntegerVal int
| UnlimNaturalVal enat
| StringVal string
| ObjectVal cls oid
(*
typedef eany = "UNIV :: any option set" ..

definition eany :: "any \<Rightarrow> eany" where
  "eany v = Abs_eany (Some v)"
*)
instantiation any :: bot
begin
definition "\<bottom> = ErrorVal"
instance ..
end


datatype oany =
  OVoidVal
| OErrorVal
| OBooleanVal obool
| ORealVal real
| OIntegerVal int
| OUnlimNaturalVal enat
| OStringVal string
| OObjectVal cls oid

instantiation oany :: opt
begin
definition "\<bottom> = OErrorVal"
definition "\<epsilon> = OVoidVal"
instance ..
end

(* Сделать индуктивное определение?
   Или даже включить в определение cast? *)


datatype t1 = A | B t1 t1
datatype t2 = C | D t2 t2

inductive t1t2 :: "t1 \<Rightarrow> t2 \<Rightarrow> bool" where
  "t1t2 A C"
| "t1t2 x p \<Longrightarrow> t1t2 y q \<Longrightarrow> t1t2 (B x y) (D p q)"

code_pred [show_modes] t1t2 .

datatype val1 = A | B
datatype val2 = C | D

inductive cast_val :: "val1 \<Rightarrow> val2 \<Rightarrow> bool" where
  "cast_val A C"
| "cast_val B D"

fun cast_val_fun :: "val1 \<Rightarrow> val2" where
  "cast_val_fun A = C"
| "cast_val_fun B = D"

inductive cast_list :: "val1 list \<Rightarrow> val2 list \<Rightarrow> bool" where
  "cast_list [] []"
| "cast_val x y \<Longrightarrow> cast_list xs ys \<Longrightarrow> cast_list (x#xs) (y#ys)"

code_pred [show_modes] cast_list .

values "{x. cast_list [A, B] x}"
values "{x. cast_list x [C, D]}"


inductive cast_fset1 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset1 {||} {||}"
| "cast_val x y \<Longrightarrow> cast_fset1 xs ys \<Longrightarrow> cast_fset1 (finsert x xs) (finsert y ys)"

code_pred [show_modes] cast_fset1 .

(*values "{x. cast_fset1 {|A, B|} x}"*)

inductive cast_fset2 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "\<And>x y. x |\<in>| xs \<Longrightarrow> y |\<in>| ys \<Longrightarrow> cast_val x y \<Longrightarrow>  cast_fset2 xs ys"

code_pred [show_modes] cast_fset2 .

inductive cast_fset3 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset3 x (fimage cast_val_fun x)"

code_pred [show_modes] cast_fset3 .

values "{x. cast_fset3 {|A, B|} x}"

value "sorted_list_of_fset {|A, B|}"

inductive cast_fset4 :: "val1 fset \<Rightarrow> val2 fset \<Rightarrow> bool" where
  "cast_fset4 x (fimage cast_val_fun x)"



(*values "{(x, y). cast_list x y}"*)

datatype val3 = RVal val1 | OVal val2 | SVal "val3 fset"


inductive_cases cast_strict_elim: "cast x t y"
inductive_cases cast_strict_elim2[elim!]: "cast (SetVal t1 x) t2 y"
inductive_cases cast_strict_elim3[elim!]: "cast (SetVal t1 x) t2 (SetVal t2 y)"

thm cast_strict_elim2

schematic_goal q:
  "cast (SetVal (Boolean[?]) (myset {|RequiredVal (BooleanVal True)|})) (Set (Boolean[1])) ?a"
  apply (rule cast_strict_elim3)


inductive_cases cast_strict_elim: "x as! y"



(*
typedef ebool2 = "UNIV :: bool option set" ..

instantiation ebool2 :: errorable
begin

definition "\<bottom> \<equiv> Abs_ebool2 None"

instance ..

end
*)
fun plus_nat where
  "plus_nat (enat x) (enat y) = x + y"
| "plus_nat \<infinity> (enat y) = y"
| "plus_nat (enat x) \<infinity> = x"
| "plus_nat \<infinity> \<infinity> = (\<infinity> :: enat)"

thm enat_def ebool_def
thm infinity_enat_def bot_ebool_def

function neg_val :: "enat \<Rightarrow> enat" where
  "neg_val (Abs_enat (Some a)) = enat a"
| "neg_val (Abs_enat None) = Abs_enat None"
  using enat_def infinity_enat_def apply auto[1]
  apply auto
(*
fun and_val :: "ebool \<Rightarrow> ebool \<Rightarrow> ebool" where
  "and_val (ebool a) (ebool b) = ebool (a \<and> b)"
| "and_val (ebool False) _ = ebool False"
| "and_val _ (ebool False) = ebool False"
| "and_val \<bottom> _ = \<bottom>"
| "and_val _ \<bottom> = \<bottom>"

term obool
fun and_val :: "obool \<Rightarrow> obool \<Rightarrow> obool" where
  "and_val (obool a) (obool b) = obool (a \<and> b)"
| "and_val (obool False) _ = obool False"
| "and_val _ (obool False) = obool False"
| "and_val \<bottom> _ = \<bottom>"
| "and_val _ \<bottom> = \<bottom>"
| "and_val \<epsilon> _ = \<epsilon>"
| "and_val _ \<epsilon> = \<epsilon>"

fun and_val :: "obool \<Rightarrow> obool \<Rightarrow> obool" where
  "and_val (obool a) (obool b) = obool (a \<and> b)"
| "and_val (obool False) _ = obool False"
| "and_val _ (obool False) = obool False"
| "and_val obool.ErrorVal _ = obool.ErrorVal"
| "and_val _ obool.ErrorVal = obool.ErrorVal"
| "and_val obool.VoidVal _ = \<epsilon>"
| "and_val _ \<epsilon> = obool.VoidVal"

value "and_val obool.ErrorVal (obool True)"
value "and_val obool.VoidVal (obool True)"
*)
datatype 'a errorable = Just 'a | Void | Error

type_synonym ebool = "bool errorable"
type_synonym eint = "int errorable"
type_synonym ereal = "real errorable"
type_synonym eunat = "enat errorable"
type_synonym estring = "string errorable"

datatype simple_val =
  NullVal
| BooleanVal ebool
| RealVal ereal
| IntegerVal eint
| UnlimNatVal eunat
| StringVal estring
| AnyVal
| ObjectVal cls oid

datatype val =
  Required simple_val
| Optional simple_val
(*| SetVal "val set"
| OrderedSet "val list"
| Bag "val list"
| Sequence "val list"
*)
inductive cast :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "as!" 55) where
  "NullVal as! BooleanVal Void"
| "NullVal as! RealVal Void"
| "NullVal as! IntegerVal Void"
| "NullVal as! UnlimNatVal Void"
| "NullVal as! StringVal Void"
(*| "c \<in> cls \<Longrightarrow> NullVal as! ObjectVal c ''''"*)
| "IntegerVal (Just x) as! RealVal (Just x)"
| "IntegerVal Void as! RealVal Void"
| "IntegerVal Error as! RealVal Error"
| "UnlimNatVal (Just (enat x)) as! IntegerVal (Just x)"
| "UnlimNatVal (Just \<infinity>) as! IntegerVal Error"
| "UnlimNatVal Void as! IntegerVal Void"
| "UnlimNatVal Error as! IntegerVal Error"
| "UnlimNatVal (Just (enat x)) as! RealVal (Just x)"
| "UnlimNatVal (Just \<infinity>) as! RealVal Error"
| "UnlimNatVal Void as! RealVal Void"
| "UnlimNatVal Error as! RealVal Error"
(*| "\<forall>y. x \<noteq> AnyVal y \<Longrightarrow> x as! AnyVal x"*)
| "x \<noteq> AnyVal \<Longrightarrow> x as! AnyVal"
(*  "c |\<in>| cls \<Longrightarrow> cast cls NullVal (ObjectVal c '''')"
| "cast cls (ObjectVal c i) (ObjectVal c i)"*)

code_pred [show_modes] cast .
(*
inductive_cases cast_strict_elim: "x as! y"
*)
definition cast_eq :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "as" 55) where
  "x as y \<equiv> x = y \<or> x as! y"

instantiation val :: order
begin

definition less_val where
  "less_val \<equiv> cast"

definition less_eq_val where
  "less_eq_val \<equiv> cast_eq"

lemma less_le_not_le_val:
  "x as! y \<longleftrightarrow> x as y \<and> \<not> y as x"
  apply (auto simp add: cast_eq_def)
  apply (erule cast.cases; auto)
  apply (erule cast.cases; simp add: cast.simps)
  done

lemma order_refl_val [iff]:
  "x as x"
  by (simp add: cast_eq_def)

lemma order_trans_val:
  "x as y \<Longrightarrow> y as z \<Longrightarrow> x as z"
  apply (auto simp add: cast_eq_def)
  apply (erule cast.cases; auto simp add: cast.simps)
  done

lemma antisym_val:
  "x as y \<Longrightarrow> y as x \<Longrightarrow> x = y"
  using cast_eq_def less_le_not_le_val by blast

instance
  apply (standard)
  apply (simp add: less_eq_val_def less_le_not_le_val less_val_def)
  apply (simp add: less_eq_val_def)
  apply (metis less_eq_val_def order_trans_val)
  by (simp add: antisym_val less_eq_val_def)

end
(*
inductive cast_either :: "val \<times> val \<Rightarrow> val \<times> val \<Rightarrow> bool" (infix "as*" 55) where
  "x as* x"
| "a = x \<Longrightarrow> b as! y \<Longrightarrow> (a, b) as* (x, y)"
| "a as! x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"

inductive_cases cast_eitherE[elim!]: "(a, b) as* (x, y)"

code_pred [show_modes] cast_either .
*)
(*** Type of Val ************************************************************************)

fun type_of_val :: "val \<Rightarrow> type" ("\<T> _" [75] 75) where
  "\<T> (NullVal) = OclVoid"
| "\<T> (BooleanVal _) = Boolean"
| "\<T> (RealVal _) = Real"
| "\<T> (IntegerVal _) = Integer"
| "\<T> (UnlimNatVal _) = UnlimitedNatural"
| "\<T> (StringVal _) = String"
| "\<T> (AnyVal) = OclAny"
| "\<T> (ObjectVal c _) = ObjectType c"
| "\<T> (ObjectVals c _) = ObjectType c"

(*
fun type_of_val :: "val \<Rightarrow> (oid \<Rightarrow> cls) \<Rightarrow> type" ("\<T> _ _" [75] 75) where
  "\<T> (NullVal) x = VoidType"
| "\<T> (BooleanVal _) x = BooleanType"
| "\<T> (RealVal _) x = RealType"
| "\<T> (IntegerVal _) x = IntegerType"
| "\<T> (UnlimNatVal _) x = UnlimNatType"
| "\<T> (StringVal _) x = StringType"
| "\<T> (AnyVal) x = OclAny"
| "\<T> (ObjectVal i) x = ObjectType (x i)"
*)
lemma type_of_val_less_any_type:
  "(x \<noteq> AnyVal) = (\<T> x < OclAny)"
  apply (cases x)
  using less_type.simps by auto
(*
lemma type_of_val_less_any_type:
  "(x \<noteq> AnyVal \<and> (\<forall>y. x \<noteq> ObjectVal y)) = (\<T> x < OclAny)"
  apply (cases x; auto)
*)
lemma type_of_val_less:
  "x as! y \<Longrightarrow>
   \<T> x < \<T> y"
  by (induct rule: cast.induct; simp add: type_of_val_less_any_type less_type.simps)

lemma type_of_val_less_eq:
  "x as y \<Longrightarrow>
   \<T> x \<le> \<T> y"
  using cast_eq_def less_eq_type_def type_of_val_less by auto
(*
lemma type_of_pair_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   \<T> x \<squnion> \<T> y = \<tau>"
  apply (erule cast_eitherE; simp)
  apply (metis sup.strict_order_iff type_of_val_less)
  by (metis sup.strict_order_iff sup_commut_type type_of_val_less)

lemma type_of_pair_less_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b"
  apply (erule cast_eitherE; simp)
  apply (simp add: less_eq_type_def less_supI2 type_of_val_less)
  apply (simp add: less_eq_type_def less_supI1 type_of_val_less)
  done  
*)
(*** Val for Type ***********************************************************************)

lemma type_of_val_eq_rev:
  "\<T> x = t \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x = y"
  by auto
(*
lemma type_of_val_less_rev:
  "\<T> x < t \<Longrightarrow> t \<noteq> ObjectType c \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as! y"
  apply (induct x; induct t; simp)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  (*using cast.intros type_of_val.simps apply blast*)
  apply (metis cast.intros(6) cast.intros(7) cast.intros(8) errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(7) cast.intros(8) cast.intros(9) errorable.exhaust type_of_val.simps(3))*)
  using cast.intros type_of_val.simps apply blast
  apply (metis cast.intros(13) cast.intros(14) cast.intros(15) cast.intros(16) enat.exhaust errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(14) cast.intros(15) cast.intros(16) cast.intros(17) enat.exhaust errorable.exhaust type_of_val.simps(3))*)
  apply (metis cast.intros(9) cast.intros(10) cast.intros(11) cast.intros(12) enat.exhaust errorable.exhaust type_of_val.simps(4))
  (*apply (metis cast.intros(10) cast.intros(11) cast.intros(12) cast.intros(13) enat.exhaust errorable.exhaust type_of_val.simps(4))*)
  using cast.intros type_of_val.simps apply blast
  (*using cast.intros(18) type_of_val.simps(7) apply blast*)
  done
*)
lemma type_of_val_less_rev:
  "\<T> x < t \<Longrightarrow> \<forall>c. t \<noteq> ObjectType c \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as! y"
  apply (induct x; induct t; simp add: less_type.simps)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  apply auto[1]
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  (*using cast.intros type_of_val.simps apply blast*)
  apply (metis cast.intros(6) cast.intros(7) cast.intros(8) errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(7) cast.intros(8) cast.intros(9) errorable.exhaust type_of_val.simps(3))*)
  using cast.intros type_of_val.simps apply blast
  apply (metis cast.intros(13) cast.intros(14) cast.intros(15) cast.intros(16) enat.exhaust errorable.exhaust type_of_val.simps(3))
  (*apply (metis cast.intros(14) cast.intros(15) cast.intros(16) cast.intros(17) enat.exhaust errorable.exhaust type_of_val.simps(3))*)
  apply (metis cast.intros(9) cast.intros(10) cast.intros(11) cast.intros(12) enat.exhaust errorable.exhaust type_of_val.simps(4))
  (*apply (metis cast.intros(10) cast.intros(11) cast.intros(12) cast.intros(13) enat.exhaust errorable.exhaust type_of_val.simps(4))*)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  done

lemma type_of_val_less_eq_rev:
  "\<T> x \<le> t \<Longrightarrow> \<forall>c. t \<noteq> ObjectType c \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as y"
  by (meson cast_eq_def less_eq_type_def type_of_val_less_rev)

(*** Type System ************************************************************************)
(*
interpretation ocl_type_system: type_system
  "op \<squnion> :: type \<Rightarrow> type \<Rightarrow> type"
  "op \<le> :: type \<Rightarrow> type \<Rightarrow> bool"
  "op < :: type \<Rightarrow> type \<Rightarrow> bool"
  cast_eq
  cast
  type_of_val
  apply (standard)
  apply (simp add: less_le_not_le_val)
  apply (simp add: cast_eq_def)
  using order_trans_val apply blast
  apply (simp add: eq_iff less_eq_val_def)
  apply simp
  apply (simp add: type_of_val_less_eq)
  apply (simp add: type_of_val_less)
  apply simp
  apply (simp add: type_of_val_less_eq_rev)
  apply (simp add: type_of_val_less_rev)
  done
*)
inductive cast_either :: "val \<times> val \<Rightarrow> val \<times> val \<Rightarrow> bool" (infix "as*" 55) where
(*  "x as* x"*)
  "a = x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"
| "a = x \<Longrightarrow> b as! y \<Longrightarrow> (a, b) as* (x, y)"
| "a as! x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"

lemma cast_either_perm:
  "(a, b) as* (x, y) = (b, a) as* (y, x)"
  apply (auto; erule cast_either.cases; elim Pair_inject)
  using cast_either.intros apply auto
  done

lemma type_of_pair_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   \<T> x \<squnion> \<T> y = \<tau>"
  apply (erule cast_either.cases; elim Pair_inject)
  apply simp
  apply (metis sup.strict_order_iff type_of_val_less)
  apply (metis sup.strict_order_iff type_of_val_less sup_commut_type)
  (*apply (metis ocl_type_system.type_of_val_less sup.strict_order_iff)
  apply (metis ocl_type_system.type_of_val_less sup.strict_order_iff sup_commut_type)*)
  done

lemma type_of_pair_less_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b"
  apply (erule cast_either.cases; elim Pair_inject; auto)
  apply (simp add: le_supI2 less_le_not_le_val type_of_val_less_eq)
  apply (simp add: le_supI1 less_le_not_le_val type_of_val_less_eq)
  (*apply (simp add: le_supI2 ocl_type_system.type_of_val_less_eq)
  apply (simp add: le_supI1 ocl_type_system.type_of_val_less_eq)*)
  done  

(*** Misc *******************************************************************************)

lemma type_max_simp:
  "x \<squnion> y = (t :: type) \<Longrightarrow> t \<noteq> OclAny \<Longrightarrow> (x = t \<and> y \<le> t) \<or> (x \<le> t \<and> y = t)"
  using sup_type_def by auto

lemma type_max_simp_elim:
  "x \<squnion> y = (t :: type) \<Longrightarrow>
   (t \<noteq> OclAny) \<Longrightarrow>
   (x = t \<and> y \<le> t \<Longrightarrow> P) \<Longrightarrow>
   (x \<le> t \<and> y = t \<Longrightarrow> P) \<Longrightarrow> P"
  using type_max_simp by blast

lemma type_of_val_eq_rev_elim:
  "\<T> x = t \<Longrightarrow>
   (\<exists>y. \<T> y = t \<and> x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma type_of_val_less_eq_rev_elim:
  "\<T> x \<le> t \<Longrightarrow> \<forall>c. t \<noteq> ObjectType c \<Longrightarrow>
   (\<exists>y. \<T> y = t \<and> x as y \<Longrightarrow> P) \<Longrightarrow> P"
  using type_of_val_less_eq_rev by blast

lemma type_of_pair_eq_rev:
  "\<T> x \<squnion> \<T> y = \<tau> \<Longrightarrow>
   \<tau> \<noteq> OclAny \<Longrightarrow>
   \<forall>c. \<tau> \<noteq> ObjectType c \<Longrightarrow>
   \<exists>a b.
      \<T> a = \<tau> \<and> \<T> b = \<tau> \<and>
      (x, y) as* (a, b)"
  apply (erule type_max_simp_elim)
  apply (simp)
  apply (erule conjE)
  apply (erule type_of_val_less_eq_rev_elim)
  apply simp (* \<forall>c. \<tau> \<noteq> ObjectType c \<Longrightarrow> *)
  apply (erule type_of_val_eq_rev_elim)
  apply (metis cast_either.intros(1) cast_either.intros(2) cast_eq_def)
  apply (erule conjE)
  apply (erule type_of_val_less_eq_rev_elim)
  apply (erule type_of_val_eq_rev_elim)
  apply simp (* \<forall>c. \<tau> \<noteq> ObjectType c \<Longrightarrow> *)
  apply (metis cast_either.intros(1) cast_either.intros(3) cast_eq_def)
  done

lemma cast_either_ex_intros:
  "\<exists>x y. a = P x \<and> b = P y \<or>
         a = P x \<and> b as! P y \<or>
         a as! P x \<and> b = P y \<Longrightarrow>
   \<exists>x y. (a, b) as* (P x, P y)"
  by (meson cast_either.intros(1) cast_either.intros(2) cast_either_perm)
(*  using ocl_type_system.cast_either.intros by blast*)

(*** Specifics **************************************************************************)

lemma boolean_val_exists:
  "\<T> x = Boolean \<Longrightarrow> \<exists>y. x = BooleanVal y"
(*
  apply (rule exE)
  apply (erule type_of_val_eq_rev)
  using cast.simps by auto
*)
  by (cases x; simp)

lemma real_val_exists:
  "\<T> x = Real \<Longrightarrow> \<exists>y. x = RealVal y"
  by (cases x; simp)

lemma integer_val_exists:
  "\<T> x = Integer \<Longrightarrow> \<exists>y. x = IntegerVal y"
  by (cases x; simp)

lemma unlim_nat_val_exists:
  "\<T> x = UnlimitedNatural \<Longrightarrow> \<exists>y. x = UnlimNatVal y"
  by (cases x; simp)

lemma boolean_val_pair_exists:
  "\<T> x \<squnion> \<T> y = Boolean \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (BooleanVal xn, BooleanVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis boolean_val_exists less_eq_type_def type.distinct(51) type_of_val_less_rev)
  apply (metis boolean_val_exists less_eq_type_def type.distinct(51) type_of_val_less_rev)
  (*apply (metis boolean_val_exists cast_eq_def type.distinct(35) type_of_val_less_eq_rev)
  apply (metis boolean_val_exists cast_eq_def type.distinct(35) type_of_val_less_eq_rev)*)
  (*apply (metis boolean_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis boolean_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma real_val_pair_exists:
  "\<T> x \<squnion> \<T> y = Real \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (RealVal xn, RealVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis real_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  apply (metis real_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  (*apply (metis le_less real_val_exists type.distinct(43) type_of_val_less_rev)
  apply (metis le_less real_val_exists type.distinct(43) type_of_val_less_rev)*)
  (*apply (metis real_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis real_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma integer_val_pair_exists:
  "\<T> x \<squnion> \<T> y = Integer \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (IntegerVal xn, IntegerVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis integer_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  apply (metis integer_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  (*apply (metis cast_eq_def integer_val_exists type.distinct(49) type_of_val_less_eq_rev_elim)
  apply (metis cast_eq_def integer_val_exists type.distinct(49) type_of_val_less_eq_rev_elim)*)
  (*apply (metis integer_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis integer_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma unlim_nat_val_pair_exists:
  "\<T> x \<squnion> \<T> y = UnlimitedNatural \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (UnlimNatVal xn, UnlimNatVal yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis unlim_nat_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  apply (metis unlim_nat_val_exists less_eq_type_def type.distinct type_of_val_less_rev)
  (*apply (metis cast_eq_def type.distinct(53) type_of_val_less_eq_rev_elim unlim_nat_val_exists)
  apply (metis cast_eq_def type.distinct(53) type_of_val_less_eq_rev_elim unlim_nat_val_exists)*)
  (*apply (metis unlim_nat_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis unlim_nat_val_exists cast_eq_def type_of_val_less_eq_rev)*)
  done

lemma real_type_le_cases:
  "x \<squnion> y \<le> Real \<Longrightarrow>
   (x \<squnion> y = Real \<Longrightarrow> P) \<Longrightarrow> 
   (x \<squnion> y = Integer \<Longrightarrow> P) \<Longrightarrow>
   (x \<squnion> y = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> 
   (x \<squnion> y = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases x; cases y; simp add: less_eq_type_def less_type.simps sup_type_def)
  by blast
  (*using less_type.elims(2) by blast8*)
  (*by (cases x; cases y; simp add: less_eq_type_def sup_type_def)*)

lemma num_type_cases:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> Real \<Longrightarrow>
   OclVoid < \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = Real \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis dual_order.strict_iff_order real_type_le_cases)

(*** Model ******************************************************************************)

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
      (''name'', String)]),
    (''Car'', fmap_of_list [
      (''color'', String)]),
    (''Company'', fmap_of_list [
      (''name'', String)])]"

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

(*** Data *******************************************************************************)

type_synonym objects = "oid \<rightharpoonup>\<^sub>f cls"
type_synonym attr_vals = "oid \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f val"
(*type_synonym link = "oid list"
type_synonym links = "assoc \<rightharpoonup>\<^sub>f link fset"*)
type_synonym links = "assoc \<rightharpoonup>\<^sub>f (role \<rightharpoonup>\<^sub>f oid) fset"
type_synonym data = "objects \<times> attr_vals \<times> links"
(*
definition linked_objs :: "link fset \<Rightarrow> oid \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> oid fset" where
  "linked_objs link_set obj i j \<equiv> (\<lambda>x. x!j) |`| ffilter (\<lambda>x. x!i = obj) link_set"
*)
(*
definition find_links :: "links \<Rightarrow> oid \<Rightarrow> links" where
  "find_links links obj \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup links assoc of Some link_set \<Rightarrow>
      obj |\<in>| fmran link_set) links"
*)
(*
definition find_links :: "links \<Rightarrow> oid \<Rightarrow> links" where
  "find_links links obj \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup links assoc of Some link_set \<Rightarrow>
      fBex (fmdom link_set) (\<lambda>role.
        case fmlookup link_set role of Some obj2 \<Rightarrow>
          obj = obj2)) links"
*)
(*
definition link_refer_obj :: "(role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> oid \<Rightarrow> bool" where
  "link_refer_obj link_set obj \<equiv>
    fBex (fmdom link_set) (\<lambda>role.
      fmlookup link_set role = Some obj)"

definition find_links :: "links \<Rightarrow> oid \<Rightarrow> links" where
  "find_links links obj \<equiv> fmfilter (\<lambda>assoc.
    case fmlookup links assoc of None \<Rightarrow> False | Some link_set \<Rightarrow>
      link_refer_obj link_set obj) links"

definition find_links2 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> assoc fset" where
  "find_links2 links obj role \<equiv> fmdom (fmfilter (\<lambda>assoc.
    case fmlookup links assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
      case fmlookup ends role of None \<Rightarrow> False | Some obj2 \<Rightarrow>
        obj2 \<noteq> obj) (find_links links obj))"
*)
(*
definition find_link :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> assoc" where
  "find_link links obj role \<equiv> fthe_elem (find_links2 links obj role)"
*)
definition link_set_ok :: "objects \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) fset \<Rightarrow> bool" where
  "link_set_ok objects link_set \<equiv> fBall link_set (\<lambda>x. fmran x |\<subseteq>| fmdom objects)"

inductive data_is_ok :: "data \<Rightarrow> bool" where
  "(* Attribute values defined for existing objects *)
   fmdom attr_vals |\<subseteq>| fmdom objects \<Longrightarrow>
   (* Links defined for existing objects *)
   fBall (fmran links) (link_set_ok objects) \<Longrightarrow>
   data_is_ok (objects, attr_vals, links)"

code_pred [show_modes] data_is_ok .


(*
definition find_link :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> oid option" where
  "find_link links obj role \<equiv>
    fmlookup (fthe_elem (fmran (find_links5 links obj role))) role"
*)

definition objects1 :: "objects" where
  "objects1 \<equiv> fmap_of_list [
    (''Ivan'', ''Person''),
    (''Jhon'', ''Person''),
    (''Car1'', ''Car''),
    (''Car2'', ''Car''),
    (''Car3'', ''Car'')]"

definition attr_val1 :: "attr_vals" where
  "attr_val1 \<equiv> fmap_of_list [
    (''Ivan'', fmap_of_list [
      (''name'', StringVal (Just ''Ivan Ivanov''))]),
      (*(''name'', IntegerValue 1)]),*)
    (''Car1'', fmap_of_list [
      (''color'', StringVal (Just ''White''))])]"

definition links1 :: "links" where
  "links1 \<equiv> fmap_of_list [
    (''PersonCar'', {|
      fmap_of_list [
        (''driver'',''Jhon''),
        (''car'',''Car1'')],
      fmap_of_list [
        (''driver'',''Ivan''),
        (''car'',''Car1'')],
      fmap_of_list [
        (''driver'',''Ivan''),
        (''car'',''Car2'')]|}),
    (''Employment2'', {|
      fmap_of_list [
        (''employee'',''Jhon''),
        (''employer'',''Ivan'')],
      fmap_of_list [
        (''employee'',''Ivan''),
        (''employer'',''Ivan'')]|})]"

definition data1 :: "data" where
  "data1 \<equiv> (objects1, attr_val1, links1)"

definition link_refer_class5 :: "(role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> bool" where
  "link_refer_class5 link obj role \<equiv> fmlookup link role = Some obj"

definition link_refer_role5 :: "(role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> role \<Rightarrow> bool" where
  "link_refer_role5 link role \<equiv> fmlookup link role \<noteq> None"
(*
definition find_links5 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> links" where
  "find_links5 links obj role \<equiv>
    fmmap (\<lambda>link_set. ffilter (\<lambda>link.
      link_refer_role5 link role \<and> link_refer_class5 link obj role) link_set)
    (fmfilter (\<lambda>assoc.
      case fmlookup links assoc of None \<Rightarrow> False | Some link_set \<Rightarrow>
        fBex link_set (\<lambda>link.
          link_refer_role5 link role \<and> link_refer_class5 link obj role)) links)"
*)
definition remove_empty_links where
  "remove_empty_links links \<equiv> fmfilter (\<lambda>assoc.
      case fmlookup links assoc of None \<Rightarrow> False | Some link_set \<Rightarrow>
        link_set \<noteq> fempty) links"

definition find_links5 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> role \<Rightarrow> links" where
  "find_links5 links obj from to \<equiv>
    remove_empty_links
      (fmmap (\<lambda>link_set. ffilter (\<lambda>link.
        link_refer_class5 link obj from \<and> link_refer_role5 link to) link_set) links)"

value "find_assocs5 assocs1 ''Person'' ''driver'' ''car''"
value "find_links5 links1 ''Ivan'' ''driver'' ''car''"


(*** Model & Data ***********************************************************************)

definition attr_vals_is_ok2 where
  "attr_vals_is_ok2 cls_attrs vals \<equiv>
    fBall (fmdom cls_attrs |\<union>| fmdom vals) (\<lambda>prop.
      case (fmlookup cls_attrs prop, fmlookup vals prop)
        of (Some \<tau>, Some v) \<Rightarrow> \<forall>cls obj.
            type_of_val v = \<tau> \<and>
            v \<noteq> ObjectVal cls obj \<and>
            \<tau> \<noteq> ObjectType cls
         | (_, _) \<Rightarrow> False)"

definition attr_vals_is_ok where
  "attr_vals_is_ok attrs objects attr_vals \<equiv>
    fBall (fmdom objects) (\<lambda>obj.
      case (fmlookup objects obj) of Some cls \<Rightarrow>
        case (fmlookup attrs cls, fmlookup attr_vals obj)
          of (None, None) \<Rightarrow> True
           | (None, Some _) \<Rightarrow> False
           | (Some _, None) \<Rightarrow> False
           | (Some cls_attrs, Some vals) \<Rightarrow>
                attr_vals_is_ok2 cls_attrs vals)"
(*
definition link_ok :: "assoc_end list \<Rightarrow> link \<Rightarrow> objects \<Rightarrow> bool" where
  "link_ok ends link objects \<equiv> list_all2 (\<lambda>end obj.
    fmlookup objects obj = Some (assoc_end_class end)) ends link"

definition links_ok :: "assocs \<Rightarrow> links \<Rightarrow> objects \<Rightarrow> bool" where
  "links_ok assocs links objects \<equiv>
    fBall (fmdom links) (\<lambda>assoc.
      case (fmlookup links assoc) of Some link_set \<Rightarrow>
        case (fmlookup assocs assoc) of Some ends \<Rightarrow>
          fBall link_set (\<lambda>link.
            link_ok ends link objects))"
*)

definition link_obj_cls_ok :: "(oid \<rightharpoonup>\<^sub>f cls) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> bool" where
  "link_obj_cls_ok objects ends link \<equiv>
    fBall (fmdom ends |\<union>| fmdom link) (\<lambda>role.
      case (fmlookup ends role) of None \<Rightarrow> False | Some end \<Rightarrow>
        case (fmlookup link role) of None \<Rightarrow> False | Some obj \<Rightarrow>
          fmlookup objects obj = Some (assoc_end_class end))"
(*
definition link_obj_cls_ok :: "(oid \<rightharpoonup>\<^sub>f cls) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> bool" where
  "link_obj_cls_ok objects ends link \<equiv>
    fBall (fmdom ends |\<union>| fmdom link) (\<lambda>role.
      case (fmlookup ends role, fmlookup link role) of (Some end, Some obj) \<Rightarrow>
        fmlookup objects obj = Some (assoc_end_class end) | _ \<Rightarrow> False)"
*)
definition all_roles where
  "all_roles assocs \<equiv> ffUnion (fmran (fmmap fmdom assocs))"
(*
definition links_unique where
  "links_unique objects assocs links \<equiv>
    fBall (all_roles assocs) (\<lambda>role.
      fBall (fmdom objects) (\<lambda>obj.
        case (fmlookup objects obj) of None \<Rightarrow> False | Some cls \<Rightarrow>
          fcard (fmdom (find_assocs5 assocs cls role)) \<le> 1 \<and>
          fcard (fmdom (find_links5 links obj role)) \<le> 1
          (*is_singleton (fset (fmdom (find_assocs5 assocs cls role))) \<and>
          is_singleton (fset (fmdom (find_links5 links obj role)))*) ))"
*)
(* TODO: Check cardinality *)
definition links_ok :: "objects \<Rightarrow> assocs \<Rightarrow> links \<Rightarrow> bool" where
  "links_ok objects assocs links \<equiv>
    (*links_unique objects assocs links \<and>*)
    fBall (fmdom links) (\<lambda>assoc.
      case (fmlookup assocs assoc) of None \<Rightarrow> False | Some ends \<Rightarrow>
        case (fmlookup links assoc) of None \<Rightarrow> False | Some link_set \<Rightarrow> (* It can't be None *)
          fBall link_set (link_obj_cls_ok objects ends))"

value assocs1
value "find_assocs5 assocs1 ''Person'' ''employee''"
value "find_assocs5 assocs1 ''Person'' ''driver''"
value "links_ok objects1 assocs1 links1"
(*
definition assoc_refer_class7 :: "(role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> cls \<Rightarrow> nat" where
  "assoc_refer_class7 ends cls \<equiv>
    fcard (ffilter (\<lambda>role.
      case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
        cls = assoc_end_class end) (fmdom ends))"
*)
(*
definition find_assocs7 :: "assocs \<Rightarrow> cls \<Rightarrow> assocs" where
  "find_assocs7 assocs cls \<equiv>
    fmfilter (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> False | Some ends \<Rightarrow>
        fBex (fmdom ends) (\<lambda>role.
          case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow>
            cls = assoc_end_class end \<and> assoc_refer_class5 ends cls role)) assocs"
*)
(*
term fmmap
definition find_assocs7 :: "assocs \<Rightarrow> cls \<Rightarrow> role list" where
  "find_assocs7 assocs cls \<equiv>
    fmmap (\<lambda>assoc.
      case fmlookup assocs assoc of None \<Rightarrow> fempty | Some ends \<Rightarrow>
        case assoc_refer_class7 ends cls
          of 0 \<Rightarrow> fempty) assocs"
*)
value "find_assocs7 assocs1 ''Person''"

(*
lemma link_refer_obj_then_class:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   link_refer_obj link_set obj \<Longrightarrow>
   assoc_refer_class ends cls"
  apply (simp add: link_obj_cls_ok_def link_refer_obj_def assoc_refer_class_def)
  by (smt fBall_alt_def fBall_funion fBexCI fBexE fmdom_notD option.case_eq_if option.sel)
*)
lemma links_ok_preserv_class:
  "links_ok objects assocs links \<Longrightarrow>

   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = cls \<Longrightarrow>

   fmlookup links assoc = Some link_set \<Longrightarrow>
   link |\<in>| link_set \<Longrightarrow>
   fmlookup link role = Some obj \<Longrightarrow>
   fmlookup objects obj = Some cls2 \<Longrightarrow>

   cls = cls2"
  apply (simp add: links_ok_def)
  apply (smt fBall_alt_def fBall_funion fmdomI link_obj_cls_ok_def option.inject option.simps(5))
  done
(*
lemma links_ok_and_find_links_then_find_assocs:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmdom (find_links links obj) = assocs1 \<Longrightarrow>
   fmdom (find_assocs assocs cls) = assocs2 \<Longrightarrow>
   assocs1 |\<subseteq>| assocs2"
  apply (simp add: links_ok_def)
  apply (simp add: find_assocs_def find_links_def)
  apply (auto)
  apply (metis (no_types, lifting) fbspec fmdom_notD option.case_eq_if)
  apply (smt fBall_alt_def link_refer_obj_then_class option.case_eq_if)
  done
*)
(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   f = (\<lambda>assoc.
      case fmlookup links assoc of None \<Rightarrow> False
         | Some ends \<Rightarrow>
             case fmlookup ends role of None \<Rightarrow> False | Some obj2 \<Rightarrow> obj2 \<noteq> obj) \<Longrightarrow>
   g = (\<lambda>assoc.
         case fmlookup assocs assoc of None \<Rightarrow> False
         | Some ends \<Rightarrow>
             case fmlookup ends role of None \<Rightarrow> False
             | Some end \<Rightarrow> assoc_end_class end \<noteq> cls) \<Longrightarrow>
   f assoc \<Longrightarrow> g assoc"
*)
lemma q11:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   role |\<in>| (fmdom ends |\<union>| fmdom link_set) \<Longrightarrow>
   case fmlookup link_set role of None \<Rightarrow> False | Some obj2 \<Rightarrow> obj2 = obj \<Longrightarrow>
   case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> assoc_end_class end = cls"
  apply (simp add: link_obj_cls_ok_def)
  apply (smt fbspec funionCI option.case_eq_if option.sel)
  done

thm fbspec funionCI option.case_eq_if option.sel

lemma q12:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   (case fmlookup ends role of None \<Rightarrow> False | Some end \<Rightarrow> assoc_end_class end \<noteq> cls) \<Longrightarrow>
   (case fmlookup link_set role of None \<Rightarrow> False | Some obj2 \<Rightarrow> obj2 \<noteq> obj)"
  apply (simp add: link_obj_cls_ok_def)
  apply (smt fBall_funion fbspec fmdom_notD option.case_eq_if option.inject)
  done
(*
lemma q:
  "ffilter P s1 = fs1 \<Longrightarrow>
   ffilter Q s2 = fs2 \<Longrightarrow>
   s1 |\<subseteq>| s2 \<Longrightarrow>
   (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow>
   fs1 |\<subseteq>| fs2"
  apply auto
  done
*)
(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   find_link links obj role = assoc1 \<Longrightarrow>
   find_assoc assocs cls role = assoc2 \<Longrightarrow>
   assoc1 = assoc2"
  apply (simp add: find_link_def find_assoc_def)
  apply (simp add: find_links2_def find_assocs2_def)
*)

lemma w13:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   link_refer_role5 link_set role \<Longrightarrow>
   assoc_refer_role5 ends role"
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: link_refer_role5_def)
  apply (simp add: assoc_refer_role5_def)
  by (metis (no_types, lifting) case_optionE fBall_alt_def fmdomI funion_iff prod_cases3)

lemma w14:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   link_refer_class5 link_set obj role \<Longrightarrow>
   assoc_refer_class5 ends cls role"
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: link_refer_class5_def)
  apply (simp add: assoc_refer_class5_def)
  apply (auto simp add: fBall_alt_def)
  by (smt case_optionE fBexI fBex_cong fBex_triv_one_point1 fmlookup_restrict_fset fmrestrict_fset_dom option.sel option.simps(4) option.simps(5))

lemma w12:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmdom (find_links5 links obj from to) |\<subseteq>| fmdom (find_assocs5 assocs cls from to)"
  apply (simp add: links_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)
  apply (auto simp add: remove_empty_links_def)
  apply (metis (no_types, lifting) case_optionE fbspec fmdomI)
  apply (smt comp_def eq_ffilter fBall_alt_def fempty_ffilter option.case_eq_if w13 w14)
  (*apply (metis (no_types, lifting) fbspec fmdomI option.case_eq_if option.collapse)
  apply (erule case_optionE; simp add: fBall_alt_def)
  apply (smt fBall_alt_def fBexE option.case_eq_if option.simps(5) w13 w14)*)
  done

(*
lemma q:
  "m1 |\<subseteq>| m2 \<Longrightarrow>
   fcard m1 \<le> 1 \<Longrightarrow>
   fcard m2 = 1 \<Longrightarrow>
   fthe_elem m1 = fthe_elem m2"

lemma w121:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fcard (fmdom (find_assocs5 assocs cls role)) \<le>
   fcard (fmdom (find_links5 links obj role))"
  apply (simp add: links_ok_def)
  apply (auto simp add: links_unique_def)
  apply (simp add: find_links5_def find_assocs5_def)
*)
(*
lemma w12:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmdom (find_links5 links obj role) = assoc1 \<Longrightarrow>
   fmdom (find_assocs5 assocs cls role) = assoc2 \<Longrightarrow>
   assoc1 = assoc2"
  apply (simp add: links_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)
  apply auto
  apply (metis (no_types, lifting) fbspec fmdomI funion_iff option.case_eq_if option.collapse)
  apply (erule case_optionE; simp add: fBall_alt_def)
  apply (smt fBall_alt_def fBexE option.case_eq_if option.simps(5) w13 w14)
  apply (metis (no_types, lifting) case_optionE fBall_funion fbspec fmlookup_dom_iff)
  apply (erule case_optionE; simp add: fBall_alt_def)
*)
lemma w15:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   fmlookup link_set role = Some obj2 \<Longrightarrow>
   fmlookup objects obj2 = Some (assoc_end_class end)"
  apply (simp add: link_obj_cls_ok_def)
  by (smt fBall_funion fbspec fmdomI option.case_eq_if option.sel)
(*
lemma w31:
  "links_ok objects assocs links \<Longrightarrow>
   fcard (fdom (find_assocs5 assocs cls role)) \<le> 1"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: find_assocs5_def)

lemma w17:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   ends |\<in>| fmran (find_assocs5 assocs cls role) \<Longrightarrow>
   link_set |\<in>| fmran (find_links5 links obj role) \<Longrightarrow>
   link_obj_cls_ok objects ends link_set"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply auto

lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls role))) = Some ends \<Longrightarrow>
   fmlookup links (fthe_elem (fmdom (find_links5 links obj role))) = Some link_set \<Longrightarrow>
   link_obj_cls_ok objects ends link_set"
*)
(*
definition link_obj_cls_ok :: "(oid \<rightharpoonup>\<^sub>f cls) \<Rightarrow> (role \<rightharpoonup>\<^sub>f assoc_end) \<Rightarrow> (role \<rightharpoonup>\<^sub>f oid) \<Rightarrow> bool" where
  "link_obj_cls_ok objects ends link_set \<equiv>
    fBall (fmdom ends |\<union>| fmdom link_set) (\<lambda>role.
      case (fmlookup ends role) of None \<Rightarrow> False | Some end \<Rightarrow>
        case (fmlookup link_set role) of None \<Rightarrow> False | Some obj \<Rightarrow>
          fmlookup objects obj = Some (assoc_end_class end))"
*)
(*
definition find_assoc :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc assocs cls role \<equiv>
    fmlookup (fthe_elem (fmran (find_assocs5 assocs cls role))) role"
*)

definition find_assoc2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc2 assocs cls from to \<equiv>
    if fcard (fmdom (find_assocs5 assocs cls from to)) = 1 then
      case fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls from to)))
        of None \<Rightarrow> None
         | Some ends \<Rightarrow> fmlookup ends to else None"

definition find_link2 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> role \<Rightarrow> oid fset option" where
  "find_link2 links obj from to \<equiv>
    if fcard (fmdom (find_links5 links obj from to)) = 1 then
      case fmlookup (find_links5 links obj from to)
                    (fthe_elem (fmdom (find_links5 links obj from to)))
        of None \<Rightarrow> None
         | Some link_set \<Rightarrow> Some ((\<lambda>link. the (fmlookup link to)) |`| link_set) else None"

value links1
value "find_links5 links1 ''Ivan'' ''driver'' ''car''"
value "find_link2 links1 ''Ivan'' ''driver'' ''car''"

(*
definition find_assoc2 :: "assocs \<Rightarrow> cls \<Rightarrow> role \<Rightarrow> assoc_end option" where
  "find_assoc2 assocs cls role \<equiv>
    case fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls role)))
      of None \<Rightarrow> None
       | Some ends \<Rightarrow> fmlookup ends role"

definition find_link2 :: "links \<Rightarrow> oid \<Rightarrow> role \<Rightarrow> oid fset" where
  "find_link2 links obj role \<equiv>
    case fmlookup links (fthe_elem (fmdom (find_links5 links obj role)))
      of None \<Rightarrow> fempty
       | Some link_set \<Rightarrow> (\<lambda>link. the (fmlookup link role)) |`| link_set"
*)


value "the_elem {1::nat}"
value "fthe_elem {|1::nat|}"
value "fthe_elem {|1::nat,2|}"

lemma w20:
  "fmdom m1 |\<subseteq>| fmdom m2 \<Longrightarrow>
   fmlookup m1 x \<noteq> None \<Longrightarrow>
   fmlookup m2 x \<noteq> None"
  by (meson fmdom_notD fmdom_notI fset_mp)

lemma w21:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup (find_links5 links obj from to) assoc \<noteq> None \<Longrightarrow>
   fmlookup (find_assocs5 assocs cls from to) assoc \<noteq> None"
  using w12 w20 apply auto
  by (meson fmlookup_dom_iff fset_mp)

lemma fmsubset_dom:
  "f \<subseteq>\<^sub>f g \<Longrightarrow>
   fmdom f |\<subseteq>| fmdom g"
  apply (auto simp add: fmsubset_def map_le_def)
  by (metis domI fmlookup_dom_iff)
(*
lemma q:
  "fBall link_set (link_obj_cls_ok objects ends) \<Longrightarrow>
   link_set2 |\<subseteq>| link_set \<Longrightarrow>
   fBall link_set2 (link_obj_cls_ok objects ends)"
  by blast

lemma q:
  "ends2 \<subseteq>\<^sub>f ends \<Longrightarrow>
   fmdom ends2 |\<subseteq>| fmdom ends"
  by (simp add: fmsubset_dom)
*)
lemma fBall_subset_un:
  "fBall (fmdom ends |\<union>| fmdom link) P \<Longrightarrow>
   fmdom ends2 |\<subseteq>| fmdom ends \<Longrightarrow>
   fBall (fmdom ends2 |\<union>| fmdom link) P"
  by auto

lemma w191:
  "links_ok objects assocs links \<Longrightarrow>
   assocs2 \<subseteq>\<^sub>f assocs \<Longrightarrow>
   fmdom links2 |\<subseteq>| fmdom links \<Longrightarrow>

   (\<forall>assoc. \<exists>link_set2 link_set.
      assoc |\<in>| fmdom links2 \<longrightarrow>
      fmlookup links2 assoc = Some link_set2 \<and>
      fmlookup links assoc = Some link_set \<and>
      link_set2 |\<subseteq>| link_set) \<Longrightarrow>
(*
   assoc |\<in>| fmdom links2 \<Longrightarrow>
   fmlookup links2 assoc = Some link_set2 \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   link_set2 |\<subseteq>| link_set \<Longrightarrow>
*)
   fmdom links2 |\<subseteq>| fmdom assocs2 \<Longrightarrow>
   links_ok objects assocs2 links2"
  apply (frule_tac f="assocs2" in fmsubset_dom)
  apply (simp add: links_ok_def)
  apply (simp add: fmsubset_def map_le_def)
  apply auto
  apply (frule_tac x="x" and A="fmdom links2" and B="fmdom links" in fset_mp)
  apply assumption
  apply (simp add: option.case_eq_if)
  apply auto
  apply (meson fmlookup_dom_iff fset_rev_mp)
  apply (smt domI fbspec fset_rev_mp option.case_eq_if option.sel)
  done


(*
lemma w191:
  "links_ok objects assocs links \<Longrightarrow>
   assocs2 \<subseteq>\<^sub>f assocs \<Longrightarrow>
   links2 \<subseteq>\<^sub>f links \<Longrightarrow>
   fmdom links2 |\<subseteq>| fmdom assocs2 \<Longrightarrow>
   links_ok objects assocs2 links2"
  apply (frule_tac f="assocs2" in fmsubset_dom)
  apply (frule_tac f="links2" in fmsubset_dom)
  apply (simp add: links_ok_def)
  apply (simp add: fmsubset_def map_le_def)
  apply (simp add: fBall_alt_def)
  apply auto
  apply (frule fset_mp)
  apply assumption
  apply (metis (no_types, lifting) domI fmlookup_dom_iff fset_rev_mp option.case_eq_if)
  done
*)
lemma w194:
  "links_ok objects assocs links \<Longrightarrow>
   find_assocs5 assocs cls from to \<subseteq>\<^sub>f assocs"
  by (simp add: find_assocs5_def fmpredI fmpred_filter fmsubset_alt_def)

lemma w1951:
  "links_ok objects assocs links \<Longrightarrow>
   fmdom (find_links5 links obj from to) |\<subseteq>| fmdom links"
  apply (simp add: find_links5_def remove_empty_links_def)
  by fastforce

lemma w1952:
  "links_ok objects assocs links \<Longrightarrow>
   links2 = find_links5 links obj from to \<Longrightarrow>
   assoc |\<in>| fmdom links2 \<Longrightarrow>
   fmlookup links2 assoc = Some link_set2 \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   link_set2 |\<subseteq>| link_set"
  apply (auto simp add: find_links5_def remove_empty_links_def)
  done

lemma w1953:
  "links_ok objects assocs links \<Longrightarrow>
   links2 = find_links5 links obj from to \<Longrightarrow>
   (\<forall>assoc. \<exists>link_set2 link_set.
      assoc |\<in>| fmdom links2 \<longrightarrow>
      fmlookup links2 assoc = Some link_set2 \<and>
      fmlookup links assoc = Some link_set \<and>
      link_set2 |\<subseteq>| link_set)"
  by (meson fmlookup_dom_iff fset_mp w1951 w1952)

lemma w195:
  "links_ok objects assocs links \<Longrightarrow>
   fmdom (find_links5 links obj from to) |\<subseteq>| fmdom links \<and>
   (\<forall>assoc. \<exists>link_set2 link_set.
      assoc |\<in>| fmdom (find_links5 links obj from to) \<longrightarrow>
      fmlookup (find_links5 links obj from to) assoc = Some link_set2 \<and>
      fmlookup (find_links5 links obj from to) assoc = Some link_set \<and>
      link_set2 |\<subseteq>| link_set)"
  by (meson order_refl w1951 w1953)

(*
lemma w195:
  "links_ok objects assocs links \<Longrightarrow>
   find_links5 links obj role \<subseteq>\<^sub>f links"
  by (simp add: find_links5_def fmpredI fmpred_filter fmsubset_alt_def)
*)
thm w12
lemma w19:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   assocs2 = find_assocs5 assocs cls from to \<Longrightarrow>
   links2 = find_links5 links obj from to \<Longrightarrow>
   links_ok objects assocs2 links2"
  apply (frule_tac obj=obj and cls=cls and ?from="from" and ?to="to" in w12)
  apply assumption
  apply (frule_tac cls=cls and ?from="from" and ?to="to" in w194)
  apply (frule_tac obj=obj and ?from="from" and ?to="to" in w195)
  using w191 w1953 by auto
(*  using w191 by blast*)
(*
term is_singleton

lemma w22:
  "links_ok objects assocs links \<Longrightarrow>
   fcard (fmran assocs) = 1 \<Longrightarrow>
   fcard (fmran links) = 1 \<Longrightarrow>
   link_obj_cls_ok objects
      (fthe_elem (fmran assocs))
      (fthe_elem (fmran links))"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)

lemma q:
  "s1 \<subseteq> s2 \<Longrightarrow>
   is_singleton s1 \<Longrightarrow>
   is_singleton s2 \<Longrightarrow>
   the_elem s1 = e1 \<Longrightarrow>
   the_elem s2 = e2 \<Longrightarrow>
   e1 = e2"
  by (metis insert_subset is_singleton_the_elem singletonD)

lemma q:
  "s1 |\<subseteq>| s2 \<Longrightarrow>
   fthe_elem s1 = e1 \<Longrightarrow>
   fthe_elem s2 = e2 \<Longrightarrow>
   e1 = e2"

lemma w61:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   assocs11 = fmdom (find_links5 links obj role) \<Longrightarrow>
   assocs2 = fmdom (find_assocs5 assocs cls role) \<Longrightarrow>
   assoc1 = fthe_elem assocs11 \<Longrightarrow>
   assoc2 = fthe_elem assocs2 \<Longrightarrow>
   assoc1 = assoc2"
  using w12 apply auto
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)

lemma w16:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   link_obj_cls_ok objects
      (fthe_elem (fmran (find_assocs5 assocs cls role)))
      (fthe_elem (fmran (find_links5 links obj role)))"
  apply (simp add: links_ok_def)
  apply (simp add: link_obj_cls_ok_def)
  apply (simp add: find_links5_def find_assocs5_def)
  apply auto
*)
lemma w41:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   fBall link_set (link_obj_cls_ok objects ends)"
  apply (simp add: links_ok_def)
  by (metis (no_types, lifting) fbspec fmdomI option.case_eq_if option.sel)

lemma w42:
  "link_obj_cls_ok objects ends link_set \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   fmlookup link_set role = Some obj \<Longrightarrow>
   fmlookup objects obj = Some (assoc_end_class end)"
  apply (simp add: link_obj_cls_ok_def)
  by (smt fBall_alt_def fmdomI funion_iff option.case_eq_if option.sel)

lemma w43:
  "links_ok objects assocs links \<Longrightarrow>

   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links assoc = Some link_set \<Longrightarrow>

   fBall link_set (\<lambda>link.
    case fmlookup link role of None \<Rightarrow> False | Some obj \<Rightarrow>
      fmlookup objects obj = Some (assoc_end_class end))"
  apply (frule w41)
  apply (assumption)
  apply (assumption)
  apply (simp add: fBall_alt_def link_obj_cls_ok_def)
  using fmdomI by fastforce

lemma w44:
  "links_ok objects assocs links \<Longrightarrow>

   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links assoc = Some link_set \<Longrightarrow>
   objs = (\<lambda>link. the (fmlookup link role)) |`| link_set \<Longrightarrow>

   fBall objs (\<lambda>obj. fmlookup objects obj = Some (assoc_end_class end))"
  by (smt fBallI fbspec fimageE option.case_eq_if w43)

lemma assocs_eq:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   fcard (fmdom (find_assocs5 assocs cls from to)) = 1 \<Longrightarrow>
   fcard (fmdom (find_links5 links obj from to)) = 1 \<Longrightarrow>

   (fthe_elem (fmdom (find_assocs5 assocs cls from to))) =
   (fthe_elem (fmdom (find_links5 links obj from to)))"
  by (metis fcard_seteq le_numeral_extra(4) w12)
(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   fcard (fmdom (find_assocs5 assocs cls role)) = 1 \<Longrightarrow>
   fcard (fmdom (find_links5 links obj role)) = 1 \<Longrightarrow>

   (fthe_elem (fmdom (find_assocs5 assocs cls role))) =
   (fthe_elem (fmdom (find_links5 links obj role))) \<Longrightarrow>

   fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls role))) = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links (fthe_elem (fmdom (find_links5 links obj role))) = Some link_set \<Longrightarrow>
   objs = (\<lambda>link. the (fmlookup link role)) |`| link_set \<Longrightarrow>

   fBall objs (\<lambda>obj. fmlookup objects obj = Some (assoc_end_class end))"
  using w44 apply auto
*)
lemma find_assoc2_rev:
  "find_assoc2 assocs cls from to = Some end \<Longrightarrow>
   \<exists>ends.
     fcard (fmdom (find_assocs5 assocs cls from to)) = 1 \<and>
     fmlookup assocs (fthe_elem (fmdom (find_assocs5 assocs cls from to))) = Some ends \<and>
     fmlookup ends to = Some end"
  apply (simp add: find_assoc2_def)
  by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.exhaust_sel)

lemma find_link2_rev:
  "find_link2 links obj from to = Some objs \<Longrightarrow>
(*   objs \<noteq> fempty \<Longrightarrow>*)
   \<exists>link_set.
     fcard (fmdom (find_links5 links obj from to)) = 1 \<and>
     fmlookup (find_links5 links obj from to)
              (fthe_elem (fmdom (find_links5 links obj from to))) = Some link_set \<and>
     objs = (\<lambda>link. the (fmlookup link to)) |`| link_set"
  apply (simp add: find_link2_def)
  by (smt option.case_eq_if option.collapse option.distinct(1) option.inject)
(*  by (metis (mono_tags, lifting) option.case_eq_if option.collapse)*)
(*
lemma q:
  "fmlookup (f::assocs) (fthe_elem a) = Some x \<Longrightarrow>
   \<exists>q. a = {|q|}"
  apply (simp add: fthe_elem_def the_elem_def)

term fset
lemma q:
  "fthe_elem m1 |\<in>| fmdom assocs \<Longrightarrow>
   is_singleton (fset m1) \<Longrightarrow>
   \<exists>q. m1 = {|q|}"
  by (metis bot_fset.rep_eq finsert.rep_eq fset_inject is_singletonE)

lemma q:
  "m1 |\<subseteq>| m2 \<Longrightarrow>
   fcard m2 \<le> fcard m1 \<Longrightarrow>
   fthe_elem m1 = fthe_elem m2"
  using fcard_seteq apply fastforce

lemma q:
  "m1 |\<subseteq>| m2 \<Longrightarrow>
   is_singleton (fset m1) \<Longrightarrow>
   is_singleton (fset m2) \<Longrightarrow>
   fthe_elem m1 = fthe_elem m2"
  by (metis empty_iff fthe_elem.rep_eq insert_iff insert_subset is_singleton_the_elem less_eq_fset.rep_eq)

lemma q:
  "is_singleton (fset (fmdom (find_assocs5 assocs cls role)))"
  apply (simp add: find_assocs5_def)
  apply (auto)
*)

lemma w18:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   find_assoc2 assocs cls from to = Some end \<Longrightarrow>
   find_link2 links obj from to = Some objs \<Longrightarrow>
   fBall objs (\<lambda>obj. fmlookup objects obj = Some (assoc_end_class end))"
  apply (drule find_assoc2_rev)
  apply (erule exE)
  apply (erule conjE)
  apply (cases "objs = fempty")
  apply auto[1]
  apply (drule find_link2_rev)
  (*apply auto[1]
  apply (erule exE)
  apply (erule conjE)*)
  apply (frule assocs_eq)
  apply (assumption)
  apply (assumption)
  apply auto[1]
  (*by (smt fBallI fBall_alt_def fimageE fimage_cong fimage_eqI fmdomI fset_rev_mp option.sel w1953 w44)*)
  using w44 apply auto
  by (smt fBall_funion fbspec fmdomI fsubset_funion_eq option.collapse option.sel option.simps(4) w1953 w41 w42 w43)
(*  by (smt fBall_alt_def fBall_funion fmdomI fsubset_funion_eq option.collapse option.sel option.simps(4) w15 w1953 w41 w43)*)

(*
lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   (*fmlookup objects obj = Some cls \<Longrightarrow>*)

   fmlookup assocs (find_assoc assocs cls role) = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links (find_link links obj role) = Some link_set \<Longrightarrow>
   fmlookup link_set role = Some obj2 \<Longrightarrow>
   fmlookup objects obj2 = Some cls2a \<Longrightarrow>

   cls2a = assoc_end_class end"
  apply (simp add: links_ok_def)
  apply (simp add: find_assoc_def find_assocs2_def)
  apply (simp add: find_link_def find_links2_def)
*)
(*
TODO: Количество связей правильное
*)
inductive conforms_to_model :: "model \<Rightarrow> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "model_is_ok model \<Longrightarrow>
   data_is_ok data \<Longrightarrow>
   model = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   (* Objects belong to existing classes *)
   fmran objects |\<subseteq>| classes \<Longrightarrow>
   (* Attribute values defined for existing attributes and have right types *)
   attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   (* Links defined for existing associations, have right objects and cardinality *)
   links_ok objects assocs links \<Longrightarrow>
   model \<turnstile> data"

lemma attr_vals_is_ok_then:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   attr_vals_is_ok2 cls_attrs vals"
  apply (simp add: attr_vals_is_ok_def)
  by (metis (no_types, lifting) case_prodD fBall_alt_def fmlookup_dom_iff option.simps(5))

lemma attr_vals_is_ok_then2:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  apply (simp add: attr_vals_is_ok2_def)
  by (smt fBall_funion fbspec fmdomI option.simps(5))

lemma attr_vals_is_ok_then_rev:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   \<exists>cls_attrs vals.
      fmlookup attrs cls = None \<and>
      fmlookup attr_vals obj = None \<or>
      fmlookup attrs cls = Some cls_attrs \<and>
      fmlookup attr_vals obj = Some vals"
  apply (simp add: attr_vals_is_ok_def)
  by (smt case_prod_conv fbspec fmdom_notD not_None_eq option.case_eq_if option.sel)

lemma attr_vals_is_ok_then_rev2:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
    (\<exists>cls_attrs. fmlookup attrs cls = Some cls_attrs) \<longleftrightarrow>
    (\<exists>vals. fmlookup attr_vals obj = Some vals)"
  apply (simp add: attr_vals_is_ok_def)
  by (smt case_prod_conv fbspec fmdom_notD not_None_eq option.case_eq_if option.sel)

lemma attr_vals_is_ok_then2_rev:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<or>
   fmlookup vals prop = Some v \<Longrightarrow>
   \<exists>\<tau> v.
    fmlookup cls_attrs prop = Some \<tau> \<and>
    fmlookup vals prop = Some v \<and>
    type_of_val v = \<tau>"
  apply (simp add: attr_vals_is_ok2_def)
  by (smt fBall_funion fbspec fmdom_notD fmlookup_dom_iff option.case_eq_if option.sel)

lemma model_preserv_type:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  by (meson attr_vals_is_ok_then attr_vals_is_ok_then2)

code_pred [show_modes] conforms_to_model .

(*** Environment Typing *****************************************************************)
(*
type_synonym 'a fenv = "vname \<rightharpoonup>\<^sub>f 'a"

definition fetyping :: "type fenv \<Rightarrow> val fenv \<Rightarrow> bool" (infix "\<turnstile>\<^sub>f" 50) where
  "\<Gamma> \<turnstile>\<^sub>f env \<equiv> fBall (fmdom \<Gamma> |\<union>| fmdom env) (\<lambda>x.
    case (fmlookup \<Gamma> x, fmlookup env x)
      of (Some \<tau>, Some v) \<Rightarrow> type_of_val v = \<tau>
       | (_, _) \<Rightarrow> False)"
*)
definition etyping :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> env \<equiv> \<forall>x.
    case (\<Gamma> x, env x)
      of (Some \<tau>, Some v) \<Rightarrow> type_of_val v = \<tau>
       | (_, _) \<Rightarrow> False"

lemma var_has_type_impies_has_value:
  "\<Gamma> var = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>v. env var = Some v"
  by (smt etyping_def old.prod.case option.case_eq_if option.collapse option.distinct(1))

lemma var_has_value_impies_has_type:
  "env var = Some v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>\<tau>. \<Gamma> var = Some \<tau>"
  by (smt etyping_def old.prod.case option.case_eq_if option.distinct(1) option.expand option.sel)

lemma etyping_preserv_type:
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   \<Gamma> var = Some \<tau> \<Longrightarrow>
   env var = Some v \<Longrightarrow>
   type_of_val v = \<tau>"
  apply (simp add: etyping_def)
  by (smt option.case_eq_if option.sel prod.simps(2))

(*value "[''x''\<mapsto>IntegerType] \<turnstile> [''x''\<mapsto>IntegerVal (Just 1)]"*)
(*
definition object_type_is_ok :: "model \<Rightarrow> type \<Rightarrow> bool" where
  "object_type_is_ok \<M> \<tau> \<equiv>
    \<forall>cls. \<tau> = ObjectType cls \<longrightarrow> cls |\<in>| (fst \<M>)"

definition tenv_classes_ok :: "type env \<Rightarrow> model \<Rightarrow> bool" where
  "tenv_classes_ok \<Gamma> \<M> \<equiv> \<forall>x \<tau>.
    \<Gamma> x = Some \<tau> \<longrightarrow> object_type_is_ok \<M> \<tau>"

definition object_val_is_ok :: "data \<Rightarrow> val \<Rightarrow> bool" where
  "object_val_is_ok data v \<equiv>
    \<forall>cls obj. v = ObjectVal cls obj \<longrightarrow> obj |\<in>| fmdom (fst data)"

definition env_objects_ok :: "val env \<Rightarrow> data \<Rightarrow> bool" where
  "env_objects_ok env data \<equiv> \<forall>x v.
    env x = Some v \<longrightarrow> object_val_is_ok data v"
*)

definition object_val_ok :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok \<tau> v objects \<equiv> \<forall>cls cls2 obj.
    \<tau> = ObjectType cls \<and>
    v = ObjectVal cls2 obj \<longrightarrow>
    fmlookup objects obj = Some cls"

definition object_val_ok_impl :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok_impl \<tau> v objects \<equiv>
    case (\<tau>, v)
      of (ObjectType cls, ObjectVal cls2 obj) \<Rightarrow>
           fmlookup objects obj = Some cls
       | (_, _) \<Rightarrow> True"

lemma object_val_ok_eq [code]:
  "object_val_ok \<tau> v objects = object_val_ok_impl \<tau> v objects"
  apply (simp only: object_val_ok_def object_val_ok_impl_def)
  apply (cases \<tau>; simp)
  apply (cases v; simp)
  done
(*
lemma object_val_ok_true:
  "\<forall>cls cls2 obj.
    \<tau> \<noteq> ObjectType cls \<and>
    v \<noteq> ObjectVal cls2 obj \<Longrightarrow> object_val_ok \<tau> v objects"
  by (simp add: object_val_ok_def)
*)
definition object_vals_ok :: "type env \<Rightarrow> val env \<Rightarrow> objects \<Rightarrow> bool" where
  "object_vals_ok \<Gamma> env objects \<equiv> \<forall>x.
    case (\<Gamma> x, env x) of (Some \<tau>, Some v) \<Rightarrow> object_val_ok \<tau> v objects"
(*
definition object_vals_ok :: "type env \<Rightarrow> val env \<Rightarrow> objects \<Rightarrow> bool" where
  "object_vals_ok \<Gamma> env objects \<equiv> \<forall>x. \<exists>cls obj.
    \<Gamma> x = Some (ObjectType cls) \<and>
    env x = Some (ObjectVal cls obj) \<longrightarrow>
    fmlookup objects obj = Some cls"
*)
inductive etyping2 :: "type env \<times> model \<Rightarrow> val env \<times> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   \<M> \<turnstile> data \<Longrightarrow>
   (*\<M> = (classes, attrs, assocs) \<Longrightarrow>*)
   data = (objects, attr_vals, links) \<Longrightarrow>
   object_vals_ok \<Gamma> env objects \<Longrightarrow>
   (*tenv_classes_ok \<Gamma> \<M> \<Longrightarrow>
   env_objects_ok env data \<Longrightarrow>*)
   (\<Gamma>,\<M>) \<turnstile> (env,data)"

code_pred [show_modes] etyping2 .
(*
definition etyping2 :: "type env \<times> model \<Rightarrow> val env \<times> data \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "etyping2 \<Gamma>_\<M> env_data \<equiv>
    case (\<Gamma>_\<M>, env_data)
      of ((\<Gamma>, (classes, attrs, assocs)), (env, (objects, attr_vals, links))) \<Rightarrow>
          \<Gamma> \<turnstile> env \<and>
          (classes, attrs, assocs) \<turnstile> (objects, attr_vals, links) \<and>
          tenv_classes_ok \<Gamma> (classes, attrs, assocs) \<and>
          env_objects_ok env (objects, attr_vals, links)"
*)
lemma etyping2_preserv_type:
  "(\<Gamma>,\<M>) \<turnstile> (env,data) \<Longrightarrow>
   \<Gamma> var = Some \<tau> \<Longrightarrow>
   env var = Some v \<Longrightarrow>
   \<T> v = \<tau>"
  using etyping2.simps etyping_preserv_type by blast

lemma etyping_preserv_type2:
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   \<T> v = \<tau> \<Longrightarrow>
   \<Gamma>(var\<mapsto>\<tau>) \<turnstile> env(var\<mapsto>v)"
  by (smt etyping_def fun_upd_apply old.prod.case option.case_eq_if option.sel option.simps(3))

(*
    \<Gamma> x = Some (ObjectType cls) \<longrightarrow> cls |\<in>| (fst \<M>)"

definition env_objects_ok :: "val env \<Rightarrow> data \<Rightarrow> bool" where
  "env_objects_ok env data \<equiv> \<forall>x. \<exists>cls obj.
    env x = Some (ObjectVal cls obj) \<longrightarrow> obj |\<in>| fmdom (fst data)"
*)
lemma object_vals_ok_ext:
  "object_vals_ok \<Gamma> env objects \<Longrightarrow>
   object_val_ok \<tau> v objects \<Longrightarrow>
   object_vals_ok (\<Gamma>(var \<mapsto> \<tau>)) (env(var \<mapsto> v)) objects"
  by (simp add: object_val_ok_def object_vals_ok_def)

lemma etyping2_preserv_type2:
  "(\<Gamma>,\<M>) \<turnstile> (env,data) \<Longrightarrow>
   \<T> v = \<tau> \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   object_val_ok \<tau> v objects \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>),\<M>) \<turnstile> (env(var\<mapsto>v),data)"
  by (simp add: etyping2.simps etyping_preserv_type2 object_vals_ok_ext)
(*  using env_objects_ok_def etyping_preserv_type2 tenv_classes_ok_def by auto*)
(*  by (smt etyping2.intros etyping2.simps etyping_def fst_conv fun_upd_apply old.prod.case option.case_eq_if option.sel option.simps(3) snd_conv)*)
(*
lemma q:
  "(\<forall>x cls obj. env x = Some (ObjectVal cls obj) \<longrightarrow> P) \<Longrightarrow>
   env x = Some (ObjectVal cls obj) \<Longrightarrow> P"
  by auto

lemma q:
  "(\<forall>x. \<exists>v. env x = Some v \<longrightarrow>
       (\<exists>cls obj.
           v = ObjectVal cls obj \<longrightarrow>
           P)) \<Longrightarrow>
   env x = Some (ObjectVal cls obj) \<Longrightarrow> P"
  apply (erule allE)
  apply (erule exE)
  apply (erule impE)
*)
lemma etyping2_preserv_class1:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   \<M> \<turnstile> data \<Longrightarrow>
   obj |\<in>| fmdom objects \<Longrightarrow>
   \<exists>cls. fmlookup objects obj = Some cls"
  apply (simp add: conforms_to_model.simps)
  by (simp add: fmlookup_dom_iff)

(*
definition object_val_ok :: "type \<Rightarrow> val \<Rightarrow> objects \<Rightarrow> bool" where
  "object_val_ok \<tau> v objects \<equiv> \<exists>cls obj.
    \<tau> = ObjectType cls \<and>
    v = ObjectVal cls obj \<longrightarrow>
    fmlookup objects obj = Some cls"
*)
(*
lemma q:
  "\<tau> = ObjectType cls \<Longrightarrow>
   v = ObjectVal cls obj \<Longrightarrow>
   object_val_ok \<tau> v objects \<Longrightarrow>
   fmlookup objects obj = Some cls"
  apply (simp add: object_val_ok_def)
*)
lemma etyping2_preserv_class:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   data = (objects, attr_vals, links) \<Longrightarrow>
   (\<Gamma>,\<M>) \<turnstile> (env,data) \<Longrightarrow>
   \<Gamma> x = Some (ObjectType cls) \<Longrightarrow>
   env x = Some (ObjectVal cls obj) \<Longrightarrow>
   (*obj |\<in>| fmdom objects*)
   fmlookup objects obj = Some cls"
  apply (simp add: etyping2.simps conforms_to_model.simps)
  apply (simp add: object_vals_ok_def)
  apply (metis object_val_ok_def option.simps(5))
  done

lemma attr_vals_is_ok2_then_object_val_ok:
  "attr_vals_is_ok2 cls_attrs vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   object_val_ok \<tau> v objects"
  apply (simp add: attr_vals_is_ok2_def)
  apply (simp add: object_val_ok_def)
  by (smt fBall_funion fbspec fmdomI option.simps(5))

lemma attr_vals_is_ok_then_object_val_ok:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   object_val_ok \<tau> v objects"
  by (meson attr_vals_is_ok2_then_object_val_ok attr_vals_is_ok_then)

end

(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Object Model\<close>
theory Object_Model
  imports Finite_Map_Ext "HOL-Library.Extended_Nat" "HOL-Library.Phantom_Type"
begin

text \<open>
  The section defines a generic object model.\<close>

(*** Type Synonyms **********************************************************)

subsection \<open>Type Synonyms\<close>

type_synonym attr = String.literal
type_synonym assoc = String.literal
type_synonym role = String.literal
type_synonym oper = String.literal
type_synonym param = String.literal
type_synonym elit = String.literal

type_synonym 'a enum_type = "('a, String.literal) phantom"

datatype param_dir = In | Out | InOut

type_synonym 'c assoc_end = "'c \<times> nat \<times> enat \<times> bool \<times> bool"
type_synonym 't param_spec = "param \<times> 't \<times> param_dir"
type_synonym ('t, 'e) oper_def = "oper \<times> 't param_spec list \<times> 't \<times> bool \<times> 'e option"
type_synonym ('t, 'e) oper_spec = "'t \<times> ('t, 'e) oper_def"

definition "assoc_end_class :: 'c assoc_end \<Rightarrow> 'c \<equiv> fst"
definition "assoc_end_min :: 'c assoc_end \<Rightarrow> nat \<equiv> fst \<circ> snd"
definition "assoc_end_max :: 'c assoc_end \<Rightarrow> enat \<equiv> fst \<circ> snd \<circ> snd"
definition "assoc_end_ordered :: 'c assoc_end \<Rightarrow> bool \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "assoc_end_unique :: 'c assoc_end \<Rightarrow> bool \<equiv> snd \<circ> snd \<circ> snd \<circ> snd"

definition "oper_context :: ('t, 'e) oper_spec \<Rightarrow> 't \<equiv> fst"
definition "oper_name :: ('t, 'e) oper_spec \<Rightarrow> oper \<equiv> fst \<circ> snd"
definition "oper_params :: ('t, 'e) oper_spec \<Rightarrow> 't param_spec list \<equiv> fst \<circ> snd \<circ> snd"
definition "oper_result :: ('t, 'e) oper_spec \<Rightarrow> 't \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
definition "oper_static :: ('t, 'e) oper_spec \<Rightarrow> bool \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
definition "oper_body :: ('t, 'e) oper_spec \<Rightarrow> 'e option \<equiv> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

definition "param_name ::'t param_spec \<Rightarrow> param \<equiv> fst"
definition "param_type ::'t param_spec \<Rightarrow> 't \<equiv> fst \<circ> snd"
definition "param_dir ::'t param_spec \<Rightarrow> param_dir \<equiv> snd \<circ> snd"

definition "oper_in_params op \<equiv>
  filter (\<lambda>p. param_dir p = In \<or> param_dir p = InOut) (oper_params op)"

definition "oper_out_params op \<equiv>
  filter (\<lambda>p. param_dir p = Out \<or> param_dir p = InOut) (oper_params op)"

subsection \<open>Attributes\<close>

inductive owned_attribute' where
  "\<C> |\<in>| fmdom attributes \<Longrightarrow>
   fmlookup attributes \<C> = Some attrs\<^sub>\<C> \<Longrightarrow>
   fmlookup attrs\<^sub>\<C> attr = Some \<tau> \<Longrightarrow>
   owned_attribute' attributes \<C> attr \<tau>"

inductive attribute_not_closest where
  "owned_attribute' attributes \<D>' attr \<tau>' \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow>
   \<D>' < \<D> \<Longrightarrow>
   attribute_not_closest attributes \<C> attr \<D> \<tau>"

inductive closest_attribute where
  "owned_attribute' attributes \<D> attr \<tau> \<Longrightarrow>
   \<C> \<le> \<D> \<Longrightarrow>
   \<not> attribute_not_closest attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   closest_attribute attributes \<C> attr \<D> \<tau>"

inductive closest_attribute_not_unique where
  "closest_attribute attributes \<C> attr \<D>' \<tau>' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<or> \<tau> \<noteq> \<tau>' \<Longrightarrow>
   closest_attribute_not_unique attributes \<C> attr \<D> \<tau>"

inductive unique_closest_attribute where
  "closest_attribute attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   \<not> closest_attribute_not_unique attributes \<C> attr \<D> \<tau> \<Longrightarrow>
   unique_closest_attribute attributes \<C> attr \<D> \<tau>"

subsection \<open>Association Ends\<close>

inductive role_refer_class where
  "role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   assoc_end_class end = \<C> \<Longrightarrow>
   role_refer_class ends \<C> role"

inductive association_ends' where
  "\<C> |\<in>| classes \<Longrightarrow>
   assoc |\<in>| fmdom associations \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   role_refer_class ends \<C> from \<Longrightarrow>
   role |\<in>| fmdom ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   role \<noteq> from \<Longrightarrow>
   association_ends' classes associations \<C> from role end"

inductive association_ends_not_unique' where
  "association_ends' classes associations \<C> from role end\<^sub>1 \<Longrightarrow>
   association_ends' classes associations \<C> from role end\<^sub>2 \<Longrightarrow>
   end\<^sub>1 \<noteq> end\<^sub>2 \<Longrightarrow>
   association_ends_not_unique' classes associations"

inductive owned_association_end' where
  "association_ends' classes associations \<C> from role end \<Longrightarrow>
   owned_association_end' classes associations \<C> None role end"
| "association_ends' classes associations \<C> from role end \<Longrightarrow>
   owned_association_end' classes associations \<C> (Some from) role end"

inductive association_end_not_closest where
  "owned_association_end' classes associations \<D>' from role end' \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow>
   \<D>' < \<D> \<Longrightarrow>
   association_end_not_closest classes associations \<C> from role \<D> end"

inductive closest_association_end where
  "owned_association_end' classes associations \<D> from role end \<Longrightarrow>
   \<C> \<le> \<D> \<Longrightarrow>
   \<not> association_end_not_closest classes associations \<C> from role \<D> end \<Longrightarrow>
   closest_association_end classes associations \<C> from role \<D> end"

inductive closest_association_end_not_unique where
  "closest_association_end classes associations \<C> from role \<D>' end' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<or> end \<noteq> end' \<Longrightarrow>
   closest_association_end_not_unique classes associations \<C> from role \<D> end"

inductive unique_closest_association_end where
  "closest_association_end classes associations \<C> from role \<D> end \<Longrightarrow>
   \<not> closest_association_end_not_unique classes associations \<C> from role \<D> end \<Longrightarrow>
   unique_closest_association_end classes associations \<C> from role \<D> end"

subsection \<open>Association Classes\<close>

inductive referred_by_association_class'' where
  "fmlookup association_classes \<A> = Some assoc \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   role_refer_class ends \<C> from \<Longrightarrow>
   referred_by_association_class'' association_classes associations \<C> from \<A>"

inductive referred_by_association_class' where
  "referred_by_association_class'' association_classes associations \<C> from \<A> \<Longrightarrow>
   referred_by_association_class' association_classes associations \<C> None \<A>"
| "referred_by_association_class'' association_classes associations \<C> from \<A> \<Longrightarrow>
   referred_by_association_class' association_classes associations \<C> (Some from) \<A>"

inductive association_class_not_closest where
  "referred_by_association_class' association_classes associations \<D>' from \<A> \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow>
   \<D>' < \<D> \<Longrightarrow>
   association_class_not_closest association_classes associations \<C> from \<A> \<D>"

inductive closest_association_class where
  "referred_by_association_class' association_classes associations \<D> from \<A> \<Longrightarrow>
   \<C> \<le> \<D> \<Longrightarrow>
   \<not> association_class_not_closest association_classes associations \<C> from \<A> \<D> \<Longrightarrow>
   closest_association_class association_classes associations \<C> from \<A> \<D>"

inductive closest_association_class_not_unique where
  "closest_association_class association_classes associations \<C> from \<A> \<D>' \<Longrightarrow>
   \<D> \<noteq> \<D>' \<Longrightarrow>
   closest_association_class_not_unique
        association_classes associations \<C> from \<A> \<D>"

inductive unique_closest_association_class where
  "closest_association_class association_classes associations \<C> from \<A> \<D> \<Longrightarrow>
   \<not> closest_association_class_not_unique
        association_classes associations \<C> from \<A> \<D> \<Longrightarrow>
   unique_closest_association_class association_classes associations \<C> from \<A> \<D>"

subsection \<open>Association Class Ends\<close>

inductive association_class_end' where
  "fmlookup association_classes \<A> = Some assoc \<Longrightarrow>
   fmlookup associations assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>
   association_class_end' association_classes associations \<A> role end"

inductive association_class_end_not_unique where
  "association_class_end' association_classes associations \<A> role end' \<Longrightarrow>
   end \<noteq> end' \<Longrightarrow>
   association_class_end_not_unique association_classes associations \<A> role end"

inductive unique_association_class_end where
  "association_class_end' association_classes associations \<A> role end \<Longrightarrow>
   \<not> association_class_end_not_unique
        association_classes associations \<A> role end \<Longrightarrow>
   unique_association_class_end association_classes associations \<A> role end"

subsection \<open>Operations\<close>

inductive any_operation' where
  "op |\<in>| fset_of_list operations \<Longrightarrow>
   oper_name op = name \<Longrightarrow>
   \<tau> \<le> oper_context op \<Longrightarrow>
   list_all2 (\<lambda>\<sigma> param. \<sigma> \<le> param_type param) \<pi> (oper_in_params op) \<Longrightarrow>
   any_operation' operations \<tau> name \<pi> op"

inductive operation' where
  "any_operation' operations \<tau> name \<pi> op \<Longrightarrow>
   \<not> oper_static op \<Longrightarrow>
   operation' operations \<tau> name \<pi> op"

inductive operation_not_unique where
  "operation' operations \<tau> name \<pi> oper' \<Longrightarrow>
   oper \<noteq> oper' \<Longrightarrow>
   operation_not_unique operations \<tau> name \<pi> oper"

inductive unique_operation where
  "operation' operations \<tau> name \<pi> oper \<Longrightarrow>
   \<not> operation_not_unique operations \<tau> name \<pi> oper \<Longrightarrow>
   unique_operation operations \<tau> name \<pi> oper"

inductive operation_defined' where
  "unique_operation operations \<tau> name \<pi> oper \<Longrightarrow>
   operation_defined' operations \<tau> name \<pi>"

inductive static_operation' where
  "any_operation' operations \<tau> name \<pi> op \<Longrightarrow>
   oper_static op \<Longrightarrow>
   static_operation' operations \<tau> name \<pi> op"

inductive static_operation_not_unique where
  "static_operation' operations \<tau> name \<pi> oper' \<Longrightarrow>
   oper \<noteq> oper' \<Longrightarrow>
   static_operation_not_unique operations \<tau> name \<pi> oper"

inductive unique_static_operation where
  "static_operation' operations \<tau> name \<pi> oper \<Longrightarrow>
   \<not> static_operation_not_unique operations \<tau> name \<pi> oper \<Longrightarrow>
   unique_static_operation operations \<tau> name \<pi> oper"

inductive static_operation_defined' where
  "unique_static_operation operations \<tau> name \<pi> oper \<Longrightarrow>
   static_operation_defined' operations \<tau> name \<pi>"

subsection \<open>Literals\<close>

inductive has_literal' where
  "fmlookup literals e = Some lits \<Longrightarrow>
   lit |\<in>| lits \<Longrightarrow>
   has_literal' literals e lit"

(*** Definition *************************************************************)

subsection \<open>Definition\<close>

locale object_model =
  fixes classes :: "'a :: semilattice_sup fset"
    and attributes :: "'a \<rightharpoonup>\<^sub>f attr \<rightharpoonup>\<^sub>f 't :: order"
    and associations :: "assoc \<rightharpoonup>\<^sub>f role \<rightharpoonup>\<^sub>f 'a assoc_end"
    and association_classes :: "'a \<rightharpoonup>\<^sub>f assoc"
    and operations :: "('t, 'e) oper_spec list"
    and literals :: "'a enum_type \<rightharpoonup>\<^sub>f elit fset"
  assumes assoc_end_min_less_eq_max:
    "assoc |\<in>| fmdom associations \<Longrightarrow>
     fmlookup associations assoc = Some ends \<Longrightarrow>
     role |\<in>| fmdom ends  \<Longrightarrow>
     fmlookup ends role = Some end \<Longrightarrow>
     assoc_end_min end \<le> assoc_end_max end"
  assumes association_ends_unique:
    "association_ends' classes associations \<C> from role end\<^sub>1 \<Longrightarrow>
     association_ends' classes associations \<C> from role end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
begin

abbreviation "owned_attribute \<equiv>
  owned_attribute' attributes"

abbreviation "attribute \<equiv>
  unique_closest_attribute attributes"

abbreviation "association_ends \<equiv>
  association_ends' classes associations"

abbreviation "owned_association_end \<equiv>
  owned_association_end' classes associations"

abbreviation "association_end \<equiv>
  unique_closest_association_end classes associations"

abbreviation "referred_by_association_class \<equiv>
  unique_closest_association_class association_classes associations"

abbreviation "association_class_end \<equiv>
  unique_association_class_end association_classes associations"

abbreviation "operation \<equiv>
  unique_operation operations"

abbreviation "operation_defined \<equiv>
  operation_defined' operations"

abbreviation "static_operation \<equiv>
  unique_static_operation operations"

abbreviation "static_operation_defined \<equiv>
  static_operation_defined' operations"

abbreviation "has_literal \<equiv>
  has_literal' literals"

end

lemmas object_model_simps =
  assoc_end_class_def
  assoc_end_min_def
  assoc_end_max_def
  assoc_end_ordered_def
  assoc_end_unique_def
  oper_name_def
  oper_context_def
  oper_params_def
  oper_result_def
  oper_static_def
  oper_body_def
  oper_in_params_def
  oper_out_params_def
  has_literal'.simps

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma (in object_model) attribute_det:
  "attribute \<C> attr \<D>\<^sub>1 \<tau>\<^sub>1 \<Longrightarrow>
   attribute \<C> attr \<D>\<^sub>2 \<tau>\<^sub>2 \<Longrightarrow> \<D>\<^sub>1 = \<D>\<^sub>2 \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (meson closest_attribute_not_unique.intros unique_closest_attribute.cases)

lemma (in object_model) attribute_self_or_inherited:
  "attribute \<C> attr \<D> \<tau> \<Longrightarrow> \<C> \<le> \<D>"
  by (meson closest_attribute.cases unique_closest_attribute.cases)

lemma (in object_model) attribute_closest:
  "attribute \<C> attr \<D> \<tau> \<Longrightarrow>
   owned_attribute \<D>' attr \<tau> \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow> \<not> \<D>' < \<D>"
  by (meson attribute_not_closest.intros closest_attribute.cases
      unique_closest_attribute.cases)


lemma (in object_model) association_end_det:
  "association_end \<C> from role \<D>\<^sub>1 end\<^sub>1 \<Longrightarrow>
   association_end \<C> from role \<D>\<^sub>2 end\<^sub>2 \<Longrightarrow> \<D>\<^sub>1 = \<D>\<^sub>2 \<and> end\<^sub>1 = end\<^sub>2"
  by (meson closest_association_end_not_unique.intros
      unique_closest_association_end.cases)

lemma (in object_model) association_end_self_or_inherited:
  "association_end \<C> from role \<D> end \<Longrightarrow> \<C> \<le> \<D>"
  by (meson closest_association_end.cases unique_closest_association_end.cases)

lemma (in object_model) association_end_closest:
  "association_end \<C> from role \<D> end \<Longrightarrow>
   owned_association_end \<D>' from role end \<Longrightarrow>
   \<C> \<le> \<D>' \<Longrightarrow> \<not> \<D>' < \<D>"
  by (meson association_end_not_closest.intros closest_association_end.cases
      unique_closest_association_end.cases)


lemma (in object_model) association_class_end_det:
  "association_class_end \<A> role end\<^sub>1 \<Longrightarrow>
   association_class_end \<A> role end\<^sub>2 \<Longrightarrow> end\<^sub>1 = end\<^sub>2"
  by (meson association_class_end_not_unique.intros unique_association_class_end.cases)


lemma (in object_model) operation_det:
  "operation \<tau> name \<pi> oper\<^sub>1 \<Longrightarrow>
   operation \<tau> name \<pi> oper\<^sub>2 \<Longrightarrow> oper\<^sub>1 = oper\<^sub>2"
  by (meson operation_not_unique.intros unique_operation.cases)

lemma (in object_model) static_operation_det:
  "static_operation \<tau> name \<pi> oper\<^sub>1 \<Longrightarrow>
   static_operation \<tau> name \<pi> oper\<^sub>2 \<Longrightarrow> oper\<^sub>1 = oper\<^sub>2"
  by (meson static_operation_not_unique.intros unique_static_operation.cases)

(*** Notation ***************************************************************)

subsection \<open>Notation\<close>

datatype ('a, 't, 'e) model_element_spec =
  EnumSpec "'a enum_type" "elit list"
| ClassSpec 'a "attr \<rightharpoonup>\<^sub>f 't"
| AssociationSpec assoc "role \<rightharpoonup>\<^sub>f 'a assoc_end"
| ContextSpec 't "('t, 'e) oper_def list"

datatype ('a, 't, 'e) model_spec =
  ModelSpec (model_spec_elements: "('a, 't, 'e) model_element_spec list")

primrec model_spec_classes where
  "model_spec_classes [] = []"
| "model_spec_classes (x # xs) = (case x
    of ClassSpec cls attrs \<Rightarrow> (cls, attrs) # (model_spec_classes xs)
     | _ \<Rightarrow> (model_spec_classes xs))"

primrec model_spec_assocs where
  "model_spec_assocs [] = []"
| "model_spec_assocs (x # xs) = (case x
    of AssociationSpec assoc ends \<Rightarrow> (assoc, ends) # (model_spec_assocs xs)
     | _ \<Rightarrow> (model_spec_assocs xs))"

primrec model_spec_contexts where
  "model_spec_contexts [] = []"
| "model_spec_contexts (x # xs) = (case x
    of ContextSpec ctx opers \<Rightarrow> (ctx, opers) # (model_spec_contexts xs)
     | _ \<Rightarrow> (model_spec_contexts xs))"

primrec model_spec_enums where
  "model_spec_enums [] = []"
| "model_spec_enums (x # xs) = (case x
    of EnumSpec enm lits \<Rightarrow> (enm, fset_of_list lits) # (model_spec_enums xs)
     | _ \<Rightarrow> (model_spec_enums xs))"

definition "model_spec_attributes m \<equiv>
  fmap_of_list (model_spec_classes (model_spec_elements m))"

definition "model_spec_assoc_ens m \<equiv>
  fmap_of_list (model_spec_assocs (model_spec_elements m))"

definition "model_spec_operations m \<equiv>
  concat (map (\<lambda>ctx. map (\<lambda>op. (fst ctx, op)) (snd ctx))
      (model_spec_contexts (model_spec_elements m)))"

definition "model_spec_enum_literals m \<equiv>
  fmap_of_list (model_spec_enums (model_spec_elements m))"

lemmas object_model_notation_simps =
  model_spec_elements_def
  model_spec_assocs_def
  model_spec_assoc_ens_def
  model_spec_enum_literals_def

nonterminal model_elements and model_element

nonterminal enum_def and enum_literal_defs and enum_literal_def

syntax
  "_enum_def" :: "'a \<Rightarrow> enum_literal_defs \<Rightarrow> model_element" ("enum _ {_}" [1000,0] 0)
  "_enum_literal_defs_single" :: "elit \<Rightarrow> enum_literal_defs" ("_")
  "_enum_literal_defs_cons" :: "elit \<Rightarrow> enum_literal_defs \<Rightarrow> enum_literal_defs" ("_, _")

translations
  "_enum_def name literals" \<rightharpoonup> "CONST EnumSpec name literals"
  "_enum_literal_defs_cons x (y # xs)" \<rightharpoonup> "x # y # xs"
  "_enum_literal_defs_single x" \<rightharpoonup> "[x]"

nonterminal class_defs and class_def
nonterminal attr_defs and attr_def

syntax
  "_class_def" :: "'a \<Rightarrow> attr_defs \<Rightarrow> model_element" ("class _ _" [1000,0] 0)
  "_class_def" :: "'a \<Rightarrow> model_element" ("class _" [1000] 0)
  "_attr_def" :: "'a \<Rightarrow> 'b \<Rightarrow> attr_def" ("_ : _" [1000,1000] 0)
  "_attr_defs_single" :: "attr_def \<Rightarrow> attr_defs" ("_")
  "_attr_defs_cons" :: "attr_def \<Rightarrow> attr_defs \<Rightarrow> attr_defs" ("_ _")

translations
  "_class_def cls attrs" \<rightharpoonup> "CONST ClassSpec cls (CONST fmap_of_list attrs)"
  "_class_def cls" \<rightharpoonup> "CONST ClassSpec cls (CONST fmap_of_list [])"
  "_attr_def x y" \<rightharpoonup> "(x, y)"
  "_attr_defs_single x" \<rightharpoonup> "[x]"
  "_attr_defs_cons x (y # xs)" \<rightharpoonup> "x # y # xs"

nonterminal assoc_defs and assoc_def
nonterminal assoc_end_defs and assoc_end_def

syntax
  "_assoc_def" :: "'a \<Rightarrow> assoc_end_defs \<Rightarrow> model_element" ("association _ _" [1000,100] 10)
  "_assoc_end_defs_single" :: "assoc_end_def \<Rightarrow> assoc_end_defs" ("_")
  "_assoc_end_defs_cons" :: "assoc_end_def \<Rightarrow> assoc_end_defs \<Rightarrow> assoc_end_defs" ("_ _")
  "_assoc_end_def" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> assoc_end_def" ("_ : _ [_.._]" [100,100,100,100] 100)
  "_assoc_end_def_o" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> assoc_end_def" ("_ : _ [_.._] {ordered}" [100,100,100,100] 100)
  "_assoc_end_def_u" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> assoc_end_def" ("_ : _ [_.._] {unique}" [100,100,100,100] 100)
  "_assoc_end_def_ou" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> assoc_end_def" ("_ : _ [_.._] {ordered,unique}" [100,100,100,100] 100)

translations
  "_assoc_def assoc ends" \<rightharpoonup> "CONST AssociationSpec assoc (CONST fmap_of_list ends)"
  "_assoc_end_defs_single x" \<rightharpoonup> "[x]"
  "_assoc_end_defs_cons x (y # xs)" \<rightharpoonup> "x # y # xs"
  "_assoc_end_def name cls lower upper" \<rightharpoonup>
    "(name, cls, lower :: nat, upper :: enat, CONST False, CONST False)"
  "_assoc_end_def_o name cls lower upper" \<rightharpoonup>
    "(name, cls, lower :: nat, upper :: enat, CONST True, CONST False)"
  "_assoc_end_def_u name cls lower upper" \<rightharpoonup>
    "(name, cls, lower :: nat, upper :: enat, CONST False, CONST True)"
  "_assoc_end_def_ou name cls lower upper" \<rightharpoonup>
    "(name, cls, lower :: nat, upper :: enat, CONST True, CONST True)"

nonterminal context_defs and context_def
nonterminal oper_defs and oper_def_const and oper_signature
nonterminal oper_params and oper_param

syntax
  "_oper_param" :: "'a \<Rightarrow> 'a \<Rightarrow> oper_param" ("_ : _")
  "_oper_param_in" :: "'a \<Rightarrow> 'a \<Rightarrow> oper_param" ("in _ : _")
  "_oper_param_out" :: "'a \<Rightarrow> 'a \<Rightarrow> oper_param" ("out _ : _")
  "_oper_param_inout" :: "'a \<Rightarrow> 'a \<Rightarrow> oper_param" ("inout _ : _")
  "_oper_params_nil" :: "oper_params" ("")
  "_oper_params_single" :: "oper_param \<Rightarrow> oper_params" ("_")
  "_oper_params_cons" :: "oper_param \<Rightarrow> oper_params \<Rightarrow> oper_params" ("_, _")

translations
  "_oper_param param ty" \<rightharpoonup> "(param, ty, CONST In)"
  "_oper_param_in param ty" \<rightharpoonup> "(param, ty, CONST In)"
  "_oper_param_out param ty" \<rightharpoonup> "(param, ty, CONST Out)"
  "_oper_param_inout param ty" \<rightharpoonup> "(param, ty, CONST InOut)"
  "_oper_params_nil" \<rightharpoonup> "[]"
  "_oper_params_single x" \<rightharpoonup> "[x]"
  "_oper_params_cons x xs" \<rightharpoonup> "x # xs"

syntax
  "_context_def" :: "'a \<Rightarrow> oper_defs \<Rightarrow> model_element" ("context _ _" [1000,100] 10)
  "_oper_def" :: "oper_signature \<Rightarrow> 'a \<Rightarrow> oper_def_const" ("def : _ = _" [100,100] 100)
  "_oper_def_no_body" :: "oper_signature \<Rightarrow> oper_def_const" ("def : _" [100] 100)
  "_oper_def_static" :: "oper_signature \<Rightarrow> 'a \<Rightarrow> oper_def_const" ("static def : _ = _" [100,100] 100)
  "_oper_def_static_no_body" :: "oper_signature \<Rightarrow> oper_def_const" ("static def : _" [100] 100)
  "_oper_defs_nil" :: "oper_defs" ("")
  "_oper_defs_cons" :: "oper_def_const \<Rightarrow> oper_defs \<Rightarrow> oper_defs" ("_ _")
  "_oper_signature" :: "'a \<Rightarrow> oper_params \<Rightarrow> 'b \<Rightarrow> oper_signature" ("_'(_') : _" [1000,100,100] 100)
  "_oper_signature_no_params" :: "'a \<Rightarrow> 'b \<Rightarrow> oper_signature" ("_'(') : _" [1000,100] 100)

definition "mk_oper_spec op st body \<equiv> (fst op, fst (snd op), snd (snd op), st, body)"

translations
  "_context_def ctx ops" \<rightharpoonup> "CONST ContextSpec ctx ops"
  "_oper_defs_nil" \<rightharpoonup> "[]"
  "_oper_defs_cons x xs" \<rightharpoonup> "x # xs"
  "_oper_def sign body" \<rightharpoonup> "CONST mk_oper_spec sign CONST False (CONST Some body)"
  "_oper_def_no_body sign" \<rightharpoonup> "CONST mk_oper_spec sign CONST False CONST None"
  "_oper_def_static sign body" \<rightharpoonup> "CONST mk_oper_spec sign CONST True (CONST Some body)"
  "_oper_def_static_no_body sign" \<rightharpoonup> "CONST mk_oper_spec sign CONST True (CONST None)"
  "_oper_signature op params ty" \<rightharpoonup> "(op, params, ty)"
  "_oper_signature_no_params op ty" \<rightharpoonup> "(op, [], ty)"

syntax
  "_model" :: "model_elements \<Rightarrow> ('a, 't, 'e) model_spec" ("_" 10)
  "_model_element_single" :: "model_element \<Rightarrow> model_elements" (" _")
  "_model_element_cons" :: "model_element \<Rightarrow> model_elements \<Rightarrow> model_elements" ("_ _")

translations
  "_model xs" \<rightharpoonup> "CONST ModelSpec xs"
  "_model_element_single x" \<rightharpoonup> "[x]"
  "_model_element_cons x (y # xs)" \<rightharpoonup> "x # y # xs"

(*** Code Setup *************************************************************)

subsection \<open>Code Setup\<close>

lemma fmember_code_predI [code_pred_intro]:
  "x |\<in>| xs" if "Predicate_Compile.contains (fset xs) x"
  using that by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

code_pred fmember
  by (simp add: Predicate_Compile.contains_def fmember.rep_eq)

code_pred unique_closest_attribute .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) association_ends' .

code_pred association_ends_not_unique' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) owned_association_end' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) closest_association_end .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool ) closest_association_end_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) unique_closest_association_end .

code_pred unique_closest_association_class .

code_pred association_class_end' .

code_pred association_class_end_not_unique .

code_pred unique_association_class_end .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) any_operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) operation_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) unique_operation .

code_pred operation_defined' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) static_operation' .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) static_operation_not_unique .

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) unique_static_operation .

code_pred static_operation_defined' .

code_pred has_literal' .

end

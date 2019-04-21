(*  Title:       Safe OCL
    Author:      Denis Nikiforov, April 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Type Helpers\<close>
theory OCL_Type_Helpers
  imports OCL_Types
begin

(*** Definition *************************************************************)

section \<open>Definition\<close>

subsection \<open>All Types\<close>

abbreviation between ("_/ = _\<midarrow>_"  [51, 51, 51] 50) where
  "x = y\<midarrow>z \<equiv> y \<le> x \<and> x \<le> z"

inductive any_type\<^sub>N where
  "any_type\<^sub>N (Required \<tau>) False"
| "any_type\<^sub>N (Optional \<tau>) True"

inductive any_type where
  "any_type\<^sub>N \<tau> n \<Longrightarrow>
   any_type (ErrorFree \<tau>) n"
| "any_type\<^sub>N \<tau> n \<Longrightarrow>
   any_type (Errorable \<tau>) n"

text \<open>Set, ordered set, map and tuple types with finite element types are finite.
  However they are too big, so we consider them as infinite types.\<close>

fun finite_type\<^sub>T
and finite_type\<^sub>N where
  "finite_type\<^sub>T OclAny = False"
| "finite_type\<^sub>T OclVoid = True"

| "finite_type\<^sub>T Boolean = True"
| "finite_type\<^sub>T Real = False"
| "finite_type\<^sub>T Integer = False"
| "finite_type\<^sub>T UnlimitedNatural = False"
| "finite_type\<^sub>T String = False"

| "finite_type\<^sub>T (Enum \<E>) = True"
| "finite_type\<^sub>T (ObjectType \<C>) = True"
| "finite_type\<^sub>T (Tuple \<pi>) = False"

| "finite_type\<^sub>T (Collection \<tau>) = False"
| "finite_type\<^sub>T (Set \<tau>) = False"
| "finite_type\<^sub>T (OrderedSet \<tau>) = False"
| "finite_type\<^sub>T (Bag \<tau>) = False"
| "finite_type\<^sub>T (Sequence \<tau>) = False"

| "finite_type\<^sub>T (Map \<tau> \<sigma>) = False"

| "finite_type\<^sub>N (Required \<tau>) = finite_type\<^sub>T \<tau>"
| "finite_type\<^sub>N (Optional \<tau>) = finite_type\<^sub>T \<tau>"

fun finite_type where
  "finite_type (ErrorFree \<tau>) = finite_type\<^sub>N \<tau>"
| "finite_type (Errorable \<tau>) = finite_type\<^sub>N \<tau>"

subsection \<open>Object Types\<close>

inductive object_type\<^sub>T where
  "object_type\<^sub>T (ObjectType \<C>) \<C>"

inductive object_type\<^sub>N where
  "object_type\<^sub>T \<tau> \<C> \<Longrightarrow>
   object_type\<^sub>N (Required \<tau>) \<C> False"
| "object_type\<^sub>T \<tau> \<C> \<Longrightarrow>
   object_type\<^sub>N (Optional \<tau>) \<C> True"

inductive object_type where
  "object_type\<^sub>N \<tau> \<C> n \<Longrightarrow>
   object_type (ErrorFree \<tau>) \<C> n"
| "object_type\<^sub>N \<tau> \<C> n \<Longrightarrow>
   object_type (Errorable \<tau>) \<C> n"

abbreviation "required_object_type \<tau> \<C> \<equiv> object_type \<tau> \<C> False"
abbreviation "optional_object_type \<tau> \<C> \<equiv> object_type \<tau> \<C> True"

subsection \<open>Tuple Types\<close>

inductive tuple_type\<^sub>T where
  "tuple_type\<^sub>T (Tuple \<pi>) \<pi>"

inductive tuple_type\<^sub>N where
  "tuple_type\<^sub>T \<tau> \<pi> \<Longrightarrow>
   tuple_type\<^sub>N (Required \<tau>) \<pi> False"
| "tuple_type\<^sub>T \<tau> \<pi> \<Longrightarrow>
   tuple_type\<^sub>N (Optional \<tau>) \<pi> True"

inductive tuple_type where
  "tuple_type\<^sub>N \<tau> \<pi> n \<Longrightarrow>
   tuple_type (ErrorFree \<tau>) (fmmap ErrorFree \<pi>) n"
| "tuple_type\<^sub>N \<tau> \<pi> n \<Longrightarrow>
   tuple_type (Errorable \<tau>) (fmmap Errorable \<pi>) n"

inductive tuple_type' where
  "tuple_type\<^sub>N \<tau> (fmmap unwrap_errorable_type \<pi>) n \<Longrightarrow>
   \<not> fBex (fmran \<pi>) errorable_type \<Longrightarrow>
   tuple_type' (ErrorFree \<tau>) \<pi> n"
| "tuple_type\<^sub>N \<tau> (fmmap unwrap_errorable_type \<pi>) n \<Longrightarrow>
   fBex (fmran \<pi>) errorable_type \<Longrightarrow>
   tuple_type' (Errorable \<tau>) \<pi> n"

abbreviation "required_tuple_type \<tau> \<pi> \<equiv> tuple_type \<tau> \<pi> False"
abbreviation "optional_tuple_type \<tau> \<pi> \<equiv> tuple_type \<tau> \<pi> True"
abbreviation "required_tuple_type' \<tau> \<pi> \<equiv> tuple_type' \<tau> \<pi> False"
abbreviation "optional_tuple_type' \<tau> \<pi> \<equiv> tuple_type' \<tau> \<pi> True"

subsection \<open>Collection Types\<close>

inductive collection_type\<^sub>T where
  "collection_type\<^sub>T (Collection \<tau>) CollectionKind \<tau>"
| "collection_type\<^sub>T (Set \<tau>) SetKind \<tau>"
| "collection_type\<^sub>T (OrderedSet \<tau>) OrderedSetKind \<tau>"
| "collection_type\<^sub>T (Bag \<tau>) BagKind \<tau>"
| "collection_type\<^sub>T (Sequence \<tau>) SequenceKind \<tau>"

inductive collection_type\<^sub>N where
  "collection_type\<^sub>T \<tau> k \<sigma> \<Longrightarrow>
   collection_type\<^sub>N (Required \<tau>) k \<sigma> False"
| "collection_type\<^sub>T \<tau> k \<sigma> \<Longrightarrow>
   collection_type\<^sub>N (Optional \<tau>) k \<sigma> True"

inductive collection_type where
  "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type (ErrorFree \<tau>) k (ErrorFree \<sigma>) n"
| "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type (Errorable \<tau>) k (Errorable \<sigma>) n"

abbreviation "required_collection_type \<tau> k \<sigma> \<equiv> collection_type \<tau> k \<sigma> False"
abbreviation "optional_collection_type \<tau> k \<sigma> \<equiv> collection_type \<tau> k \<sigma> True"

inductive is_collection_type where
  "collection_type \<tau> _ _ _ \<Longrightarrow>
   is_collection_type \<tau>"

inductive any_collection_type where
  "collection_type \<tau> _ \<sigma> n \<Longrightarrow>
   any_collection_type \<tau> \<sigma> n"

abbreviation "required_any_collection_type \<tau> \<sigma> \<equiv> any_collection_type \<tau> \<sigma> False"
abbreviation "optional_any_collection_type \<tau> \<sigma> \<equiv> any_collection_type \<tau> \<sigma> True"

abbreviation "set_type' \<tau> \<sigma> n \<equiv> collection_type \<tau> SetKind \<sigma> n"
abbreviation "required_set_type' \<tau> \<sigma> \<equiv> collection_type \<tau> SetKind \<sigma> False"
abbreviation "optional_set_type' \<tau> \<sigma> \<equiv> collection_type \<tau> SetKind \<sigma> True"

abbreviation "ordered_set_type \<tau> \<sigma> n \<equiv> collection_type \<tau> OrderedSetKind \<sigma> n"
abbreviation "required_ordered_set_type \<tau> \<sigma> \<equiv> collection_type \<tau> OrderedSetKind \<sigma> False"
abbreviation "optional_ordered_set_type \<tau> \<sigma> \<equiv> collection_type \<tau> OrderedSetKind \<sigma> True"

abbreviation "bag_type \<tau> \<sigma> n \<equiv> collection_type \<tau> BagKind \<sigma> n"
abbreviation "required_bag_type \<tau> \<sigma> \<equiv> collection_type \<tau> BagKind \<sigma> False"
abbreviation "optional_bag_type \<tau> \<sigma> \<equiv> collection_type \<tau> BagKind \<sigma> True"

abbreviation "sequence_type \<tau> \<sigma> n \<equiv> collection_type \<tau> SequenceKind \<sigma> n"
abbreviation "required_sequence_type \<tau> \<sigma> \<equiv> collection_type \<tau> SequenceKind \<sigma> False"
abbreviation "optional_sequence_type \<tau> \<sigma> \<equiv> collection_type \<tau> SequenceKind \<sigma> True"

inductive ordered_collection_type where
  "collection_type \<tau> OrderedSetKind \<sigma> n \<Longrightarrow>
   ordered_collection_type \<tau> \<sigma> n"
| "collection_type \<tau> SequenceKind \<sigma> n \<Longrightarrow>
   ordered_collection_type \<tau> \<sigma> n"

abbreviation "required_ordered_collection_type \<tau> \<sigma> \<equiv>
  ordered_collection_type \<tau> \<sigma> False"
abbreviation "optional_ordered_collection_type \<tau> \<sigma> \<equiv>
  ordered_collection_type \<tau> \<sigma> True"

abbreviation "non_collection_type \<tau> n \<equiv> (\<not> is_collection_type \<tau> \<and> any_type \<tau> n)"


inductive to_single_type where
  "\<not> is_collection_type \<tau> \<Longrightarrow>
   to_single_type \<tau> \<tau>"
| "collection_type \<tau> _ \<sigma> _ \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   to_single_type \<tau> \<rho>"


inductive inner_element_type where
  "collection_type \<tau> _ \<sigma> _ \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   inner_element_type \<tau> \<rho>"


inductive update_element_type\<^sub>T where
  "update_element_type\<^sub>T (Collection _) \<tau> (Collection \<tau>)"
| "update_element_type\<^sub>T (Set _) \<tau> (Set \<tau>)"
| "update_element_type\<^sub>T (OrderedSet _) \<tau> (OrderedSet \<tau>)"
| "update_element_type\<^sub>T (Bag _) \<tau> (Bag \<tau>)"
| "update_element_type\<^sub>T (Sequence _) \<tau> (Sequence \<tau>)"

inductive update_element_type\<^sub>N where
  "update_element_type\<^sub>T \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type\<^sub>N (Required \<tau>) \<sigma> (Required \<rho>)"
| "update_element_type\<^sub>T \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type\<^sub>N (Optional \<tau>) \<sigma> (Optional \<rho>)"

inductive update_element_type where
  "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (ErrorFree \<tau>) (Errorable \<sigma>) (Errorable \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>)"


inductive to_unique_collection_type\<^sub>T where
  "to_unique_collection_type\<^sub>T (Collection \<tau>) (Set \<tau>)"
| "to_unique_collection_type\<^sub>T (Set \<tau>) (Set \<tau>)"
| "to_unique_collection_type\<^sub>T (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection_type\<^sub>T (Bag \<tau>) (Set \<tau>)"
| "to_unique_collection_type\<^sub>T (Sequence \<tau>) (OrderedSet \<tau>)"

inductive to_unique_collection_type\<^sub>N where
  "to_unique_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "to_unique_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

inductive to_unique_collection_type where
  "to_unique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_unique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type (Errorable \<tau>) (Errorable \<sigma>)"


inductive to_nonunique_collection_type\<^sub>T where
  "to_nonunique_collection_type\<^sub>T (Collection \<tau>) (Bag \<tau>)"
| "to_nonunique_collection_type\<^sub>T (Set \<tau>) (Bag \<tau>)"
| "to_nonunique_collection_type\<^sub>T (OrderedSet \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection_type\<^sub>T (Bag \<tau>) (Bag \<tau>)"
| "to_nonunique_collection_type\<^sub>T (Sequence \<tau>) (Sequence \<tau>)"

inductive to_nonunique_collection_type\<^sub>N where
  "to_nonunique_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "to_nonunique_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

inductive to_nonunique_collection_type where
  "to_nonunique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_nonunique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type (Errorable \<tau>) (Errorable \<sigma>)"


inductive to_ordered_collection_type\<^sub>T where
  "to_ordered_collection_type\<^sub>T (Collection \<tau>) (Sequence \<tau>)"
| "to_ordered_collection_type\<^sub>T (Set \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection_type\<^sub>T (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection_type\<^sub>T (Bag \<tau>) (Sequence \<tau>)"
| "to_ordered_collection_type\<^sub>T (Sequence \<tau>) (Sequence \<tau>)"

inductive to_ordered_collection_type\<^sub>N where
  "to_ordered_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "to_ordered_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

inductive to_ordered_collection_type where
  "to_ordered_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_ordered_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type (Errorable \<tau>) (Errorable \<sigma>)"

subsection \<open>Map Types\<close>

inductive map_type\<^sub>T where
  "map_type\<^sub>T (Map \<sigma> \<rho>) \<sigma> \<rho>"

inductive map_type\<^sub>N where
  "map_type\<^sub>T \<tau> \<sigma> \<rho> \<Longrightarrow>
   map_type\<^sub>N (Required \<tau>) \<sigma> \<rho> False"
| "map_type\<^sub>T \<tau> \<sigma> \<rho> \<Longrightarrow>
   map_type\<^sub>N (Optional \<tau>) \<sigma> \<rho> True"

inductive map_type where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) n"

inductive map_type' where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (ErrorFree \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>) n"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) n"

abbreviation "required_map_type \<tau> \<sigma> \<rho> \<equiv> map_type \<tau> \<sigma> \<rho> False"
abbreviation "optional_map_type \<tau> \<sigma> \<rho> \<equiv> map_type \<tau> \<sigma> \<rho> True"
abbreviation "required_map_type' \<tau> \<sigma> \<rho> \<equiv> map_type' \<tau> \<sigma> \<rho> False"
abbreviation "optional_map_type' \<tau> \<sigma> \<rho> \<equiv> map_type' \<tau> \<sigma> \<rho> True"

subsection \<open>Iterable Types\<close>

inductive iterable_type where
  "collection_type \<tau> _ \<sigma> n \<Longrightarrow>
   iterable_type \<tau> \<sigma> n"
| "map_type \<tau> \<sigma> _ n \<Longrightarrow>
   iterable_type \<tau> \<sigma> n"

abbreviation "required_iterable_type \<tau> \<sigma> \<equiv> iterable_type \<tau> \<sigma> False"
abbreviation "optional_iterable_type \<tau> \<sigma> \<equiv> iterable_type \<tau> \<sigma> True"

inductive any_iterable_type where
  "iterable_type \<tau> _ n \<Longrightarrow> any_iterable_type \<tau> n"

inductive is_iterable_type where
  "iterable_type \<tau> _ _ \<Longrightarrow> is_iterable_type \<tau>"

abbreviation "non_iterable_type \<tau> n \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type \<tau> n)"

abbreviation "required_non_iterable_type \<tau> \<equiv> non_iterable_type \<tau> False"
abbreviation "optional_non_iterable_type \<tau> \<equiv> non_iterable_type \<tau> True"

subsection \<open>Nullable and Null-free Types\<close>

fun required_type\<^sub>N where
  "required_type\<^sub>N (Required \<tau>) = True"
| "required_type\<^sub>N (Optional \<tau>) = False"

fun required_type where
  "required_type (ErrorFree \<tau>) = required_type\<^sub>N \<tau>"
| "required_type (Errorable \<tau>) = required_type\<^sub>N \<tau>"

abbreviation "optional_type\<^sub>N \<tau> \<equiv> \<not> required_type\<^sub>N \<tau>"
abbreviation "optional_type \<tau> \<equiv> \<not> required_type \<tau>"

fun to_required_type\<^sub>N where
  "to_required_type\<^sub>N (Required \<tau>) = Required \<tau>"
| "to_required_type\<^sub>N (Optional \<tau>) = Required \<tau>"

abbreviation "to_required_type \<equiv> map_errorable to_required_type\<^sub>N"

(* Is it realy required? Maybe it better to check types intersection? *)
fun to_optional_type_nested\<^sub>T
and to_optional_type_nested\<^sub>N where
  "to_optional_type_nested\<^sub>T OclAny = OclAny"
| "to_optional_type_nested\<^sub>T OclVoid = OclVoid"

| "to_optional_type_nested\<^sub>T Boolean = Boolean"
| "to_optional_type_nested\<^sub>T Real = Real"
| "to_optional_type_nested\<^sub>T Integer = Integer"
| "to_optional_type_nested\<^sub>T UnlimitedNatural = UnlimitedNatural"
| "to_optional_type_nested\<^sub>T String = String"

| "to_optional_type_nested\<^sub>T (Enum \<E>) = Enum \<E>"
| "to_optional_type_nested\<^sub>T (ObjectType \<C>) = ObjectType \<C>"
| "to_optional_type_nested\<^sub>T (Tuple \<pi>) =
      Tuple (fmmap to_optional_type_nested\<^sub>N \<pi>)"

| "to_optional_type_nested\<^sub>T (Collection \<tau>) =
      Collection (to_optional_type_nested\<^sub>N \<tau>)"
| "to_optional_type_nested\<^sub>T (Set \<tau>) =
      Set (to_optional_type_nested\<^sub>N \<tau>)"
| "to_optional_type_nested\<^sub>T (OrderedSet \<tau>) =
      OrderedSet (to_optional_type_nested\<^sub>N \<tau>)"
| "to_optional_type_nested\<^sub>T (Bag \<tau>) =
      Bag (to_optional_type_nested\<^sub>N \<tau>)"
| "to_optional_type_nested\<^sub>T (Sequence \<tau>) =
      Sequence (to_optional_type_nested\<^sub>N \<tau>)"

| "to_optional_type_nested\<^sub>T (Map \<tau> \<sigma>) =
      Map (to_optional_type_nested\<^sub>N \<tau>) (to_optional_type_nested\<^sub>N \<sigma>)"

| "to_optional_type_nested\<^sub>N (Required \<tau>) = Optional (to_optional_type_nested\<^sub>T \<tau>)"
| "to_optional_type_nested\<^sub>N (Optional \<tau>) = Optional (to_optional_type_nested\<^sub>T \<tau>)"

abbreviation "to_optional_type_nested \<equiv> map_errorable to_optional_type_nested\<^sub>N"

(*** Misc Properties ********************************************************)

section \<open>Misc Properties\<close>

lemma ex_any_type_simps:
  "Ex (any_type (ErrorFree \<tau>)) = (\<exists>n. any_type\<^sub>N \<tau> n)"
  "Ex (any_type (Errorable \<tau>)) = (\<exists>n. any_type\<^sub>N \<tau> n)"
  by (auto simp: any_type.simps)


lemma tuple_type_implies_tuple_type':
  "tuple_type \<tau> \<pi> n \<Longrightarrow> \<pi> \<noteq> fmempty \<Longrightarrow> tuple_type' \<tau> \<pi> n"
  apply (erule tuple_type.cases;
         simp add: tuple_type'.simps fmap.map_comp fmap.map_id0)
  using not_fmempty_eq_fmran_not_fempty by fastforce

lemma tuple_type'_implies_ex_tuple_type:
  "tuple_type' \<tau> \<pi> n \<Longrightarrow> \<exists>\<xi>. tuple_type \<tau> \<xi> n"
  by (erule tuple_type'.cases; auto simp add: tuple_type.simps)

lemma tuple_type\<^sub>T_sup:
  "tuple_type\<^sub>T \<tau> \<pi> \<Longrightarrow>
   tuple_type\<^sub>T \<sigma> \<xi> \<Longrightarrow>
   tuple_type\<^sub>T (\<tau> \<squnion> \<sigma>) (fmmerge (\<squnion>) \<pi> \<xi>)"
  for \<tau> \<sigma> :: "('a :: semilattice_sup) type"
  by (simp add: tuple_type\<^sub>T.simps)

lemma tuple_type\<^sub>N_sup:
  "tuple_type\<^sub>N \<tau> \<pi> n \<Longrightarrow>
   tuple_type\<^sub>N \<sigma> \<xi> n \<Longrightarrow>
   tuple_type\<^sub>N (\<tau> \<squnion> \<sigma>) (fmmerge (\<squnion>) \<pi> \<xi>) n"
  for \<tau> \<sigma> :: "('a :: semilattice_sup) type\<^sub>N"
  by (auto simp add: tuple_type\<^sub>N.simps tuple_type\<^sub>T.simps)

(* TODO: Show a concrete value of \<pi> *)
lemma tuple_type_sup:
  "tuple_type \<tau> \<pi> n \<Longrightarrow>
   tuple_type \<sigma> \<xi> n \<Longrightarrow>
   \<exists>\<pi>. tuple_type (\<tau> \<squnion> \<sigma>) \<pi> n"
  for \<tau> \<sigma> :: "('a :: semilattice_sup) type\<^sub>N\<^sub>E"
  by (cases \<tau>; cases \<sigma>; auto simp add: tuple_type.simps
      tuple_type\<^sub>N.simps tuple_type\<^sub>T.simps)


lemma collection_type_left_simps:
  "collection_type (ErrorFree \<tau>) k \<sigma> n =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "collection_type (Errorable \<tau>) k \<sigma> n =
   (\<exists>\<rho>. \<sigma> = Errorable \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "Ex (collection_type (ErrorFree \<tau>) k \<sigma>) =
   (\<exists>\<rho> n. \<sigma> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "Ex (collection_type (Errorable \<tau>) k \<sigma>) =
   (\<exists>\<rho> n. \<sigma> = Errorable \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  by (auto simp: collection_type.simps) auto

lemma collection_type_right_simps:
  "collection_type \<tau> k (ErrorFree \<sigma>) n =
   (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  "collection_type \<tau> k (Errorable \<sigma>) n =
   (\<exists>\<rho>. \<tau> = Errorable \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  by (auto simp: collection_type.simps)

text \<open>
  The first argument gets simpler, so the following simplification rules
  does not get stuck.\<close>

lemma to_single_type_left_simps:
  "to_single_type (ErrorFree \<tau>) \<sigma> =
   ((\<not> is_collection_type (ErrorFree \<tau>) \<and> (ErrorFree \<tau>) = \<sigma>) \<or>
    (\<exists>k \<upsilon> n. collection_type (ErrorFree \<tau>) k \<upsilon> n \<and> to_single_type \<upsilon> \<sigma>))"
  "to_single_type (Errorable \<tau>) \<sigma> =
   ((\<not> is_collection_type (Errorable \<tau>) \<and> (Errorable \<tau>) = \<sigma>) \<or>
    (\<exists>k \<upsilon> n. collection_type (Errorable \<tau>) k \<upsilon> n \<and> to_single_type \<upsilon> \<sigma>))"
  by (subst to_single_type.simps; auto)+


lemma collection_type_sup:
  "collection_type \<tau> k \<rho> n \<Longrightarrow>
   collection_type \<sigma> k \<upsilon> n \<Longrightarrow>
   collection_type (\<tau> \<squnion> \<sigma>) k (\<rho> \<squnion> \<upsilon>) n"
  by (auto simp add: collection_type.simps
      collection_type\<^sub>N.simps collection_type\<^sub>T.simps)


lemma collection_type_non_collection_type_distinct:
  "any_collection_type \<tau> \<sigma> n1 \<Longrightarrow> non_collection_type \<tau> n2 \<Longrightarrow> False"
  by (auto simp add: any_collection_type.simps is_collection_type.simps)

lemma collection_type_and_map_type_distinct:
  "collection_type \<tau> k \<sigma> n\<^sub>1 \<Longrightarrow> map_type \<tau> \<rho> \<upsilon> n\<^sub>2 \<Longrightarrow> False"
  by (auto simp: collection_type.simps collection_type\<^sub>N.simps
      collection_type\<^sub>T.simps map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)

lemma to_nonunique_collection_type_and_map_type_distinct:
  "to_nonunique_collection_type \<tau> \<sigma> \<Longrightarrow> map_type \<tau> \<rho> \<upsilon> n\<^sub>2 \<Longrightarrow> False"
  by (auto simp: to_nonunique_collection_type.simps
      to_nonunique_collection_type\<^sub>N.simps to_nonunique_collection_type\<^sub>T.simps
      map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)


lemma map_type_implies_map_type':
  "map_type \<tau> \<sigma> \<rho> n \<Longrightarrow> map_type' \<tau> \<sigma> \<rho> n"
  by (erule map_type.cases; simp add: map_type'.simps)

lemma map_type'_implies_ex_map_type:
  "map_type' \<tau> \<sigma> \<rho> n \<Longrightarrow> \<exists>\<upsilon> \<phi>. map_type \<tau> \<upsilon> \<phi> n"
  by (erule map_type'.cases; auto simp add: map_type.simps)

lemma map_type_sup:
  "map_type \<tau> \<rho> \<phi> n \<Longrightarrow>
   map_type \<sigma> \<upsilon> \<psi> n \<Longrightarrow>
   map_type (\<tau> \<squnion> \<sigma>) (\<rho> \<squnion> \<upsilon>) (\<phi> \<squnion> \<psi>) n"
  for \<tau> \<sigma> \<rho> \<upsilon> :: "('a :: semilattice_sup) type\<^sub>N\<^sub>E"
  apply (cases \<rho>; cases \<phi>)
  by (auto simp add: map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)

lemma map_type'_sup:
  "map_type' \<tau> \<rho> \<phi> n \<Longrightarrow>
   map_type \<sigma> \<upsilon> \<psi> n \<Longrightarrow>
   map_type' (\<tau> \<squnion> \<sigma>) (\<rho> \<squnion> \<upsilon>) (\<phi> \<squnion> \<psi>) n"
  for \<tau> \<sigma> \<rho> \<upsilon> :: "('a :: semilattice_sup) type\<^sub>N\<^sub>E"
  apply (cases \<rho>; cases \<phi>)
  by (auto simp add: map_type'.simps map_type.simps
      map_type\<^sub>N.simps map_type\<^sub>T.simps)


lemmas ocl_type_helper_simps =
  any_type\<^sub>N.simps
  any_type.simps
  ex_any_type_simps
  collection_type\<^sub>T.simps
  collection_type\<^sub>N.simps
  collection_type_left_simps
  collection_type_right_simps
  any_collection_type.simps
  to_unique_collection_type\<^sub>T.simps
  to_unique_collection_type\<^sub>N.simps
  to_unique_collection_type.simps
  to_nonunique_collection_type\<^sub>T.simps
  to_nonunique_collection_type\<^sub>N.simps
  to_nonunique_collection_type.simps
  is_collection_type.simps
  to_single_type_left_simps
  update_element_type\<^sub>T.simps
  update_element_type\<^sub>N.simps
  update_element_type.simps
  map_type\<^sub>T.simps
  map_type\<^sub>N.simps
  map_type.simps
  iterable_type.simps
  is_iterable_type.simps

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma tuple_type\<^sub>T_det:
  "tuple_type\<^sub>T \<tau> \<pi>\<^sub>1 \<Longrightarrow>
   tuple_type\<^sub>T \<tau> \<pi>\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2"
  "tuple_type\<^sub>T \<tau>\<^sub>1 \<pi> \<Longrightarrow>
   tuple_type\<^sub>T \<tau>\<^sub>2 \<pi> \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: tuple_type\<^sub>T.simps)

lemma tuple_type\<^sub>N_det:
  "tuple_type\<^sub>N \<tau> \<pi>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   tuple_type\<^sub>N \<tau> \<pi>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<and>  n\<^sub>1 =  n\<^sub>2"
  "tuple_type\<^sub>N \<tau>\<^sub>1 \<pi> n \<Longrightarrow>
   tuple_type\<^sub>N \<tau>\<^sub>2 \<pi> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: tuple_type\<^sub>N.simps tuple_type\<^sub>T_det)

lemma tuple_type_det:
  "tuple_type \<tau> \<pi>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   tuple_type \<tau> \<pi>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<pi>\<^sub>1 = \<pi>\<^sub>2 \<and>  n\<^sub>1 =  n\<^sub>2"
  "tuple_type' \<tau>\<^sub>1 \<pi> n \<Longrightarrow>
   tuple_type' \<tau>\<^sub>2 \<pi> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim tuple_type.cases)
  using tuple_type\<^sub>N_det(1) apply blast+
  apply (elim tuple_type'.cases)
  using tuple_type\<^sub>N_det(2) by blast+


lemma collection_type\<^sub>T_det:
  "collection_type\<^sub>T \<tau> k\<^sub>1 \<sigma>\<^sub>N \<Longrightarrow>
   collection_type\<^sub>T \<tau> k\<^sub>2 \<rho>\<^sub>N \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>N = \<rho>\<^sub>N"
  "collection_type\<^sub>T \<tau>\<^sub>1 k \<sigma>\<^sub>N \<Longrightarrow>
   collection_type\<^sub>T \<tau>\<^sub>2 k \<sigma>\<^sub>N \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: collection_type\<^sub>T.simps)

lemma collection_type\<^sub>N_det:
  "collection_type\<^sub>N \<tau>\<^sub>N k\<^sub>1 \<sigma>\<^sub>N n\<^sub>1 \<Longrightarrow>
   collection_type\<^sub>N \<tau>\<^sub>N k\<^sub>2 \<rho>\<^sub>N n\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>N = \<rho>\<^sub>N \<and> n\<^sub>1 = n\<^sub>2"
  "collection_type\<^sub>N \<tau>\<^sub>N\<^sub>1 k \<sigma>\<^sub>N n \<Longrightarrow>
   collection_type\<^sub>N \<tau>\<^sub>N\<^sub>2 k \<sigma>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>N\<^sub>1 = \<tau>\<^sub>N\<^sub>2"
  by (auto simp add: collection_type\<^sub>N.simps collection_type\<^sub>T_det)

lemma collection_type_det:
  "collection_type \<tau> k\<^sub>1 \<sigma>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   collection_type \<tau> k\<^sub>2 \<sigma>\<^sub>2 n\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "collection_type \<tau>\<^sub>1 k \<sigma> n \<Longrightarrow>
   collection_type \<tau>\<^sub>2 k \<sigma> n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim collection_type.cases; simp add: collection_type\<^sub>N_det(1))
  by (elim collection_type.cases; simp add: collection_type\<^sub>N_det(2))

lemma any_collection_type_det:
  "any_collection_type \<tau> \<sigma>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   any_collection_type \<tau> \<sigma>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  by (elim any_collection_type.cases; simp add: collection_type_det(1))


lemma to_single_type_det:
  "to_single_type \<tau> \<sigma> \<Longrightarrow>
   to_single_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (induct rule: to_single_type.induct)
  apply (erule to_single_type.cases; simp add: is_collection_type.intros)
  using collection_type_det(1) is_collection_type.intros to_single_type.simps by blast

lemma inner_element_type_det:
  "inner_element_type \<tau> \<sigma> \<Longrightarrow>
   inner_element_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  unfolding inner_element_type.simps
  using inner_element_type.simps collection_type_det to_single_type_det by blast


lemma update_element_type\<^sub>T_det:
  "update_element_type\<^sub>T \<tau> \<sigma>\<^sub>N \<rho> \<Longrightarrow>
   update_element_type\<^sub>T \<tau> \<sigma>\<^sub>N \<upsilon> \<Longrightarrow> \<rho> = \<upsilon>"
  by (auto simp: update_element_type\<^sub>T.simps)

lemma update_element_type\<^sub>N_det:
  "update_element_type\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N \<rho>\<^sub>N \<Longrightarrow>
   update_element_type\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N \<upsilon>\<^sub>N \<Longrightarrow> \<rho>\<^sub>N = \<upsilon>\<^sub>N"
  by (auto simp: update_element_type\<^sub>N.simps update_element_type\<^sub>T_det)

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<upsilon> \<Longrightarrow> \<rho> = \<upsilon>"
  by (auto simp: update_element_type.simps update_element_type\<^sub>N_det)


lemma to_unique_collection_type\<^sub>T_det:
  "to_unique_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type\<^sub>T \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_unique_collection_type\<^sub>T.simps)

lemma to_unique_collection_type\<^sub>N_det:
  "to_unique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type\<^sub>N \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_unique_collection_type\<^sub>N.simps to_unique_collection_type\<^sub>T_det)

lemma to_unique_collection_type_det:
  "to_unique_collection_type \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_unique_collection_type.simps to_unique_collection_type\<^sub>N_det)


lemma to_nonunique_collection_type\<^sub>T_det:
  "to_nonunique_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type\<^sub>T \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_nonunique_collection_type\<^sub>T.simps)

lemma to_nonunique_collection_type\<^sub>N_det:
  "to_nonunique_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type\<^sub>N \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_nonunique_collection_type\<^sub>N.simps to_nonunique_collection_type\<^sub>T_det)

lemma to_nonunique_collection_type_det:
  "to_nonunique_collection_type \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_nonunique_collection_type.simps to_nonunique_collection_type\<^sub>N_det)


lemma to_ordered_collection_type\<^sub>T_det:
  "to_ordered_collection_type\<^sub>T \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type\<^sub>T \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_ordered_collection_type\<^sub>T.simps)

lemma to_ordered_collection_type\<^sub>N_det:
  "to_ordered_collection_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type\<^sub>N \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_ordered_collection_type\<^sub>N.simps to_ordered_collection_type\<^sub>T_det)

lemma to_ordered_collection_type_det:
  "to_ordered_collection_type \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (auto simp: to_ordered_collection_type.simps to_ordered_collection_type\<^sub>N_det)


lemma map_type\<^sub>T_det:
  "map_type\<^sub>T \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 \<Longrightarrow>
   map_type\<^sub>T \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2"
  "map_type\<^sub>T \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N \<Longrightarrow>
   map_type\<^sub>T \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: map_type\<^sub>T.simps)

lemma map_type\<^sub>N_det:
  "map_type\<^sub>N \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 \<Longrightarrow>
   map_type\<^sub>N \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "map_type\<^sub>N \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow>
   map_type\<^sub>N \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (auto simp add: map_type\<^sub>N.simps map_type\<^sub>T_det)

lemma map_type_det:
  "map_type \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 \<Longrightarrow>
   map_type \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  "map_type' \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow>
   map_type' \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N n \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (elim map_type.cases; simp add: map_type\<^sub>N_det(1))
  by (elim map_type'.cases; simp add: map_type\<^sub>N_det(2))


lemma iterable_type_det:
  "iterable_type \<tau> \<sigma> n\<^sub>1 \<Longrightarrow>
   iterable_type \<tau> \<rho> n\<^sub>2 \<Longrightarrow> \<sigma> = \<rho> \<and> n\<^sub>1 = n\<^sub>2"
  apply (auto simp add: iterable_type.simps collection_type_det(1) map_type_det(1))
  using collection_type_det collection_type_and_map_type_distinct apply blast+
  using map_type_det(1) by blast+

(*** Notation ***************************************************************)

subsection \<open>Notation\<close>

notation object_type ("_ \<hookrightarrow> ObjectType'(_')([_])")
notation required_object_type ("_ \<hookrightarrow> ObjectType'(_')([1])")
notation optional_object_type ("_ \<hookrightarrow> ObjectType'(_')([?])")

notation tuple_type ("_ \<hookrightarrow> Tuple'(_')([_])")
notation required_tuple_type ("_ \<hookrightarrow> Tuple'(_')([1])")
notation required_tuple_type' ("_ \<hookleftarrow> Tuple'(_')([1])")
notation optional_tuple_type ("_ \<hookrightarrow> Tuple'(_')([?])")
notation optional_tuple_type' ("_ \<hookleftarrow> Tuple'(_')([?])")

notation collection_type ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([_])")
notation required_collection_type ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([1])")
notation required_collection_type ("_ \<hookleftarrow> Collection\<^bsub>_\<^esub>'(_')([1])")
notation optional_collection_type ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([?])")
notation optional_collection_type ("_ \<hookleftarrow> Collection\<^bsub>_\<^esub>'(_')([?])")

notation any_collection_type ("_ \<hookrightarrow> Collection'(_')([_])")
notation any_collection_type ("_ \<hookleftarrow> Collection'(_')([_])")
notation required_any_collection_type ("_ \<hookrightarrow> Collection'(_')([1])")
notation required_any_collection_type ("_ \<hookleftarrow> Collection'(_')([1])")
notation optional_any_collection_type ("_ \<hookrightarrow> Collection'(_')([?])")
notation optional_any_collection_type ("_ \<hookleftarrow> Collection'(_')([?])")

notation set_type' ("_ \<hookrightarrow> Set'(_')([_])")
notation set_type' ("_ \<hookleftarrow> Set'(_')([_])")
notation required_set_type' ("_ \<hookrightarrow> Set'(_')([1])")
notation required_set_type' ("_ \<hookleftarrow> Set'(_')([1])")
notation optional_set_type' ("_ \<hookrightarrow> Set'(_')([?])")
notation optional_set_type' ("_ \<hookleftarrow> Set'(_')([?])")

notation ordered_set_type ("_ \<hookrightarrow> OrderedSet'(_')([_])")
notation ordered_set_type ("_ \<hookleftarrow> OrderedSet'(_')([_])")
notation required_ordered_set_type ("_ \<hookrightarrow> OrderedSet'(_')([1])")
notation required_ordered_set_type ("_ \<hookleftarrow> OrderedSet'(_')([1])")
notation optional_ordered_set_type ("_ \<hookrightarrow> OrderedSet'(_')([?])")
notation optional_ordered_set_type ("_ \<hookleftarrow> OrderedSet'(_')([?])")

notation bag_type ("_ \<hookrightarrow> Bag'(_')([_])")
notation bag_type ("_ \<hookleftarrow> Bag'(_')([_])")
notation required_bag_type ("_ \<hookrightarrow> Bag'(_')([1])")
notation required_bag_type ("_ \<hookleftarrow> Bag'(_')([1])")
notation optional_bag_type ("_ \<hookrightarrow> Bag'(_')([?])")
notation optional_bag_type ("_ \<hookleftarrow> Bag'(_')([?])")

notation sequence_type ("_ \<hookrightarrow> Sequence'(_')([_])")
notation sequence_type ("_ \<hookleftarrow> Sequence'(_')([_])")
notation required_sequence_type ("_ \<hookrightarrow> Sequence'(_')([1])")
notation required_sequence_type ("_ \<hookleftarrow> Sequence'(_')([1])")
notation optional_sequence_type ("_ \<hookrightarrow> Sequence'(_')([?])")
notation optional_sequence_type ("_ \<hookleftarrow> Sequence'(_')([?])")

notation ordered_collection_type ("_ \<hookrightarrow> OrderedCollection'(_')([_])")
notation required_ordered_collection_type ("_ \<hookrightarrow> OrderedCollection'(_')([1])")
notation optional_ordered_collection_type ("_ \<hookrightarrow> OrderedCollection'(_')([?])")

notation non_collection_type ("_ \<hookrightarrow> NonCollection'(')([_])")

notation map_type ("_ \<hookrightarrow> Map'(_, _')([_])")
notation map_type' ("_ \<hookleftarrow> Map'(_, _')([_])")
notation required_map_type ("_ \<hookrightarrow> Map'(_, _')([1])")
notation required_map_type' ("_ \<hookleftarrow> Map'(_, _')([1])")
notation optional_map_type ("_ \<hookrightarrow> Map'(_, _')([?])")
notation optional_map_type' ("_ \<hookleftarrow> Map'(_, _')([?])")

notation iterable_type ("_ \<hookrightarrow> Iterable'(_')([_])")
notation required_iterable_type ("_ \<hookrightarrow> Iterable'(_')([1])")
notation optional_iterable_type ("_ \<hookrightarrow> Iterable'(_')([?])")

notation non_iterable_type ("_ \<hookrightarrow> NonIterable'(')([_])")
notation required_non_iterable_type ("_ \<hookrightarrow> NonIterable'(')([1])")
notation optional_non_iterable_type ("_ \<hookrightarrow> NonIterable'(')([?])")

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred object_type .
code_pred tuple_type .
code_pred tuple_type' .
code_pred collection_type .
code_pred any_collection_type .
code_pred ordered_collection_type .
code_pred is_collection_type .
code_pred map_type .
code_pred map_type' .
code_pred to_single_type .
code_pred inner_element_type .
code_pred update_element_type .
code_pred to_unique_collection_type .
code_pred to_nonunique_collection_type .
code_pred to_ordered_collection_type .
code_pred is_iterable_type .

end

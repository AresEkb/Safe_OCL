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
(*
inductive any_type\<^sub>N where
  "any_type\<^sub>N (Required \<tau>) \<tau> False"
| "any_type\<^sub>N (Optional \<tau>) \<tau> True"

inductive any_type where
  "any_type\<^sub>N \<tau> \<sigma> n \<Longrightarrow>
   any_type (ErrorFree \<tau>) \<sigma> n False"
| "any_type\<^sub>N \<tau> \<sigma> n \<Longrightarrow>
   any_type (Errorable \<tau>) \<sigma> n True"

inductive any_type_template where
  "any_type\<^sub>N \<tau> \<sigma> n \<Longrightarrow>
   any_type_template (ErrorFree \<tau>) \<sigma> n"
| "any_type\<^sub>N \<tau> \<sigma> n \<Longrightarrow>
   any_type_template (Errorable \<tau>) \<sigma> n"

inductive any_type_template' where
  "any_type_template \<tau> \<sigma> _ \<Longrightarrow>
   any_type_template' \<tau> \<sigma>"
*)

inductive any_type where
  "any_type \<tau>[1] \<tau>[1] False False"
| "any_type \<tau>[?] \<tau>[?] True False"
| "any_type \<tau>[1!] \<tau>[1!] False True"
| "any_type \<tau>[?!] \<tau>[?!] True True"

inductive any_type_template where
  "any_type \<tau> \<sigma> n _ \<Longrightarrow>
   any_type_template \<tau> \<sigma> n"

inductive any_type_template' where
  "any_type \<tau> \<sigma> _ _ \<Longrightarrow>
   any_type_template' \<tau> \<sigma>"

notation error_free_type ("_ \<hookrightarrow> OclAny[.]" [900] 900)
notation errorable_type ("_ \<hookrightarrow> OclAny[.!]" [900] 900)

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
   collection_type (ErrorFree \<tau>) k (ErrorFree \<sigma>) n False"
| "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type (Errorable \<tau>) k (ErrorFree \<sigma>) n True"

abbreviation collection_type_r ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([1])" [900] 900) where
  "collection_type_r \<tau> k \<sigma> \<equiv> collection_type \<tau> k \<sigma> False False"
abbreviation collection_type_o ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([?])" [900] 900) where
  "collection_type_o \<tau> k \<sigma> \<equiv> collection_type \<tau> k \<sigma> True False"
abbreviation collection_type_re ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([1!])" [900] 900) where
  "collection_type_re \<tau> k \<sigma> \<equiv> collection_type \<tau> k \<sigma> False True"
abbreviation collection_type_oe ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([?!])" [900] 900) where
  "collection_type_oe \<tau> k \<sigma> \<equiv> collection_type \<tau> k \<sigma> True True"

inductive collection_type_template where
  "collection_type \<tau> k \<sigma> n _ \<Longrightarrow>
   collection_type_template \<tau> k \<sigma> n"

abbreviation collection_type_template_r ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([1.])" [900] 900) where
  "collection_type_template_r \<tau> k \<sigma> \<equiv> collection_type_template \<tau> k \<sigma> False"
abbreviation collection_type_template_o ("_ \<hookrightarrow> Collection\<^bsub>_\<^esub>'(_')([?.])" [900] 900) where
  "collection_type_template_o \<tau> k \<sigma> \<equiv> collection_type_template \<tau> k \<sigma> True"

inductive any_collection_type where
  "collection_type \<tau> _ \<sigma> n e \<Longrightarrow>
   any_collection_type \<tau> \<sigma> n e"

abbreviation any_collection_type_r ("_ \<hookrightarrow> Collection'(_')([1])") where
  "any_collection_type_r \<tau> \<sigma> \<equiv> any_collection_type \<tau> \<sigma> False False"
abbreviation any_collection_type_o ("_ \<hookrightarrow> Collection'(_')([?])") where
  "any_collection_type_o \<tau> \<sigma> \<equiv> any_collection_type \<tau> \<sigma> True False"
abbreviation any_collection_type_re ("_ \<hookrightarrow> Collection'(_')([1!])") where
  "any_collection_type_re \<tau> \<sigma> \<equiv> any_collection_type \<tau> \<sigma> False True"
abbreviation any_collection_type_oe ("_ \<hookrightarrow> Collection'(_')([?!])") where
  "any_collection_type_oe \<tau> \<sigma> \<equiv> any_collection_type \<tau> \<sigma> True True"

inductive any_collection_type_template where
  "collection_type \<tau> _ \<sigma> n _ \<Longrightarrow>
   any_collection_type_template \<tau> \<sigma> n"

abbreviation any_collection_type_template_r ("_ \<hookrightarrow> Collection'(_')([1.])") where
  "any_collection_type_template_r \<tau> \<sigma> \<equiv> any_collection_type_template \<tau> \<sigma> False"
abbreviation any_collection_type_template_o ("_ \<hookrightarrow> Collection'(_')([?.])") where
  "any_collection_type_template_o \<tau> \<sigma> \<equiv> any_collection_type_template \<tau> \<sigma> True"

inductive collection_type_template' ("_ \<hookrightarrow> Collection'(_')" 900) where
  "collection_type \<tau> _ \<sigma> _ _ \<Longrightarrow>
   collection_type_template' \<tau> \<sigma>"


inductive collection_type' where
  "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type' (ErrorFree \<tau>) k (ErrorFree \<sigma>) n False"
| "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type' (Errorable \<tau>) k (ErrorFree \<sigma>) n True"
| "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type' (Errorable \<tau>) k (Errorable \<sigma>) n False"
| "collection_type\<^sub>N \<tau> k \<sigma> n \<Longrightarrow>
   collection_type' (Errorable \<tau>) k (Errorable \<sigma>) n True"

abbreviation collection_type_r' ("_ \<hookleftarrow> Collection\<^bsub>_\<^esub>'(_')([1])") where
  "collection_type_r' \<tau> k \<sigma> \<equiv> collection_type' \<tau> k \<sigma> False False"
abbreviation collection_type_o' ("_ \<hookleftarrow> Collection\<^bsub>_\<^esub>'(_')([?])") where
  "collection_type_o' \<tau> k \<sigma> \<equiv> collection_type' \<tau> k \<sigma> True False"
abbreviation collection_type_re' ("_ \<hookleftarrow> Collection\<^bsub>_\<^esub>'(_')([1!])") where
  "collection_type_re' \<tau> k \<sigma> \<equiv> collection_type' \<tau> k \<sigma> False True"
abbreviation collection_type_oe' ("_ \<hookleftarrow> Collection\<^bsub>_\<^esub>'(_')([?!])") where
  "collection_type_oe' \<tau> k \<sigma> \<equiv> collection_type' \<tau> k \<sigma> True True"

abbreviation set_type_r ("_ \<hookrightarrow> Set'(_')([1])") where
  "set_type_r \<tau> \<sigma> \<equiv> collection_type \<tau> SetKind \<sigma> False False"
abbreviation set_type_o ("_ \<hookrightarrow> Set'(_')([?])") where
  "set_type_o \<tau> \<sigma> \<equiv> collection_type \<tau> SetKind \<sigma> True False"
abbreviation set_type_re ("_ \<hookrightarrow> Set'(_')([1!])") where
  "set_type_re \<tau> \<sigma> \<equiv> collection_type \<tau> SetKind \<sigma> False True"
abbreviation set_type_oe ("_ \<hookrightarrow> Set'(_')([?!])") where
  "set_type_oe \<tau> \<sigma> \<equiv> collection_type \<tau> SetKind \<sigma> True True"

abbreviation set_type_r' ("_ \<hookleftarrow> Set'(_')([1])") where
  "set_type_r' \<tau> \<sigma> \<equiv> collection_type' \<tau> SetKind \<sigma> False False"
abbreviation set_type_o' ("_ \<hookleftarrow> Set'(_')([?])") where
  "set_type_o' \<tau> \<sigma> \<equiv> collection_type' \<tau> SetKind \<sigma> True False"
abbreviation set_type_re' ("_ \<hookleftarrow> Set'(_')([1!])") where
  "set_type_re' \<tau> \<sigma> \<equiv> collection_type' \<tau> SetKind \<sigma> False True"
abbreviation set_type_oe' ("_ \<hookleftarrow> Set'(_')([?!])") where
  "set_type_oe' \<tau> \<sigma> \<equiv> collection_type' \<tau> SetKind \<sigma> True True"

abbreviation ordered_set_type_r ("_ \<hookrightarrow> OrderedSet'(_')([1])") where
  "ordered_set_type_r \<tau> \<sigma> \<equiv> collection_type \<tau> OrderedSetKind \<sigma> False False"
abbreviation ordered_set_type_o ("_ \<hookrightarrow> OrderedSet'(_')([?])") where
  "ordered_set_type_o \<tau> \<sigma> \<equiv> collection_type \<tau> OrderedSetKind \<sigma> True False"
abbreviation ordered_set_type_re ("_ \<hookrightarrow> OrderedSet'(_')([1!])") where
  "ordered_set_type_re \<tau> \<sigma> \<equiv> collection_type \<tau> OrderedSetKind \<sigma> False True"
abbreviation ordered_set_type_oe ("_ \<hookrightarrow> OrderedSet'(_')([?!])") where
  "ordered_set_type_oe \<tau> \<sigma> \<equiv> collection_type \<tau> OrderedSetKind \<sigma> True True"

abbreviation ordered_set_type_r' ("_ \<hookleftarrow> OrderedSet'(_')([1])") where
  "ordered_set_type_r' \<tau> \<sigma> \<equiv> collection_type' \<tau> OrderedSetKind \<sigma> False False"
abbreviation ordered_set_type_o' ("_ \<hookleftarrow> OrderedSet'(_')([?])") where
  "ordered_set_type_o' \<tau> \<sigma> \<equiv> collection_type' \<tau> OrderedSetKind \<sigma> True False"
abbreviation ordered_set_type_re' ("_ \<hookleftarrow> OrderedSet'(_')([1!])") where
  "ordered_set_type_re' \<tau> \<sigma> \<equiv> collection_type' \<tau> OrderedSetKind \<sigma> False True"
abbreviation ordered_set_type_oe' ("_ \<hookleftarrow> OrderedSet'(_')([?!])") where
  "ordered_set_type_oe' \<tau> \<sigma> \<equiv> collection_type' \<tau> OrderedSetKind \<sigma> True True"

abbreviation bag_type_r ("_ \<hookrightarrow> Bag'(_')([1])") where
  "bag_type_r \<tau> \<sigma> \<equiv> collection_type \<tau> BagKind \<sigma> False False"
abbreviation bag_type_o ("_ \<hookrightarrow> Bag'(_')([?])") where
  "bag_type_o \<tau> \<sigma> \<equiv> collection_type \<tau> BagKind \<sigma> True False"
abbreviation bag_type_re ("_ \<hookrightarrow> Bag'(_')([1!])") where
  "bag_type_re \<tau> \<sigma> \<equiv> collection_type \<tau> BagKind \<sigma> False True"
abbreviation bag_type_oe ("_ \<hookrightarrow> Bag'(_')([?!])") where
  "bag_type_oe \<tau> \<sigma> \<equiv> collection_type \<tau> BagKind \<sigma> True True"

abbreviation bag_type_r' ("_ \<hookleftarrow> Bag'(_')([1])") where
  "bag_type_r' \<tau> \<sigma> \<equiv> collection_type' \<tau> BagKind \<sigma> False False"
abbreviation bag_type_o' ("_ \<hookleftarrow> Bag'(_')([?])") where
  "bag_type_o' \<tau> \<sigma> \<equiv> collection_type' \<tau> BagKind \<sigma> True False"
abbreviation bag_type_re' ("_ \<hookleftarrow> Bag'(_')([1!])") where
  "bag_type_re' \<tau> \<sigma> \<equiv> collection_type' \<tau> BagKind \<sigma> False True"
abbreviation bag_type_oe' ("_ \<hookleftarrow> Bag'(_')([?!])") where
  "bag_type_oe' \<tau> \<sigma> \<equiv> collection_type' \<tau> BagKind \<sigma> True True"

abbreviation sequence_type_r ("_ \<hookrightarrow> Sequence'(_')([1])") where
  "sequence_type_r \<tau> \<sigma> \<equiv> collection_type \<tau> SequenceKind \<sigma> False False"
abbreviation sequence_type_o ("_ \<hookrightarrow> Sequence'(_')([?])") where
  "sequence_type_o \<tau> \<sigma> \<equiv> collection_type \<tau> SequenceKind \<sigma> True False"
abbreviation sequence_type_re ("_ \<hookrightarrow> Sequence'(_')([1!])") where
  "sequence_type_re \<tau> \<sigma> \<equiv> collection_type \<tau> SequenceKind \<sigma> False True"
abbreviation sequence_type_oe ("_ \<hookrightarrow> Sequence'(_')([?!])") where
  "sequence_type_oe \<tau> \<sigma> \<equiv> collection_type \<tau> SequenceKind \<sigma> True True"

abbreviation sequence_type_r' ("_ \<hookleftarrow> Sequence'(_')([1])") where
  "sequence_type_r' \<tau> \<sigma> \<equiv> collection_type' \<tau> SequenceKind \<sigma> False False"
abbreviation sequence_type_o' ("_ \<hookleftarrow> Sequence'(_')([?])") where
  "sequence_type_o' \<tau> \<sigma> \<equiv> collection_type' \<tau> SequenceKind \<sigma> True False"
abbreviation sequence_type_re' ("_ \<hookleftarrow> Sequence'(_')([1!])") where
  "sequence_type_re' \<tau> \<sigma> \<equiv> collection_type' \<tau> SequenceKind \<sigma> False True"
abbreviation sequence_type_oe' ("_ \<hookleftarrow> Sequence'(_')([?!])") where
  "sequence_type_oe' \<tau> \<sigma> \<equiv> collection_type' \<tau> SequenceKind \<sigma> True True"


inductive unique_collection_type' where
  "collection_type' \<tau> SetKind \<sigma> n e \<Longrightarrow>
   unique_collection_type' \<tau> SetKind \<sigma> n e"
| "collection_type' \<tau> OrderedSetKind \<sigma> n e \<Longrightarrow>
   unique_collection_type' \<tau> OrderedSetKind \<sigma> n e"
| "collection_type' \<tau> SetKind \<sigma> n e \<Longrightarrow>
   unique_collection_type' \<tau> BagKind \<sigma> n e"
| "collection_type' \<tau> OrderedSetKind \<sigma> n e \<Longrightarrow>
   unique_collection_type' \<tau> SequenceKind \<sigma> n e"

abbreviation unique_collection_type_r' ("_ \<hookleftarrow> UniqueCollection\<^bsub>_\<^esub>'(_')([1])") where
  "unique_collection_type_r' \<tau> k \<sigma> \<equiv> unique_collection_type' \<tau> k \<sigma> False False"
abbreviation unique_collection_type_o' ("_ \<hookleftarrow> UniqueCollection\<^bsub>_\<^esub>'(_')([?])") where
  "unique_collection_type_o' \<tau> k \<sigma> \<equiv> unique_collection_type' \<tau> k \<sigma> True False"
abbreviation unique_collection_type_re' ("_ \<hookleftarrow> UniqueCollection\<^bsub>_\<^esub>'(_')([1!])") where
  "unique_collection_type_re' \<tau> k \<sigma> \<equiv> unique_collection_type' \<tau> k \<sigma> False True"
abbreviation unique_collection_type_oe' ("_ \<hookleftarrow> UniqueCollection\<^bsub>_\<^esub>'(_')([?!])") where
  "unique_collection_type_oe' \<tau> k \<sigma> \<equiv> unique_collection_type' \<tau> k \<sigma> True True"


inductive non_unique_collection_type' where
  "collection_type' \<tau> BagKind \<sigma> n e \<Longrightarrow>
   non_unique_collection_type' \<tau> SetKind \<sigma> n e"
| "collection_type' \<tau> SequenceKind \<sigma> n e \<Longrightarrow>
   non_unique_collection_type' \<tau> OrderedSetKind \<sigma> n e"
| "collection_type' \<tau> BagKind \<sigma> n e \<Longrightarrow>
   non_unique_collection_type' \<tau> BagKind \<sigma> n e"
| "collection_type' \<tau> SequenceKind \<sigma> n e \<Longrightarrow>
   non_unique_collection_type' \<tau> SequenceKind \<sigma> n e"

abbreviation non_unique_collection_type_r' ("_ \<hookleftarrow> NonUniqueCollection\<^bsub>_\<^esub>'(_')([1])") where
  "non_unique_collection_type_r' \<tau> k \<sigma> \<equiv> non_unique_collection_type' \<tau> k \<sigma> False False"
abbreviation non_unique_collection_type_o' ("_ \<hookleftarrow> NonUniqueCollection\<^bsub>_\<^esub>'(_')([?])") where
  "non_unique_collection_type_o' \<tau> k \<sigma> \<equiv> non_unique_collection_type' \<tau> k \<sigma> True False"
abbreviation non_unique_collection_type_re' ("_ \<hookleftarrow> NonUniqueCollection\<^bsub>_\<^esub>'(_')([1!])") where
  "non_unique_collection_type_re' \<tau> k \<sigma> \<equiv> non_unique_collection_type' \<tau> k \<sigma> False True"
abbreviation non_unique_collection_type_oe' ("_ \<hookleftarrow> NonUniqueCollection\<^bsub>_\<^esub>'(_')([?!])") where
  "non_unique_collection_type_oe' \<tau> k \<sigma> \<equiv> non_unique_collection_type' \<tau> k \<sigma> True True"


inductive any_ordered_collection_type where
  "collection_type \<tau> OrderedSetKind \<sigma> n e \<Longrightarrow>
   any_ordered_collection_type \<tau> \<sigma> n e"
| "collection_type \<tau> SequenceKind \<sigma> n e \<Longrightarrow>
   any_ordered_collection_type \<tau> \<sigma> n e"

abbreviation any_ordered_collection_type_r ("_ \<hookrightarrow> OrderedCollection'(_')([1])") where
  "any_ordered_collection_type_r \<tau> \<sigma> \<equiv> any_ordered_collection_type \<tau> \<sigma> False False"
abbreviation any_ordered_collection_type_o ("_ \<hookrightarrow> OrderedCollection'(_')([?])") where
  "any_ordered_collection_type_o \<tau> \<sigma> \<equiv> any_ordered_collection_type \<tau> \<sigma> True False"
abbreviation any_ordered_collection_type_re ("_ \<hookrightarrow> OrderedCollection'(_')([1!])") where
  "any_ordered_collection_type_re \<tau> \<sigma> \<equiv> any_ordered_collection_type \<tau> \<sigma> False True"
abbreviation any_ordered_collection_type_oe ("_ \<hookrightarrow> OrderedCollection'(_')([?!])") where
  "any_ordered_collection_type_oe \<tau> \<sigma> \<equiv> any_ordered_collection_type \<tau> \<sigma> True True"

inductive any_ordered_collection_type_template where
  "collection_type \<tau> _ \<sigma> n _ \<Longrightarrow>
   any_ordered_collection_type_template \<tau> \<sigma> n"

abbreviation any_ordered_collection_type_template_r ("_ \<hookrightarrow> OrderedCollection'(_')([1.])") where
  "any_ordered_collection_type_template_r \<tau> \<sigma> \<equiv> any_ordered_collection_type_template \<tau> \<sigma> False"
abbreviation any_ordered_collection_type_template_o ("_ \<hookrightarrow> OrderedCollection'(_')([?.])") where
  "any_ordered_collection_type_template_o \<tau> \<sigma> \<equiv> any_ordered_collection_type_template \<tau> \<sigma> True"


inductive ordered_collection_type' where
  "collection_type' \<tau> OrderedSetKind \<sigma> n e \<Longrightarrow>
   ordered_collection_type' \<tau> SetKind \<sigma> n e"
| "collection_type' \<tau> OrderedSetKind \<sigma> n e \<Longrightarrow>
   ordered_collection_type' \<tau> OrderedSetKind \<sigma> n e"
| "collection_type' \<tau> SequenceKind \<sigma> n e \<Longrightarrow>
   ordered_collection_type' \<tau> BagKind \<sigma> n e"
| "collection_type' \<tau> SequenceKind \<sigma> n e \<Longrightarrow>
   ordered_collection_type' \<tau> SequenceKind \<sigma> n e"

abbreviation ordered_collection_type_r' ("_ \<hookleftarrow> OrderedCollection\<^bsub>_\<^esub>'(_')([1])") where
  "ordered_collection_type_r' \<tau> k \<sigma> \<equiv> ordered_collection_type' \<tau> k \<sigma> False False"
abbreviation ordered_collection_type_o' ("_ \<hookleftarrow> OrderedCollection\<^bsub>_\<^esub>'(_')([?])") where
  "ordered_collection_type_o' \<tau> k \<sigma> \<equiv> ordered_collection_type' \<tau> k \<sigma> True False"
abbreviation ordered_collection_type_re' ("_ \<hookleftarrow> OrderedCollection\<^bsub>_\<^esub>'(_')([1!])") where
  "ordered_collection_type_re' \<tau> k \<sigma> \<equiv> ordered_collection_type' \<tau> k \<sigma> False True"
abbreviation ordered_collection_type_oe' ("_ \<hookleftarrow> OrderedCollection\<^bsub>_\<^esub>'(_')([?!])") where
  "ordered_collection_type_oe' \<tau> k \<sigma> \<equiv> ordered_collection_type' \<tau> k \<sigma> True True"


inductive is_collection_type where
  "collection_type \<tau> _ _ _ _ \<Longrightarrow>
   is_collection_type \<tau>"

abbreviation
  "non_collection_type \<tau> \<sigma> n e \<equiv> (\<not> is_collection_type \<tau> \<and> any_type \<tau> \<sigma> n e)"

abbreviation non_collection_type_r ("_ \<hookrightarrow> NonCollection'(_')([1])") where
  "non_collection_type_r \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type \<tau> \<sigma> False False)"
abbreviation non_collection_type_o ("_ \<hookrightarrow> NonCollection'(_')([?])") where
  "non_collection_type_o \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type \<tau> \<sigma> True False)"
abbreviation non_collection_type_re ("_ \<hookrightarrow> NonCollection'(_')([1!])") where
  "non_collection_type_re \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type \<tau> \<sigma> False True)"
abbreviation non_collection_type_oe ("_ \<hookrightarrow> NonCollection'(_')([?!])") where
  "non_collection_type_oe \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type \<tau> \<sigma> True True)"

abbreviation non_collection_type_template_r ("_ \<hookrightarrow> NonCollection'(_')([1.])") where
  "non_collection_type_template_r \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type_template \<tau> \<sigma> False)"
abbreviation non_collection_type_template_o ("_ \<hookrightarrow> NonCollection'(_')([?.])") where
  "non_collection_type_template_o \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type_template \<tau> \<sigma> True)"

abbreviation non_collection_type_template' ("_ \<hookrightarrow> NonCollection'(_')" 900) where
  "non_collection_type_template' \<tau> \<sigma> \<equiv> (\<not> is_collection_type \<tau> \<and> any_type_template' \<tau> \<sigma>)"


inductive to_single_type where
  "\<not> is_collection_type \<tau> \<Longrightarrow>
   to_single_type \<tau> \<tau>"
| "collection_type \<tau> _ \<sigma> _ _ \<Longrightarrow>
   to_single_type \<sigma> \<rho> \<Longrightarrow>
   to_single_type \<tau> \<rho>"


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
   map_type (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n False"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type (Errorable \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n True"

abbreviation map_type_r ("_ \<hookrightarrow> Map'(_, _')([1])") where
  "map_type_r \<tau> \<sigma> \<rho> \<equiv> map_type \<tau> \<sigma> \<rho> False False"
abbreviation map_type_o ("_ \<hookrightarrow> Map'(_, _')([?])") where
  "map_type_o \<tau> \<sigma> \<rho> \<equiv> map_type \<tau> \<sigma> \<rho> True False"
abbreviation map_type_re ("_ \<hookrightarrow> Map'(_, _')([1!])") where
  "map_type_re \<tau> \<sigma> \<rho> \<equiv> map_type \<tau> \<sigma> \<rho> False True"
abbreviation map_type_oe ("_ \<hookrightarrow> Map'(_, _')([?!])") where
  "map_type_oe \<tau> \<sigma> \<rho> \<equiv> map_type \<tau> \<sigma> \<rho> True True"

inductive map_type_template where
  "map_type \<tau> \<sigma> \<rho> n _ \<Longrightarrow>
   map_type_template \<tau> \<sigma> \<rho> n"

abbreviation map_type_template_r ("_ \<hookrightarrow> Map'(_, _')([1.])") where
  "map_type_template_r \<tau> \<sigma> \<rho> \<equiv> map_type_template \<tau> \<sigma> \<rho> False"
abbreviation map_type_template_o ("_ \<hookrightarrow> Map'(_, _')([?.])") where
  "map_type_template_o \<tau> \<sigma> \<rho> \<equiv> map_type_template \<tau> \<sigma> \<rho> True"

inductive map_type_template' ("_ \<hookrightarrow> Map'(_, _')" 900) where
  "map_type \<tau> \<sigma> \<rho> _ _ \<Longrightarrow>
   map_type_template' \<tau> \<sigma> \<rho>"

inductive map_type' where
  "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (ErrorFree \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n False"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>) n False"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (ErrorFree \<rho>) n False"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) n False"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (ErrorFree \<sigma>) (ErrorFree \<rho>) n True"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (ErrorFree \<sigma>) (Errorable \<rho>) n True"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (ErrorFree \<rho>) n True"
| "map_type\<^sub>N \<tau> \<sigma> \<rho> n \<Longrightarrow>
   map_type' (Errorable \<tau>) (Errorable \<sigma>) (Errorable \<rho>) n True"

abbreviation map_type_r' ("_ \<hookleftarrow> Map'(_, _')([1])") where
  "map_type_r' \<tau> \<sigma> \<rho> \<equiv> map_type' \<tau> \<sigma> \<rho> False False"
abbreviation map_type_o' ("_ \<hookleftarrow> Map'(_, _')([?])") where
  "map_type_o' \<tau> \<sigma> \<rho> \<equiv> map_type' \<tau> \<sigma> \<rho> True False"
abbreviation map_type_re' ("_ \<hookleftarrow> Map'(_, _')([1!])") where
  "map_type_re' \<tau> \<sigma> \<rho> \<equiv> map_type' \<tau> \<sigma> \<rho> False True"
abbreviation map_type_oe' ("_ \<hookleftarrow> Map'(_, _')([?!])") where
  "map_type_oe' \<tau> \<sigma> \<rho> \<equiv> map_type' \<tau> \<sigma> \<rho> True True"

subsection \<open>Iterable Types\<close>

inductive iterable_type where
  "collection_type \<tau> _ \<sigma> n e \<Longrightarrow>
   iterable_type \<tau> \<sigma> n e"
| "map_type \<tau> \<sigma> _ n e \<Longrightarrow>
   iterable_type \<tau> \<sigma> n e"

abbreviation iterable_type_r ("_ \<hookrightarrow> Iterable'(_')([1])") where
  "iterable_type_r \<tau> \<sigma> \<equiv> iterable_type \<tau> \<sigma> False False"
abbreviation iterable_type_o ("_ \<hookrightarrow> Iterable'(_')([?])") where
  "iterable_type_o \<tau> \<sigma> \<equiv> iterable_type \<tau> \<sigma> True False"
abbreviation iterable_type_re ("_ \<hookrightarrow> Iterable'(_')([1!])") where
  "iterable_type_re \<tau> \<sigma> \<equiv> iterable_type \<tau> \<sigma> False True"
abbreviation iterable_type_oe ("_ \<hookrightarrow> Iterable'(_')([?!])") where
  "iterable_type_oe \<tau> \<sigma> \<equiv> iterable_type \<tau> \<sigma> True True"

inductive iterable_type_template where
  "iterable_type \<tau> \<sigma> n _ \<Longrightarrow>
   iterable_type_template \<tau> \<sigma> n"

abbreviation iterable_type_template_r ("_ \<hookrightarrow> Iterable'(_')([1.])") where
  "iterable_type_template_r \<tau> \<sigma> \<equiv> iterable_type_template \<tau> \<sigma> False"
abbreviation iterable_type_template_o ("_ \<hookrightarrow> Iterable'(_')([?.])") where
  "iterable_type_template_o \<tau> \<sigma> \<equiv> iterable_type_template \<tau> \<sigma> True"

inductive iterable_type_template' ("_ \<hookrightarrow> Iterable'(_')" 900) where
  "iterable_type \<tau> \<sigma> _ _ \<Longrightarrow>
   iterable_type_template' \<tau> \<sigma>"

inductive is_iterable_type where
  "iterable_type \<tau> _ _ _ \<Longrightarrow> is_iterable_type \<tau>"
(*
abbreviation non_iterable_type_r ("_ \<hookrightarrow> NonIterable'(_')([1])") where
  "non_iterable_type_r \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type \<tau> \<sigma> False False)"
abbreviation non_iterable_type_o ("_ \<hookrightarrow> NonIterable'(_')([?])") where
  "non_iterable_type_o \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type \<tau> \<sigma> True False)"
abbreviation non_iterable_type_re ("_ \<hookrightarrow> NonIterable'(_')([1!])") where
  "non_iterable_type_re \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type \<tau> \<sigma> False True)"
abbreviation non_iterable_type_oe ("_ \<hookrightarrow> NonIterable'(_')([?!])") where
  "non_iterable_type_oe \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type \<tau> \<sigma> True True)"

abbreviation non_iterable_type_template_r ("_ \<hookrightarrow> NonIterable'(_')([1.])") where
  "non_iterable_type_template_r \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type_template \<tau> \<sigma> False)"
abbreviation non_iterable_type_template_o ("_ \<hookrightarrow> NonIterable'(_')([?.])") where
  "non_iterable_type_template_o \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type_template \<tau> \<sigma> True)"
*)
abbreviation non_iterable_type_template' ("_ \<hookrightarrow> NonIterable'(_')" 900) where
  "non_iterable_type_template' \<tau> \<sigma> \<equiv> (\<not> is_iterable_type \<tau> \<and> any_type_template' \<tau> \<sigma>)"

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>
(*
lemma any_type_template'_simps:
  "any_type_template' (ErrorFree \<tau>) \<sigma> = (\<exists>n. any_type\<^sub>N \<tau> \<sigma> n)"
  "any_type_template' (Errorable \<tau>) \<sigma> = (\<exists>n. any_type\<^sub>N \<tau> \<sigma> n)"
  by (auto simp add: any_type_template'.simps any_type_template.simps)

lemma ex_any_type_template'_simps:
  "Ex (any_type_template' (ErrorFree \<tau>)) = (\<exists>\<sigma> n. any_type\<^sub>N \<tau> \<sigma> n)"
  "Ex (any_type_template' (Errorable \<tau>)) = (\<exists>\<sigma> n. any_type\<^sub>N \<tau> \<sigma> n)"
  using any_type_template'_simps(1) apply blast
  using any_type_template'_simps(2) by blast
*)

lemma collection_type_simps:
  "collection_type (ErrorFree \<tau>) k \<sigma> n e =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> e = False \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "collection_type (Errorable \<tau>) k \<sigma> n e =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> e = True \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  by (simp_all add: collection_type.simps)

lemma ex_collection_type_simps:
  "Ex (collection_type (ErrorFree \<tau>) k \<sigma> n) =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  "Ex (collection_type (Errorable \<tau>) k \<sigma> n) =
   (\<exists>\<rho>. \<sigma> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<tau> k \<rho> n)"
  using collection_type_simps(1) apply blast
  using collection_type_simps(2) by blast

lemma collection_type'_simps:
  "collection_type' \<tau> k (ErrorFree \<sigma>) n False =
   (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  "collection_type' \<tau> k (Errorable \<sigma>) n False =
   (\<exists>\<rho>. \<tau> = Errorable \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  "collection_type' \<tau> k (ErrorFree \<sigma>) n True =
   (\<exists>\<rho>. \<tau> = Errorable \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  "collection_type' \<tau> k (Errorable \<sigma>) n True =
   (\<exists>\<rho>. \<tau> = Errorable \<rho> \<and> collection_type\<^sub>N \<rho> k \<sigma> n)"
  by (simp_all add: collection_type'.simps)

text \<open>
  The first argument gets simpler, so the following simplification rules
  does not get stuck.\<close>

lemma to_single_type_simps:
  "to_single_type (ErrorFree \<tau>) \<sigma> =
   ((\<not> is_collection_type (ErrorFree \<tau>) \<and> (ErrorFree \<tau>) = \<sigma>) \<or>
    (\<exists>k \<upsilon> n e. collection_type (ErrorFree \<tau>) k \<upsilon> n e \<and> to_single_type \<upsilon> \<sigma>))"
  "to_single_type (Errorable \<tau>) \<sigma> =
   ((\<not> is_collection_type (Errorable \<tau>) \<and> (Errorable \<tau>) = \<sigma>) \<or>
    (\<exists>k \<upsilon> n e. collection_type (Errorable \<tau>) k \<upsilon> n e \<and> to_single_type \<upsilon> \<sigma>))"
  by (subst to_single_type.simps; auto)+

lemmas ocl_type_helper_simps =
  (*any_type\<^sub>N.simps*)
  any_type.simps
  any_type_template.simps
  any_type_template'.simps
  (*any_type_template'_simps
  ex_any_type_template'_simps*)

  tuple_type.simps
  tuple_type'.simps

  collection_type\<^sub>T.simps
  collection_type\<^sub>N.simps
  collection_type_simps
  ex_collection_type_simps
  collection_type'_simps
  any_collection_type.simps
  any_collection_type_template.simps
  collection_type_template.simps
  collection_type_template'.simps
  unique_collection_type'.simps
  non_unique_collection_type'.simps
  any_ordered_collection_type.simps
  any_ordered_collection_type_template.simps
  ordered_collection_type'.simps
  is_collection_type.simps
  to_single_type_simps

  map_type\<^sub>T.simps
  map_type\<^sub>N.simps
  map_type.simps
  map_type'.simps
  map_type_template.simps
  map_type_template'.simps

  iterable_type.simps
  iterable_type_template.simps
  iterable_type_template'.simps
  is_iterable_type.simps

(*** Misc Properties ********************************************************)

section \<open>Misc Properties\<close>

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

lemma collection_type_sup:
  "collection_type \<tau> k \<rho> n e \<Longrightarrow>
   collection_type \<sigma> k \<upsilon> n e \<Longrightarrow>
   collection_type (\<tau> \<squnion> \<sigma>) k (\<rho> \<squnion> \<upsilon>) n e"
  by (auto simp add: collection_type.simps
      collection_type\<^sub>N.simps collection_type\<^sub>T.simps)

lemma collection_type_and_non_collection_type_distinct:
  "collection_type_template \<tau> k \<sigma> n \<Longrightarrow> non_collection_type_template' \<tau> \<rho> \<Longrightarrow> False"
  "collection_type_template' \<tau> \<sigma> \<Longrightarrow> non_collection_type_template' \<tau> \<rho> \<Longrightarrow> False"
  "any_collection_type \<tau> \<sigma> n\<^sub>1 e\<^sub>1 \<Longrightarrow> non_collection_type \<tau> \<rho> n\<^sub>2 e\<^sub>2 \<Longrightarrow> False"
  "any_collection_type_template \<tau> \<sigma> n \<Longrightarrow> non_collection_type_template' \<tau> \<rho> \<Longrightarrow> False"
  by (auto simp add: collection_type_template.simps collection_type_template'.simps
      any_collection_type_template.simps any_collection_type.simps is_collection_type.simps)

lemma collection_type_and_map_type_distinct:
  "collection_type \<tau> k \<sigma> n\<^sub>1 e\<^sub>1 \<Longrightarrow> map_type \<tau> \<rho> \<upsilon> n\<^sub>2 e\<^sub>2 \<Longrightarrow> False"
  by (auto simp: collection_type.simps collection_type\<^sub>N.simps
      collection_type\<^sub>T.simps map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)


lemma map_type_implies_map_type':
  "map_type \<tau> \<sigma> \<rho> n e \<Longrightarrow> map_type' \<tau> \<sigma> \<rho> n e"
  by (erule map_type.cases; simp add: map_type'.simps)
(*
lemma map_type'_implies_ex_map_type:
  "map_type' \<tau> \<sigma> \<rho> n e \<Longrightarrow> \<exists>\<upsilon> \<phi>. map_type \<tau> \<upsilon> \<phi> n e"
  by (erule map_type'.cases; auto simp add: map_type.simps)
*)
lemma map_type_sup:
  "map_type \<tau> \<rho> \<phi> n e \<Longrightarrow>
   map_type \<sigma> \<upsilon> \<psi> n e \<Longrightarrow>
   map_type (\<tau> \<squnion> \<sigma>) (\<rho> \<squnion> \<upsilon>) (\<phi> \<squnion> \<psi>) n e"
  for \<tau> \<sigma> \<rho> \<upsilon> :: "('a :: semilattice_sup) type\<^sub>N\<^sub>E"
  apply (cases \<rho>; cases \<phi>)
  by (auto simp add: map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)

lemma map_type'_sup:
  "map_type' \<tau> \<rho> \<phi> n e \<Longrightarrow>
   map_type \<sigma> \<upsilon> \<psi> n e \<Longrightarrow>
   map_type' (\<tau> \<squnion> \<sigma>) (\<rho> \<squnion> \<upsilon>) (\<phi> \<squnion> \<psi>) n e"
  for \<tau> \<sigma> \<rho> \<upsilon> :: "('a :: semilattice_sup) type\<^sub>N\<^sub>E"
  apply (cases \<rho>; cases \<phi>)
  by (auto simp add: map_type'.simps map_type.simps
      map_type\<^sub>N.simps map_type\<^sub>T.simps)

lemma any_collection_type_and_map_type_distinct:
  "any_collection_type \<tau> \<sigma> n\<^sub>1 e\<^sub>1 \<Longrightarrow> map_type \<tau> \<rho> \<upsilon> n\<^sub>2 e\<^sub>2 \<Longrightarrow> False"
  by (auto simp: any_collection_type.simps collection_type.simps
      collection_type\<^sub>N.simps collection_type\<^sub>T.simps
      map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)

lemma any_ordered_collection_type_and_map_type_distinct:
  "any_ordered_collection_type \<tau> \<sigma> n\<^sub>1 e\<^sub>1 \<Longrightarrow> map_type \<tau> \<rho> \<upsilon> n\<^sub>2 e\<^sub>2 \<Longrightarrow> False"
  by (auto simp: any_ordered_collection_type.simps collection_type.simps
      collection_type\<^sub>N.simps collection_type\<^sub>T.simps
      map_type.simps map_type\<^sub>N.simps map_type\<^sub>T.simps)

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
  "collection_type \<tau> k\<^sub>1 \<sigma>\<^sub>1 n\<^sub>1 e\<^sub>1 \<Longrightarrow>
   collection_type \<tau> k\<^sub>2 \<sigma>\<^sub>2 n\<^sub>2 e\<^sub>2 \<Longrightarrow> k\<^sub>1 = k\<^sub>2 \<and> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
  by (elim collection_type.cases; simp add: collection_type\<^sub>N_det(1))

lemma collection_type'_det:
  "collection_type' \<tau>\<^sub>1 k \<sigma> n e \<Longrightarrow>
   collection_type' \<tau>\<^sub>2 k \<sigma> n e \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (elim collection_type'.cases; simp add: collection_type\<^sub>N_det(2))

lemma any_collection_type_det:
  "any_collection_type \<tau> \<sigma>\<^sub>1 n\<^sub>1 e\<^sub>1 \<Longrightarrow>
   any_collection_type \<tau> \<sigma>\<^sub>2 n\<^sub>2 e\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
  by (elim any_collection_type.cases; simp add: collection_type_det)

lemma any_collection_type_template_det:
  "any_collection_type_template \<tau> \<sigma>\<^sub>1 n\<^sub>1 \<Longrightarrow>
   any_collection_type_template \<tau> \<sigma>\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  by (elim any_collection_type_template.cases; simp add: collection_type_det)

lemma unique_collection_type'_det:
  "unique_collection_type' \<tau>\<^sub>1 k \<sigma> n e \<Longrightarrow>
   unique_collection_type' \<tau>\<^sub>2 k \<sigma> n e \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (elim unique_collection_type'.cases; simp add: collection_type'_det)

lemma non_unique_collection_type'_det:
  "non_unique_collection_type' \<tau>\<^sub>1 k \<sigma> n e \<Longrightarrow>
   non_unique_collection_type' \<tau>\<^sub>2 k \<sigma> n e \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (elim non_unique_collection_type'.cases; simp add: collection_type'_det)

lemma any_ordered_collection_type_det:
  "any_ordered_collection_type \<tau> \<sigma>\<^sub>1 n\<^sub>1 e\<^sub>1 \<Longrightarrow>
   any_ordered_collection_type \<tau> \<sigma>\<^sub>2 n\<^sub>2 e\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
  by (elim any_ordered_collection_type.cases; simp add: collection_type_det)

lemma ordered_collection_type'_det:
  "ordered_collection_type' \<tau>\<^sub>1 k \<sigma> n e \<Longrightarrow>
   ordered_collection_type' \<tau>\<^sub>2 k \<sigma> n e \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (elim ordered_collection_type'.cases; simp add: collection_type'_det)


lemma to_single_type_det:
  "to_single_type \<tau> \<sigma> \<Longrightarrow>
   to_single_type \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  apply (induct rule: to_single_type.induct)
  apply (erule to_single_type.cases; simp add: is_collection_type.intros)
  apply (erule to_single_type.cases)
  sorry
(*  using collection_type_det is_collection_type.intros to_single_type.simps by blast*)
(*  by (smt collection_type_det is_collection_type.intros to_single_type.simps)*)


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
  "map_type \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 e\<^sub>1 \<Longrightarrow>
   map_type \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 e\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
  by (elim map_type.cases; simp add: map_type\<^sub>N_det(1))

lemma map_type_template_det:
  "map_type_template \<tau> \<sigma>\<^sub>N\<^sub>1 \<rho>\<^sub>N\<^sub>1 n\<^sub>1 \<Longrightarrow>
   map_type_template \<tau> \<sigma>\<^sub>N\<^sub>2 \<rho>\<^sub>N\<^sub>2 n\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>N\<^sub>1 = \<sigma>\<^sub>N\<^sub>2 \<and> \<rho>\<^sub>N\<^sub>1 = \<rho>\<^sub>N\<^sub>2 \<and> n\<^sub>1 = n\<^sub>2"
  by (elim map_type_template.cases; simp add: map_type_det)

lemma map_type'_det:
  "map_type' \<tau>\<^sub>1 \<sigma>\<^sub>N \<rho>\<^sub>N n e \<Longrightarrow>
   map_type' \<tau>\<^sub>2 \<sigma>\<^sub>N \<rho>\<^sub>N n e \<Longrightarrow> \<tau>\<^sub>1 = \<tau>\<^sub>2"
  by (elim map_type'.cases; simp add: map_type\<^sub>N_det(2))


lemma iterable_type_det:
  "iterable_type \<tau> \<sigma> n\<^sub>1 e\<^sub>1 \<Longrightarrow>
   iterable_type \<tau> \<rho> n\<^sub>2 e\<^sub>2 \<Longrightarrow> \<sigma> = \<rho> \<and> n\<^sub>1 = n\<^sub>2 \<and> e\<^sub>1 = e\<^sub>2"
  apply (auto simp add: iterable_type.simps collection_type_det map_type_det(1))
  using collection_type_det collection_type_and_map_type_distinct apply blast+
  using map_type_det(1) by blast+

(*** Notation ***************************************************************)

subsection \<open>Notation\<close>

notation object_type ("_ \<hookrightarrow> ObjectType'(_')([_])")
notation required_object_type ("_ \<hookrightarrow> ObjectType'(_')([1])")
notation optional_object_type ("_ \<hookrightarrow> ObjectType'(_')([?])")

notation tuple_type ("_ \<hookrightarrow> Tuple'(_')([_])")
notation tuple_type' ("_ \<hookleftarrow> Tuple'(_')([_])")
notation required_tuple_type ("_ \<hookrightarrow> Tuple'(_')([1])")
notation required_tuple_type' ("_ \<hookleftarrow> Tuple'(_')([1])")
notation optional_tuple_type ("_ \<hookrightarrow> Tuple'(_')([?])")
notation optional_tuple_type' ("_ \<hookleftarrow> Tuple'(_')([?])")

notation to_optional_type_nested ("_[??]" [1000] 1000)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred any_type .
code_pred object_type .
code_pred tuple_type .
code_pred tuple_type' .
code_pred collection_type .
code_pred any_collection_type .
code_pred unique_collection_type' .
code_pred non_unique_collection_type' .
(*code_pred ordered_collection_type .*)
code_pred ordered_collection_type' .
code_pred is_collection_type .
code_pred to_single_type .
code_pred map_type .
code_pred map_type' .
code_pred iterable_type .
(*code_pred any_iterable_type .*)
code_pred is_iterable_type .

end

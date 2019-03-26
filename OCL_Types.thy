(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Types\<close>
theory OCL_Types
  imports Errorable Tuple "HOL-Library.Phantom_Type"
begin

(*** Definition *************************************************************)

section \<open>Definition\<close>

text \<open>
  Types are parameterized over classes.\<close>

type_synonym 'a enum = "('a, String.literal) phantom"
type_synonym elit = String.literal
type_synonym telem = String.literal

datatype (plugins del: size) 'a type =
  OclAny
| OclVoid

| Boolean
| Real
| Integer
| UnlimitedNatural
| String

| ObjectType 'a ("\<langle>_\<rangle>\<^sub>\<T>" [0] 1000)
| Enum "'a enum"

| Collection "'a type\<^sub>N\<^sub>E"
| Set "'a type\<^sub>N\<^sub>E"
| OrderedSet "'a type\<^sub>N\<^sub>E"
| Bag "'a type\<^sub>N\<^sub>E"
| Sequence "'a type\<^sub>N\<^sub>E"

| Tuple "telem \<rightharpoonup>\<^sub>f 'a type\<^sub>N\<^sub>E"

and 'a type\<^sub>N =
  Required "'a type"
| Optional "'a type"

and 'a type\<^sub>N\<^sub>E =
  ErrorFree "'a type\<^sub>N"
| Errorable "'a type\<^sub>N"


abbreviation Required_ErrorFree ("_[1]" [1000] 1000) where
  "Required_ErrorFree \<tau> \<equiv> ErrorFree (Required \<tau>)"

abbreviation Optional_ErrorFree ("_[?]" [1000] 1000) where
  "Optional_ErrorFree \<tau> \<equiv> ErrorFree (Optional \<tau>)"

abbreviation Required_Errorable ("_[1!]" [1000] 1000) where
  "Required_Errorable \<tau> \<equiv> Errorable (Required \<tau>)"

abbreviation Optional_Errorable ("_[?!]" [1000] 1000) where
  "Optional_Errorable \<tau> \<equiv> Errorable (Optional \<tau>)"


text \<open>
  We define the @{text OclInvalid} type separately, because we
  do not need types like @{text "Set(OclInvalid)"} in the theory.
  The @{text "OclVoid[1]"} type is not equal to @{text OclInvalid}.
  For example, @{text "Set(OclVoid[1])"} could theoretically be
  a valid type of the following expression:\<close>

text \<open>
\<^verbatim>\<open>Set{null}->excluding(null)\<close>\<close>

definition "OclInvalid :: 'a type\<^sub>\<bottom> \<equiv> \<bottom>"

primrec type_size :: "'a type \<Rightarrow> nat"
    and type_size\<^sub>N :: "'a type\<^sub>N \<Rightarrow> nat"
    and type_size\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E \<Rightarrow> nat" where

  "type_size OclAny = 0"
| "type_size OclVoid = 0"

| "type_size Boolean = 0"
| "type_size Real = 0"
| "type_size Integer = 0"
| "type_size UnlimitedNatural = 0"
| "type_size String = 0"

| "type_size (ObjectType \<C>) = 0"
| "type_size (Enum \<E>) = 0"

| "type_size (Collection \<tau>) = Suc (type_size\<^sub>N\<^sub>E \<tau>)"
| "type_size (Set \<tau>) = Suc (type_size\<^sub>N\<^sub>E \<tau>)"
| "type_size (OrderedSet \<tau>) = Suc (type_size\<^sub>N\<^sub>E \<tau>)"
| "type_size (Bag \<tau>) = Suc (type_size\<^sub>N\<^sub>E \<tau>)"
| "type_size (Sequence \<tau>) = Suc (type_size\<^sub>N\<^sub>E \<tau>)"

| "type_size (Tuple \<pi>) = Suc (ffold tcf 0 (fset_of_fmap (fmmap type_size\<^sub>N\<^sub>E \<pi>)))"

| "type_size\<^sub>N (Required \<tau>) = Suc (type_size \<tau>)"
| "type_size\<^sub>N (Optional \<tau>) = Suc (type_size \<tau>)"

| "type_size\<^sub>N\<^sub>E (ErrorFree \<tau>) = Suc (type_size\<^sub>N \<tau>)"
| "type_size\<^sub>N\<^sub>E (Errorable \<tau>) = Suc (type_size\<^sub>N \<tau>)"


instantiation type :: (type) size
begin
definition size_type where [simp, code]: "size_type \<equiv> type_size"
instance ..
end

instantiation type\<^sub>N :: (type) size
begin
definition size_type\<^sub>N where [simp, code]: "size_type\<^sub>N \<equiv> type_size\<^sub>N"
instance ..
end

instantiation type\<^sub>N\<^sub>E :: (type) size
begin
definition size_type\<^sub>N\<^sub>E where [simp, code]: "size_type\<^sub>N\<^sub>E \<equiv> type_size\<^sub>N\<^sub>E"
instance ..
end


inductive subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" (infix "\<sqsubset>" 65)
      and subtype\<^sub>N :: "'a type\<^sub>N \<Rightarrow> 'a type\<^sub>N \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>N" 65)
      and subtype\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>N\<^sub>E" 65) where

\<comment> \<open>Basic Types\<close>

  "OclVoid \<sqsubset> Boolean"
| "OclVoid \<sqsubset> UnlimitedNatural"
| "OclVoid \<sqsubset> String"
| "OclVoid \<sqsubset> \<langle>\<C>\<rangle>\<^sub>\<T>"
| "OclVoid \<sqsubset> Enum \<E>"

| "UnlimitedNatural \<sqsubset> Integer"
| "Integer \<sqsubset> Real"
| "\<C> < \<D> \<Longrightarrow> \<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset> \<langle>\<D>\<rangle>\<^sub>\<T>"

| "Boolean \<sqsubset> OclAny"
| "Real \<sqsubset> OclAny"
| "String \<sqsubset> OclAny"
| "\<langle>\<C>\<rangle>\<^sub>\<T> \<sqsubset> OclAny"
| "Enum \<E> \<sqsubset> OclAny"

\<comment> \<open>Collection Types\<close>

| "OclVoid \<sqsubset> Set OclVoid[1]"
| "OclVoid \<sqsubset> OrderedSet OclVoid[1]"
| "OclVoid \<sqsubset> Bag OclVoid[1]"
| "OclVoid \<sqsubset> Sequence OclVoid[1]"

| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"

| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"

| "Collection OclAny[?!] \<sqsubset> OclAny"

\<comment> \<open>Tuple Types\<close>

| "OclVoid \<sqsubset> Tuple \<pi>"
| "strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"
| "Tuple \<pi> \<sqsubset> OclAny"

\<comment> \<open>Nullable Types\<close>

| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Required \<tau> \<sqsubset>\<^sub>N Required \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Optional \<tau> \<sqsubset>\<^sub>N Optional \<sigma>"
| "Required \<tau> \<sqsubset>\<^sub>N Optional \<tau>"

\<comment> \<open>Errorable Types\<close>

| "\<tau> \<sqsubset>\<^sub>N \<sigma> \<Longrightarrow> ErrorFree \<tau> \<sqsubset>\<^sub>N\<^sub>E ErrorFree \<sigma>"
| "\<tau> \<sqsubset>\<^sub>N \<sigma> \<Longrightarrow> Errorable \<tau> \<sqsubset>\<^sub>N\<^sub>E Errorable \<sigma>"
| "ErrorFree \<tau> \<sqsubset>\<^sub>N\<^sub>E Errorable \<tau>"


code_pred [show_modes] subtype .

declare subtype_subtype\<^sub>N_subtype\<^sub>N\<^sub>E.intros [intro!]

inductive_cases subtype_x_OclAny [elim!]: "\<tau> \<sqsubset> OclAny"
inductive_cases subtype_x_OclVoid [elim!]: "\<tau> \<sqsubset> OclVoid"
inductive_cases subtype_x_Boolean [elim!]: "\<tau> \<sqsubset> Boolean"
inductive_cases subtype_x_Real [elim!]: "\<tau> \<sqsubset> Real"
inductive_cases subtype_x_Integer [elim!]: "\<tau> \<sqsubset> Integer"
inductive_cases subtype_x_UnlimitedNatural [elim!]: "\<tau> \<sqsubset> UnlimitedNatural"
inductive_cases subtype_x_String [elim!]: "\<tau> \<sqsubset> String"
inductive_cases subtype_x_ObjectType [elim!]: "\<tau> \<sqsubset> ObjectType \<C>"
inductive_cases subtype_x_Enum [elim!]: "\<tau> \<sqsubset> Enum \<E>"
inductive_cases subtype_x_Collection [elim!]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases subtype_x_Set [elim!]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases subtype_x_OrderedSet [elim!]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases subtype_x_Bag [elim!]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases subtype_x_Sequence [elim!]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases subtype_x_Tuple [elim!]: "\<tau> \<sqsubset> Tuple \<pi>"

inductive_cases subtype_x_Required [elim!]: "\<tau> \<sqsubset>\<^sub>N Required \<sigma>"
inductive_cases subtype_x_Optional [elim!]: "\<tau> \<sqsubset>\<^sub>N Optional \<sigma>"

inductive_cases subtype_x_ErrorFree [elim!]: "\<tau> \<sqsubset>\<^sub>N\<^sub>E ErrorFree \<sigma>"
inductive_cases subtype_x_Errorable [elim!]: "\<tau> \<sqsubset>\<^sub>N\<^sub>E Errorable \<sigma>"

inductive_cases subtype_OclAny_x [elim!]: "OclAny \<sqsubset> \<sigma>"
inductive_cases subtype_Collection_x [elim!]: "Collection \<tau> \<sqsubset> \<sigma>"

lemma
  subtype_asym: "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> \<sigma> \<sqsubset> \<tau> \<Longrightarrow> False" and
  subtype\<^sub>N_asym: "\<tau>\<^sub>N \<sqsubset>\<^sub>N \<sigma>\<^sub>N \<Longrightarrow> \<sigma>\<^sub>N \<sqsubset>\<^sub>N \<tau>\<^sub>N \<Longrightarrow> False" and
  subtype\<^sub>N\<^sub>E_asym: "\<tau>\<^sub>N\<^sub>E \<sqsubset>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E \<sqsubset>\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<Longrightarrow> False"
  for \<tau> \<sigma> :: "'a :: order type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  apply (induct rule: subtype_subtype\<^sub>N_subtype\<^sub>N\<^sub>E.inducts, auto)
  using subtuple_antisym by fastforce

(*** Constructors Bijectivity on Transitive Closures ************************)

section \<open>Constructors Bijectivity on Transitive Closures\<close>

lemma subtype_tranclp_Collection_x:
  "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection \<tau>) \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ \<tau> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct, auto)
  by (metis subtype_Collection_x subtype_OclAny_x tranclp.trancl_into_trancl)

lemma Collection_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Collection"
  apply (auto simp add: inj_def)
  using subtype_tranclp_Collection_x by auto

lemma Set_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Set"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma OrderedSet_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) OrderedSet"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Bag_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Bag"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Sequence_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Sequence"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Tuple_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>) Tuple"
  apply (auto simp add: inj_def)
  using tranclp.cases by fastforce

lemma Required_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N) Required"
  by (auto simp add: inj_def)

lemma not_subtype_Optional_Required:
  "(\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ (Optional \<tau>) \<sigma> \<Longrightarrow> \<sigma> = Required \<rho> \<Longrightarrow> P"
  by (induct arbitrary: \<rho> rule: tranclp_induct; auto)

lemma Optional_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N) Optional"
  apply (auto simp add: inj_def)
  using not_subtype_Optional_Required by blast

lemma ErrorFree_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N\<^sub>E) ErrorFree"
  by (auto simp add: inj_def)

lemma not_subtype_Errorable_ErrorFree:
  "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ (Errorable \<tau>) \<sigma> \<Longrightarrow> \<sigma> = ErrorFree \<rho> \<Longrightarrow> P"
  by (induct arbitrary: \<rho> rule: tranclp_induct; auto)

lemma Errorable_bij_on_trancl [simp]:
  "bij_on_trancl (\<sqsubset>\<^sub>N\<^sub>E) Errorable"
  apply (auto simp add: inj_def)
  using not_subtype_Errorable_ErrorFree by blast

(*** Partial Order of Types *************************************************)

section \<open>Partial Order of Types\<close>

instantiation type :: (order) ord
begin
definition "(<) \<equiv> (\<sqsubset>)\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> (\<sqsubset>)\<^sup>*\<^sup>*"
instance ..
end

instantiation type\<^sub>N :: (order) ord
begin
definition "(<) \<equiv> (\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> (\<sqsubset>\<^sub>N)\<^sup>*\<^sup>*"
instance ..
end

instantiation type\<^sub>N\<^sub>E :: (order) ord
begin
definition "(<) \<equiv> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+"
definition "(\<le>) \<equiv> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>*"
instance ..
end

(*** Strict Introduction Rules **********************************************)

subsection \<open>Strict Introduction Rules\<close>
(*
lemma preserve_tranclp':
  "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow>
   (\<And>y. S (f y) (g y)) \<Longrightarrow>
   R\<^sup>+\<^sup>+ x y \<Longrightarrow> S\<^sup>+\<^sup>+ (f x) (g y)"
  by (metis preserve_tranclp tranclp.trancl_into_trancl)
*)
lemma type_less_x_OclAny_intro [intro]:
  "\<tau> \<noteq> OclAny \<Longrightarrow> \<tau> < OclAny"
  "\<tau>\<^sub>N \<noteq> Optional OclAny \<Longrightarrow> \<tau>\<^sub>N < Optional OclAny"
  "\<tau>\<^sub>N\<^sub>E \<noteq> OclAny[?!] \<Longrightarrow> \<tau>\<^sub>N\<^sub>E < OclAny[?!]"
  for \<tau> :: "'a :: order type"
  and \<tau>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
proof (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E)
  case OclAny thus ?case by simp
next
  case OclVoid
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid Boolean" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ Boolean OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case Boolean show ?case unfolding less_type_def by auto
next
  case Real show ?case unfolding less_type_def by auto
next
  case Integer
  have "(\<sqsubset>)\<^sup>+\<^sup>+ Integer Real" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ Real OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case UnlimitedNatural
  have "(\<sqsubset>)\<^sup>+\<^sup>+ UnlimitedNatural Integer" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ Integer Real" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ Real OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case String show ?case unfolding less_type_def by auto
next
  case (ObjectType \<C>) show ?case unfolding less_type_def by auto
next
  case (Enum \<E>) show ?case unfolding less_type_def by auto
next
  case (Collection \<tau>)
  from Collection.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclAny[?!])"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection OclAny[?!]) OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case (Set \<tau>)
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Set \<tau>) (Collection \<tau>)" by auto
  also from Set.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclAny[?!])"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection OclAny[?!]) OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case (OrderedSet \<tau>)
  have "(\<sqsubset>)\<^sup>*\<^sup>* (OrderedSet \<tau>) (Collection \<tau>)" by auto
  also from OrderedSet.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclAny[?!])"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection OclAny[?!]) OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case (Bag \<tau>)
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Bag \<tau>) (Collection \<tau>)" by auto
  also from Bag.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclAny[?!])"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection OclAny[?!]) OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case (Sequence \<tau>)
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Sequence \<tau>) (Collection \<tau>)" by auto
  also from Sequence.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Collection \<tau>) (Collection OclAny[?!])"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ (Collection OclAny[?!]) OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case (Tuple \<pi>) show ?case unfolding less_type_def by auto
next
  case (Required \<tau>)
  have "(\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ (Required \<tau>) (Optional \<tau>)" by auto
  also from Required.hyps
  have "(\<sqsubset>\<^sub>N)\<^sup>*\<^sup>* (Optional \<tau>) (Optional OclAny)"
    unfolding less_type_def
    by (rule_tac ?R="(\<sqsubset>)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  finally show ?case unfolding less_type\<^sub>N_def by simp
next
  case (Optional \<tau>) thus ?case
    unfolding less_type_def less_type\<^sub>N_def
    by (rule_tac ?R="(\<sqsubset>)" in preserve_tranclp, auto)
next
  case (ErrorFree \<tau>)
  have "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ (ErrorFree \<tau>) (Errorable \<tau>)" by auto
  also from ErrorFree.hyps
  have "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>* (Errorable \<tau>) OclAny[?!]"
    unfolding less_type\<^sub>N_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  finally show ?case unfolding less_type\<^sub>N\<^sub>E_def by simp
next
  case (Errorable \<tau>) thus ?case
    unfolding less_type\<^sub>N_def less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N)" in preserve_tranclp, auto)
qed

lemma type_less_OclVoid_x_intro [intro]:
  "\<tau> \<noteq> OclVoid \<Longrightarrow> OclVoid < \<tau>"
  "\<tau>\<^sub>N \<noteq> Required OclVoid \<Longrightarrow> Required OclVoid < \<tau>\<^sub>N"
  "\<tau>\<^sub>N\<^sub>E \<noteq> OclVoid[1] \<Longrightarrow> OclVoid[1] < \<tau>\<^sub>N\<^sub>E"
  for \<tau> :: "'a :: order type"
  and \<tau>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
proof (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E)
  case OclAny
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid Boolean" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ Boolean OclAny" by auto
  finally show ?case unfolding less_type_def by simp
next
  case OclVoid thus ?case by simp
next
  case Boolean show ?case unfolding less_type_def by auto
next
  case Real
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid UnlimitedNatural" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ UnlimitedNatural Integer" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ Integer Real" by auto
  finally show ?case unfolding less_type_def by simp
next
  case Integer
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid UnlimitedNatural" by auto
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ UnlimitedNatural Integer" by auto
  finally show ?case unfolding less_type_def by simp
next
  case UnlimitedNatural show ?case unfolding less_type_def by auto
next
  case String show ?case unfolding less_type_def by auto
next
  case (ObjectType \<C>) show ?case unfolding less_type_def by auto
next
  case (Enum \<E>) show ?case unfolding less_type_def by auto
next
  case (Collection \<tau>)
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid (Set OclVoid[1])" by auto
  also from Collection.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Set OclVoid[1]) (Set \<tau>)"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>)\<^sup>+\<^sup>+ (Set \<tau>) (Collection \<tau>)" by auto
  finally show ?case unfolding less_type_def by simp
next
  case (Set \<tau>)
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid (Set OclVoid[1])" by auto
  also from Set.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Set OclVoid[1]) (Set \<tau>)"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  finally show ?case unfolding less_type_def by simp
next
  case (OrderedSet \<tau>)
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid (OrderedSet OclVoid[1])" by auto
  also from OrderedSet.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (OrderedSet OclVoid[1]) (OrderedSet \<tau>)"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  finally show ?case unfolding less_type_def by simp
next
  case (Bag \<tau>)
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid (Bag OclVoid[1])" by auto
  also from Bag.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Bag OclVoid[1]) (Bag \<tau>)"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  finally show ?case unfolding less_type_def by simp
next
  case (Sequence \<tau>)
  have "(\<sqsubset>)\<^sup>+\<^sup>+ OclVoid (Sequence OclVoid[1])" by auto
  also from Sequence.hyps
  have "(\<sqsubset>)\<^sup>*\<^sup>* (Sequence OclVoid[1]) (Sequence \<tau>)"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N\<^sub>E)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  finally show ?case unfolding less_type_def by simp
next
  case (Tuple \<pi>) show ?case unfolding less_type_def by auto
next
  case (Required \<tau>) thus ?case
    unfolding less_type\<^sub>N_def less_type_def
    by (rule_tac ?f="Required" in preserve_tranclp; auto)
next
  case (Optional \<tau>)
  hence "(\<sqsubset>\<^sub>N)\<^sup>*\<^sup>* (Required OclVoid) (Required \<tau>)"
    unfolding less_type_def
    by (rule_tac ?R="(\<sqsubset>)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ (Required \<tau>) (Optional \<tau>)" by auto
  finally show ?case unfolding less_type\<^sub>N_def by simp
next
  case (ErrorFree \<tau>) thus ?case
    unfolding less_type\<^sub>N_def less_type\<^sub>N\<^sub>E_def
    by (rule_tac ?f="ErrorFree" in preserve_tranclp; auto)
next
  case (Errorable \<tau>)
  hence "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>* OclVoid[1] (ErrorFree \<tau>)"
    unfolding less_type\<^sub>N_def
    by (rule_tac ?R="(\<sqsubset>\<^sub>N)" in preserve_rtranclp;
        auto simp add: Nitpick.rtranclp_unfold)
  also have "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ (ErrorFree \<tau>) (Errorable \<tau>)" by auto
  finally show ?case unfolding less_type\<^sub>N\<^sub>E_def by simp
qed

lemma type_less_x_Real_intro [intro]:
  "\<tau> = Integer \<Longrightarrow> \<tau> < Real"
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> < Real"
  unfolding less_type_def
  by (rule rtranclp_into_tranclp2, auto)+

lemma type_less_x_Integer_intro [intro]:
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> < Integer"
  unfolding less_type_def
  by auto

lemma type_less_x_ObjectType_intro [intro]:
  "\<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> < \<D> \<Longrightarrow> \<tau> < \<langle>\<D>\<rangle>\<^sub>\<T>"
  unfolding less_type_def
  using dual_order.order_iff_strict by blast

lemma type_less_x_Collection_intro [intro]:
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def less_eq_type\<^sub>N\<^sub>E_def
  apply simp_all
  apply (rule_tac ?f="Collection" in preserve_tranclp; auto)
  apply (rule preserve_rtranclp''; auto)
  apply (rule preserve_rtranclp''; auto)
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_rtranclp''; auto)

lemma type_less_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Set \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < OrderedSet \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Bag \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Sequence \<sigma>"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def
  by simp (rule preserve_tranclp; auto)

lemma fun_or_eq_refl [intro]:
  "reflp (\<lambda>x y. f x y \<or> x = y)"
  by (simp add: reflpI)

lemma type_less_x_Tuple_intro [intro]:
  assumes "\<tau> = Tuple \<pi>"
      and "strict_subtuple (\<le>) \<pi> \<xi>"
    shows "\<tau> < Tuple \<xi>"
proof -
  have "subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>)\<^sup>*\<^sup>* \<pi> \<xi>"
    by (metis assms(2) less_eq_type\<^sub>N\<^sub>E_def rtranclp_eq_rtranclp)
  hence "(subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by simp (rule subtuple_to_trancl; auto)
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>))\<^sup>*\<^sup>* \<pi> \<xi>"
    by (simp add: tranclp_into_rtranclp)
  hence "(strict_subtuple (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>N\<^sub>E \<sigma> \<or> \<tau> = \<sigma>))\<^sup>+\<^sup>+ \<pi> \<xi>"
    by (meson assms(2) rtranclpD)
  thus ?thesis
    unfolding less_type_def
    using assms(1) apply simp
    by (rule preserve_tranclp; auto)
qed

lemma type_less_x_Required_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Required \<sigma>"
  unfolding less_type\<^sub>N_def less_type_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Optional_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Optional \<sigma>"
  "\<tau> = Optional \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Optional \<sigma>"
  unfolding less_type\<^sub>N_def less_type_def less_eq_type_def
  apply simp_all
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_tranclp; auto)

lemma type_less_x_ErrorFree_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < ErrorFree \<sigma>"
  unfolding less_type\<^sub>N\<^sub>E_def less_type\<^sub>N_def
  by simp (rule preserve_tranclp; auto)

lemma type_less_x_Errorable_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Errorable \<sigma>"
  "\<tau> = Errorable \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Errorable \<sigma>"
  unfolding less_type\<^sub>N\<^sub>E_def less_type\<^sub>N_def less_eq_type\<^sub>N_def
  apply simp_all
  apply (rule preserve_rtranclp''; auto)
  by (rule preserve_tranclp; auto)

(*** Strict Elimination Rules ***********************************************)

subsection \<open>Strict Elimination Rules\<close>

lemma type_less_x_OclAny [elim!]:
  "\<tau> < OclAny \<Longrightarrow> (\<tau> \<noteq> OclAny \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (drule tranclpD, auto)

lemma type_less_x_OclVoid [elim!]:
  "\<tau> < OclVoid \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_Boolean [elim!]:
  "\<tau> < Boolean \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_Real [elim!]:
  "\<tau> < Real \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_Integer [elim!]:
  "\<tau> < Integer \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_UnlimitedNatural [elim!]:
  "\<tau> < UnlimitedNatural \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_String [elim!]:
  "\<tau> < String \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_ObjectType [elim!]:
  "\<tau> < \<langle>\<D>\<rangle>\<^sub>\<T> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<C>. \<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> < \<D> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  using less_trans by auto

lemma type_less_x_Enum [elim!]:
  "\<tau> < Enum \<E> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: converse_tranclp_induct; auto)

lemma type_less_x_Collection [elim!]:
  "\<tau> < Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_type\<^sub>N\<^sub>E_def less_eq_type\<^sub>N\<^sub>E_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  by (erule subtype.cases;
      auto simp add: converse_rtranclp_into_rtranclp less_eq_type_def
                     tranclp_into_tranclp2 tranclp_into_rtranclp)

lemma type_less_x_Set [elim!]:
  assumes "\<tau> < Set \<sigma>"
      and "\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Set \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Set \<tau> < Set \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_OrderedSet [elim!]:
  assumes "\<tau> < OrderedSet \<sigma>"
      and "\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = OrderedSet \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. OrderedSet \<tau> < OrderedSet \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Bag [elim!]:
  assumes "\<tau> < Bag \<sigma>"
      and "\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Bag \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Bag \<tau> < Bag \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Sequence [elim!]:
  assumes "\<tau> < Sequence \<sigma>"
      and "\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Sequence \<rho> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Sequence \<tau> < Sequence \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Required [elim!]:
  assumes "\<tau> < Required \<sigma>"
      and "\<And>\<rho>. \<tau> = Required \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = Required \<rho>"
    unfolding less_type\<^sub>N_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. Required \<tau> < Required \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_type\<^sub>N_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
(*
lemma type_less_x_Optional [elim!]:
  assumes "\<tau> < \<sigma>[?]"
      and "\<tau> = OclVoid \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P"
      and "\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where
    "\<tau> = OclVoid \<or> \<tau> = \<rho>[1] \<or> \<tau> = \<rho>[?]"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[1] < \<sigma>[?] \<Longrightarrow> \<tau> \<le> \<sigma>"
    unfolding less_type_def less_eq_basic_type_def
    apply (drule tranclpD, auto)
    apply (erule subtype.cases, auto)
  moreover have "\<And>\<tau> \<sigma>. \<tau>[?] < \<sigma>[?] \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type_def less_basic_type_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed
*)
lemma type_less_x_Optional [elim!]:
  "\<tau> < Optional \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Optional \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type\<^sub>N_def less_type_def less_eq_type_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  apply (erule subtype\<^sub>N.cases;
      auto simp: converse_rtranclp_into_rtranclp tranclp_into_tranclp2)
  by (meson Nitpick.rtranclp_unfold)

lemma type_less_x_ErrorFree [elim!]:
  assumes "\<tau> < ErrorFree \<sigma>"
      and "\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<rho> where "\<tau> = ErrorFree \<rho>"
    unfolding less_type\<^sub>N\<^sub>E_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover have "\<And>\<tau> \<sigma>. ErrorFree \<tau> < ErrorFree \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
    unfolding less_type\<^sub>N_def less_type\<^sub>N\<^sub>E_def
    by (rule reflect_tranclp; auto)
  ultimately show ?thesis
    using assms by auto
qed

lemma type_less_x_Errorable [elim!]:
  "\<tau> < Errorable \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Errorable \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type\<^sub>N\<^sub>E_def less_type\<^sub>N_def less_eq_type\<^sub>N_def
  apply (induct rule: converse_tranclp_induct)
  apply auto[1]
  apply (erule subtype\<^sub>N\<^sub>E.cases;
      auto simp: converse_rtranclp_into_rtranclp tranclp_into_tranclp2)
  by (meson Nitpick.rtranclp_unfold)


text \<open>
  We will be able to remove the acyclicity assumption only after
  we prove that the subtype relation is acyclic.\<close>

lemma type_less_x_Tuple':
  assumes "\<tau> < Tuple \<xi>"
      and "acyclicP_on (fmran' \<xi>) (\<sqsubset>\<^sub>N\<^sub>E)"
      and "\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P"
      and "\<tau> = OclVoid \<Longrightarrow> P"
    shows "P"
proof -
  from assms(1) obtain \<pi> where "\<tau> = Tuple \<pi> \<or> \<tau> = OclVoid"
    unfolding less_type_def
    by (induct rule: converse_tranclp_induct; auto)
  moreover from assms(2) have
    "\<And>\<pi>. Tuple \<pi> < Tuple \<xi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi>"
    unfolding less_type_def less_eq_type\<^sub>N\<^sub>E_def
    by (rule_tac ?f="Tuple" in strict_subtuple_rtranclp_intro; auto)
  ultimately show ?thesis
    using assms by auto
qed

(*** Properties *************************************************************)

subsection \<open>Properties\<close>

lemma
  subtype_irrefl: "\<tau> < \<tau> \<Longrightarrow> False" and
  subtype\<^sub>N_irrefl: "\<tau>\<^sub>N < \<tau>\<^sub>N \<Longrightarrow> False" and
  subtype\<^sub>N\<^sub>E_irrefl: "\<tau>\<^sub>N\<^sub>E < \<tau>\<^sub>N\<^sub>E \<Longrightarrow> False"
  for \<tau> :: "'a :: order type"
  and \<tau>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  apply (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E, auto)
  by (erule type_less_x_Tuple'; auto simp add: less_type\<^sub>N\<^sub>E_def tranclp_unfold)

lemma subtype_acyclic:
  "acyclicP (\<sqsubset>)"
proof -
  have "\<nexists>\<tau>. (\<sqsubset>)\<^sup>+\<^sup>+ \<tau> \<tau>"
    by (metis (mono_tags) less_type_def OCL_Types.subtype_irrefl)
  thus ?thesis
    by (intro acyclicI) (simp add: trancl_def)
qed

lemma subtype\<^sub>N_acyclic:
  "acyclicP (\<sqsubset>\<^sub>N)"
proof -
  have "\<nexists>\<tau>. (\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ \<tau> \<tau>"
    by (metis (mono_tags) less_type\<^sub>N_def OCL_Types.subtype\<^sub>N_irrefl)
  thus ?thesis
    by (intro acyclicI) (simp add: trancl_def)
qed

lemma subtype\<^sub>N\<^sub>E_acyclic:
  "acyclicP (\<sqsubset>\<^sub>N\<^sub>E)"
proof -
  have "\<nexists>\<tau>. (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ \<tau> \<tau>"
    by (metis (mono_tags) less_type\<^sub>N\<^sub>E_def OCL_Types.subtype\<^sub>N\<^sub>E_irrefl)
  thus ?thesis
    by (intro acyclicI) (simp add: trancl_def)
qed

(*** Partial Order **********************************************************)

subsection \<open>Partial Order\<close>

instantiation type :: (order) order
begin

lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type"
proof -
  have "(\<sqsubset>)\<^sup>+\<^sup>+ \<tau> \<sigma> \<Longrightarrow> (\<sqsubset>)\<^sup>*\<^sup>* \<sigma> \<tau> \<Longrightarrow> False"
    by (metis (mono_tags) subtype_irrefl less_type_def tranclp_rtranclp_tranclp)
  moreover have "(\<sqsubset>)\<^sup>*\<^sup>* \<tau> \<sigma> \<Longrightarrow> \<not> (\<sqsubset>)\<^sup>*\<^sup>* \<sigma> \<tau> \<Longrightarrow> (\<sqsubset>)\<^sup>+\<^sup>+ \<tau> \<sigma>"
    by (metis rtranclpD)
  ultimately show ?thesis
    unfolding less_type_def less_eq_type_def by auto
qed

lemma order_refl_type:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type"
  unfolding less_eq_type_def by simp

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  unfolding less_eq_type_def by simp

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  unfolding less_eq_type_def less_type_def
  by (metis (mono_tags, lifting) less_eq_type_def
      less_le_not_le_type less_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp add: order_refl_type)
  using order_trans_type apply blast
  by (simp add: antisym_type)

end

instantiation type\<^sub>N :: (order) order
begin

lemma less_le_not_le_type\<^sub>N:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type\<^sub>N"
proof -
  have "(\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ \<tau> \<sigma> \<Longrightarrow> (\<sqsubset>\<^sub>N)\<^sup>*\<^sup>* \<sigma> \<tau> \<Longrightarrow> False"
    by (metis subtype\<^sub>N_irrefl less_type\<^sub>N_def tranclp_rtranclp_tranclp)
  moreover have "(\<sqsubset>\<^sub>N)\<^sup>*\<^sup>* \<tau> \<sigma> \<Longrightarrow> \<not> (\<sqsubset>\<^sub>N)\<^sup>*\<^sup>* \<sigma> \<tau> \<Longrightarrow> (\<sqsubset>\<^sub>N)\<^sup>+\<^sup>+ \<tau> \<sigma>"
    by (metis rtranclpD)
  ultimately show ?thesis
    unfolding less_type\<^sub>N_def less_eq_type\<^sub>N_def by auto
qed

lemma order_refl_type\<^sub>N:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type\<^sub>N"
  unfolding less_eq_type\<^sub>N_def by simp

lemma order_trans_type\<^sub>N:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type\<^sub>N"
  unfolding less_eq_type\<^sub>N_def by simp

lemma antisym_type\<^sub>N:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type\<^sub>N"
  unfolding less_eq_type\<^sub>N_def less_type\<^sub>N_def
  by (metis (mono_tags, lifting) less_eq_type\<^sub>N_def
      less_le_not_le_type\<^sub>N less_type\<^sub>N_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type\<^sub>N)
  apply (simp add: order_refl_type\<^sub>N)
  using order_trans_type\<^sub>N apply blast
  by (simp add: antisym_type\<^sub>N)

end

instantiation type\<^sub>N\<^sub>E :: (order) order
begin

lemma less_le_not_le_type\<^sub>N\<^sub>E:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type\<^sub>N\<^sub>E"
proof -
  have "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ \<tau> \<sigma> \<Longrightarrow> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>* \<sigma> \<tau> \<Longrightarrow> False"
    by (metis (mono_tags) subtype\<^sub>N\<^sub>E_irrefl less_type\<^sub>N\<^sub>E_def tranclp_rtranclp_tranclp)
  moreover have "(\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>* \<tau> \<sigma> \<Longrightarrow> \<not> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>*\<^sup>* \<sigma> \<tau> \<Longrightarrow> (\<sqsubset>\<^sub>N\<^sub>E)\<^sup>+\<^sup>+ \<tau> \<sigma>"
    by (metis rtranclpD)
  ultimately show ?thesis
    unfolding less_type\<^sub>N\<^sub>E_def less_eq_type\<^sub>N\<^sub>E_def by auto
qed

lemma order_refl_type\<^sub>N\<^sub>E:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type\<^sub>N\<^sub>E"
  unfolding less_eq_type\<^sub>N\<^sub>E_def by simp

lemma order_trans_type\<^sub>N\<^sub>E:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type\<^sub>N\<^sub>E"
  unfolding less_eq_type\<^sub>N\<^sub>E_def by simp

lemma antisym_type\<^sub>N\<^sub>E:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type\<^sub>N\<^sub>E"
  unfolding less_eq_type\<^sub>N\<^sub>E_def less_type\<^sub>N_def
  by (metis (mono_tags, lifting) less_eq_type\<^sub>N\<^sub>E_def
      less_le_not_le_type\<^sub>N\<^sub>E less_type\<^sub>N\<^sub>E_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type\<^sub>N\<^sub>E)
  apply (simp add: order_refl_type\<^sub>N\<^sub>E)
  using order_trans_type\<^sub>N\<^sub>E apply blast
  by (simp add: antisym_type\<^sub>N\<^sub>E)

end

(*** Non-Strict Introduction Rules ******************************************)

subsection \<open>Non-Strict Introduction Rules\<close>

lemma type_less_eq_x_OclAny_intro [intro]:
  "\<tau> \<le> OclAny"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_OclVoid_x_intro [intro]:
  "OclVoid \<le> \<tau>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Real_intro [intro]:
  "\<tau> = Real \<Longrightarrow> \<tau> \<le> Real"
  "\<tau> = Integer \<Longrightarrow> \<tau> \<le> Real"
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> \<le> Real"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Integer_intro [intro]:
  "\<tau> = Integer \<Longrightarrow> \<tau> \<le> Integer"
  "\<tau> = UnlimitedNatural \<Longrightarrow> \<tau> \<le> Integer"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_ObjectType_intro [intro]:
  "\<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> \<le> \<D> \<Longrightarrow> \<tau> \<le> \<langle>\<D>\<rangle>\<^sub>\<T>"
  unfolding dual_order.order_iff_strict by auto

lemma type_less_eq_x_Collection_intro [intro]:
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_Set_intro [intro]:
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_OrderedSet_intro [intro]:
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_Bag_intro [intro]:
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_Sequence_intro [intro]:
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_Tuple_intro [intro]:
  "\<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> \<tau> \<le> Tuple \<xi>"
  using order.strict_iff_order by blast

lemma type_less_eq_x_Required_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Required \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_Optional_intro [intro]:
  "\<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Optional \<sigma>"
  "\<tau> = Optional \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Optional \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_ErrorFree_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> ErrorFree \<sigma>"
  unfolding order.order_iff_strict by auto

lemma type_less_eq_x_Errorable_intro [intro]:
  "\<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Errorable \<sigma>"
  "\<tau> = Errorable \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Errorable \<sigma>"
  unfolding order.order_iff_strict by auto

(*** Non-Strict Elimination Rules *******************************************)

subsection \<open>Non-Strict Elimination Rules\<close>

lemma type_less_eq_x_OclVoid [elim!]:
  "\<tau> \<le> OclVoid \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Boolean [elim!]:
  "\<tau> \<le> Boolean \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Boolean \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Real [elim!]:
  "\<tau> \<le> Real \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Real \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Integer [elim!]:
  "\<tau> \<le> Integer \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Integer \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_UnlimitedNatural [elim!]:
  "\<tau> \<le> UnlimitedNatural \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = UnlimitedNatural \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_String [elim!]:
  "\<tau> \<le> String \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = String \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_ObjectType [elim!]:
  "\<tau> \<le> \<langle>\<D>\<rangle>\<^sub>\<T> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<C>. \<tau> = \<langle>\<C>\<rangle>\<^sub>\<T> \<Longrightarrow> \<C> \<le> \<D> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Enum [elim!]:
  "\<tau> \<le> Enum \<E> \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = Enum \<E> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Collection [elim!]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Set [elim!]:
  "\<tau> \<le> Set \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_OrderedSet [elim!]:
  "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Bag [elim!]:
  "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Sequence [elim!]:
  "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_x_Tuple [elim!]:
  "\<tau> < Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> strict_subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  apply (erule type_less_x_Tuple')
  apply (meson acyclic_def subtype\<^sub>N\<^sub>E_acyclic)
  by simp

lemma type_less_eq_x_Tuple [elim!]:
  "\<tau> \<le> Tuple \<xi> \<Longrightarrow>
   (\<And>\<pi>. \<tau> = Tuple \<pi> \<Longrightarrow> subtuple (\<le>) \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule le_imp_less_or_eq, auto)
  by (simp add: fmap.rel_refl fmrel_to_subtuple)

lemma type_less_eq_x_Required [elim!]:
  "\<tau> \<le> Required \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Optional [elim!]:
  "\<tau> \<le> Optional \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Required \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Optional \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_ErrorFree [elim!]:
  "\<tau> \<le> ErrorFree \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

lemma type_less_eq_x_Errorable [elim!]:
  "\<tau> \<le> Errorable \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<tau> = ErrorFree \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Errorable \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (drule le_imp_less_or_eq; auto)

(*** Simplification Rules ***************************************************)

subsection \<open>Simplification Rules\<close>

text \<open>
  We can not declare @{thm Orderings.order_class.le_less} as
  a simplification theorem for two arbitrary types, because it is too aggressive.
  So we define a specific simplification rules for @{text "(\<le>)"} operator.}\<close>

lemma type_less_left_simps [simp]:
  "OclAny < \<sigma> = False"
  "OclVoid < \<sigma> = (\<sigma> \<noteq> OclVoid)"

  "Boolean < \<sigma> = (\<sigma> = OclAny)"
  "Real < \<sigma> = (\<sigma> = OclAny)"
  "Integer < \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Real)"
  "UnlimitedNatural < \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Real \<or> \<sigma> = Integer)"
  "String < \<sigma> = (\<sigma> = OclAny)"

  "ObjectType \<C> < \<sigma> = (\<exists>\<D>. \<sigma> = OclAny \<or> \<sigma> = ObjectType \<D> \<and> \<C> < \<D>)"
  "Enum \<E> < \<sigma> = (\<sigma> = OclAny)"

  "Collection \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> < \<phi>)"
  "Set \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Set \<phi> \<and> \<tau> < \<phi>)"
  "OrderedSet \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = OrderedSet \<phi> \<and> \<tau> < \<phi>)"
  "Bag \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Bag \<phi> \<and> \<tau> < \<phi>)"
  "Sequence \<tau> < \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Sequence \<phi> \<and> \<tau> < \<phi>)"

  "Tuple \<pi> < \<sigma> = (\<exists>\<xi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Tuple \<xi> \<and> strict_subtuple (\<le>) \<pi> \<xi>)"
  by (induct \<sigma>; auto)+

lemma type_less_eq_left_simps [simp]:
  "OclAny \<le> \<sigma> = (\<sigma> = OclAny)"
  "OclVoid \<le> \<sigma> = True"

  "Boolean \<le> \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Boolean)"
  "Real \<le> \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Real)"
  "Integer \<le> \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Real \<or> \<sigma> = Integer)"
  "UnlimitedNatural \<le> \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Real \<or> \<sigma> = Integer \<or> \<sigma> = UnlimitedNatural)"
  "String \<le> \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = String)"

  "ObjectType \<C> \<le> \<sigma> = (\<exists>\<D>. \<sigma> = OclAny \<or> \<sigma> = ObjectType \<D> \<and> \<C> \<le> \<D>)"
  "Enum \<E> \<le> \<sigma> = (\<sigma> = OclAny \<or> \<sigma> = Enum \<E>)"

  "Collection \<tau> \<le> \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi>)"
  "Set \<tau> \<le> \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Set \<phi> \<and> \<tau> \<le> \<phi>)"
  "OrderedSet \<tau> \<le> \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = OrderedSet \<phi> \<and> \<tau> \<le> \<phi>)"
  "Bag \<tau> \<le> \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Bag \<phi> \<and> \<tau> \<le> \<phi>)"
  "Sequence \<tau> \<le> \<sigma> = (\<exists>\<phi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Collection \<phi> \<and> \<tau> \<le> \<phi> \<or>
      \<sigma> = Sequence \<phi> \<and> \<tau> \<le> \<phi>)"

  "Tuple \<pi> \<le> \<sigma> = (\<exists>\<xi>.
      \<sigma> = OclAny \<or>
      \<sigma> = Tuple \<xi> \<and> subtuple (\<le>) \<pi> \<xi>)"
  by (auto simp: order.order_iff_strict reflpI)

lemma type\<^sub>N_less_left_simps [simp]:
  "Required \<rho> < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Required \<upsilon> \<and> \<rho> < \<upsilon> \<or>
      \<sigma> = Optional \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  "Optional \<rho> < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Optional \<upsilon> \<and> \<rho> < \<upsilon>)"
  by (induct \<sigma>; auto)+

lemma type\<^sub>N_less_eq_left_simps [simp]:
  "Required \<rho> \<le> \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Required \<upsilon> \<and> \<rho> \<le> \<upsilon> \<or>
      \<sigma> = Optional \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  "Optional \<rho> \<le> \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Optional \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  by (auto simp: dual_order.order_iff_strict)

lemma type\<^sub>N\<^sub>E_less_left_simps [simp]:
  "ErrorFree \<rho> < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = ErrorFree \<upsilon> \<and> \<rho> < \<upsilon> \<or>
      \<sigma> = Errorable \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  "Errorable \<rho> < \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Errorable \<upsilon> \<and> \<rho> < \<upsilon>)"
  by (induct \<sigma>; auto)+

lemma type\<^sub>N\<^sub>E_less_eq_left_simps [simp]:
  "ErrorFree \<rho> \<le> \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = ErrorFree \<upsilon> \<and> \<rho> \<le> \<upsilon> \<or>
      \<sigma> = Errorable \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  "Errorable \<rho> \<le> \<sigma> = (\<exists>\<upsilon>.
      \<sigma> = Errorable \<upsilon> \<and> \<rho> \<le> \<upsilon>)"
  by (auto simp: dual_order.order_iff_strict)

lemma type_less_right_simps [simp]:
  "\<tau> < OclAny = (\<tau> \<noteq> OclAny)"
  "\<tau> < OclVoid = False"

  "\<tau> < Boolean = (\<tau> = OclVoid)"
  "\<tau> < Real = (\<tau> = Integer \<or> \<tau> = UnlimitedNatural \<or> \<tau> = OclVoid)"
  "\<tau> < Integer = (\<tau> = UnlimitedNatural \<or> \<tau> = OclVoid)"
  "\<tau> < UnlimitedNatural = (\<tau> = OclVoid)"
  "\<tau> < String = (\<tau> = OclVoid)"

  "\<tau> < ObjectType \<D> = (\<exists>\<C>. \<tau> = ObjectType \<C> \<and> \<C> < \<D> \<or> \<tau> = OclVoid)"
  "\<tau> < Enum \<E> = (\<tau> = OclVoid)"

  "\<tau> < Collection \<sigma> = (\<exists>\<phi>.
      \<tau> = Collection \<phi> \<and> \<phi> < \<sigma> \<or>
      \<tau> = Set \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = OrderedSet \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Bag \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Sequence \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = OclVoid)"
  "\<tau> < Set \<sigma> = (\<exists>\<phi>. \<tau> = Set \<phi> \<and> \<phi> < \<sigma> \<or> \<tau> = OclVoid)"
  "\<tau> < OrderedSet \<sigma> = (\<exists>\<phi>. \<tau> = OrderedSet \<phi> \<and> \<phi> < \<sigma> \<or> \<tau> = OclVoid)"
  "\<tau> < Bag \<sigma> = (\<exists>\<phi>. \<tau> = Bag \<phi> \<and> \<phi> < \<sigma> \<or> \<tau> = OclVoid)"
  "\<tau> < Sequence \<sigma> = (\<exists>\<phi>. \<tau> = Sequence \<phi> \<and> \<phi> < \<sigma> \<or> \<tau> = OclVoid)"

  "\<tau> < Tuple \<xi> = (\<exists>\<pi>. \<tau> = Tuple \<pi> \<and> strict_subtuple (\<le>) \<pi> \<xi> \<or> \<tau> = OclVoid)"
  by auto

lemma type_less_eq_right_simps [simp]:
  "\<tau> \<le> OclAny = True"
  "\<tau> \<le> OclVoid = (\<tau> = OclVoid)"

  "\<tau> \<le> Boolean = (\<tau> = Boolean \<or> \<tau> = OclVoid)"
  "\<tau> \<le> Real = (\<tau> = Real \<or> \<tau> = Integer \<or> \<tau> = UnlimitedNatural \<or> \<tau> = OclVoid)"
  "\<tau> \<le> Integer = (\<tau> = Integer \<or> \<tau> = UnlimitedNatural \<or> \<tau> = OclVoid)"
  "\<tau> \<le> UnlimitedNatural = (\<tau> = UnlimitedNatural \<or> \<tau> = OclVoid)"
  "\<tau> \<le> String = (\<tau> = String \<or> \<tau> = OclVoid)"

  "\<tau> \<le> ObjectType \<D> = (\<exists>\<C>. \<tau> = ObjectType \<C> \<and> \<C> \<le> \<D> \<or> \<tau> = OclVoid)"
  "\<tau> \<le> Enum \<E> = (\<tau> = Enum \<E> \<or> \<tau> = OclVoid)"

  "\<tau> \<le> Collection \<sigma> = (\<exists>\<phi>.
      \<tau> = Collection \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Set \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = OrderedSet \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Bag \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = Sequence \<phi> \<and> \<phi> \<le> \<sigma> \<or>
      \<tau> = OclVoid)"
  "\<tau> \<le> Set \<sigma> = (\<exists>\<phi>. \<tau> = Set \<phi> \<and> \<phi> \<le> \<sigma> \<or> \<tau> = OclVoid)"
  "\<tau> \<le> OrderedSet \<sigma> = (\<exists>\<phi>. \<tau> = OrderedSet \<phi> \<and> \<phi> \<le> \<sigma> \<or> \<tau> = OclVoid)"
  "\<tau> \<le> Bag \<sigma> = (\<exists>\<phi>. \<tau> = Bag \<phi> \<and> \<phi> \<le> \<sigma> \<or> \<tau> = OclVoid)"
  "\<tau> \<le> Sequence \<sigma> = (\<exists>\<phi>. \<tau> = Sequence \<phi> \<and> \<phi> \<le> \<sigma> \<or> \<tau> = OclVoid)"

  "\<tau> \<le> Tuple \<xi> = (\<exists>\<pi>. \<tau> = Tuple \<pi> \<and> subtuple (\<le>) \<pi> \<xi> \<or> \<tau> = OclVoid)"
  by (auto simp: order.order_iff_strict reflpI)

lemma type\<^sub>N_less_right_simps [simp]:
  "\<tau> < Required \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> < \<upsilon>)"
  "\<tau> < Optional \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Optional \<rho> \<and> \<rho> < \<upsilon>)"
  by auto

lemma type\<^sub>N_less_eq_right_simps [simp]:
  "\<tau> \<le> Required \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> \<le> \<upsilon>)"
  "\<tau> \<le> Optional \<upsilon> = (\<exists>\<rho>. \<tau> = Required \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Optional \<rho> \<and> \<rho> \<le> \<upsilon>)"
  by auto

lemma type\<^sub>N\<^sub>E_less_right_simps [simp]:
  "\<tau> < ErrorFree \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> < \<upsilon>)"
  "\<tau> < Errorable \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Errorable \<rho> \<and> \<rho> < \<upsilon>)"
  by auto

lemma type\<^sub>N\<^sub>E_less_eq_right_simps [simp]:
  "\<tau> \<le> ErrorFree \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> \<le> \<upsilon>)"
  "\<tau> \<le> Errorable \<upsilon> = (\<exists>\<rho>. \<tau> = ErrorFree \<rho> \<and> \<rho> \<le> \<upsilon> \<or> \<tau> = Errorable \<rho> \<and> \<rho> \<le> \<upsilon>)"
  by auto

(*** Upper Semilattice of Types *********************************************)

section \<open>Upper Semilattice of Types\<close>
(*
notation sup (infixl "\<squnion>" 65)

instantiation type :: (order) sup
begin
*)

fun type_sup (infixl "\<squnion>\<^sub>T" 65)
and type_sup\<^sub>N (infixl "\<squnion>\<^sub>N" 65)
and type_sup\<^sub>N\<^sub>E (infixl "\<squnion>\<^sub>N\<^sub>E" 65) where
  "OclAny \<squnion>\<^sub>T \<sigma> = OclAny"
| "OclVoid \<squnion>\<^sub>T \<sigma> = \<sigma>"

| "Boolean \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Boolean \<Rightarrow> Boolean
     | OclVoid \<Rightarrow> Boolean
     | _ \<Rightarrow> OclAny)"
| "Real \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Real \<Rightarrow> Real
     | Integer \<Rightarrow> Real
     | UnlimitedNatural \<Rightarrow> Real
     | OclVoid \<Rightarrow> Real
     | _ \<Rightarrow> OclAny)"
| "Integer \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Real \<Rightarrow> Real
     | Integer \<Rightarrow> Integer
     | UnlimitedNatural \<Rightarrow> Integer
     | OclVoid \<Rightarrow> Integer
     | _ \<Rightarrow> OclAny)"
| "UnlimitedNatural \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Real \<Rightarrow> Real
     | Integer \<Rightarrow> Integer
     | UnlimitedNatural \<Rightarrow> UnlimitedNatural
     | OclVoid \<Rightarrow> UnlimitedNatural
     | _ \<Rightarrow> OclAny)"
| "String \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of String \<Rightarrow> String
     | OclVoid \<Rightarrow> String
     | _ \<Rightarrow> OclAny)"

| "\<langle>\<C>\<rangle>\<^sub>\<T> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of \<langle>\<D>\<rangle>\<^sub>\<T> \<Rightarrow> \<langle>sup \<C> \<D>\<rangle>\<^sub>\<T>
     | OclVoid \<Rightarrow> \<langle>\<C>\<rangle>\<^sub>\<T>
     | _ \<Rightarrow> OclAny)"
| "Enum \<E> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Enum \<E>' \<Rightarrow> if \<E> = \<E>' then Enum \<E> else OclAny
     | OclVoid \<Rightarrow> Enum \<E>
     | _ \<Rightarrow> OclAny)"

| "Collection \<tau> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OclVoid \<Rightarrow> Collection \<tau>
     | _ \<Rightarrow> OclAny)"
| "Set \<tau> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Set \<rho> \<Rightarrow> Set (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OclVoid \<Rightarrow> Set \<tau>
     | _ \<Rightarrow> OclAny)"
| "OrderedSet \<tau> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OrderedSet \<rho> \<Rightarrow> OrderedSet (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OclVoid \<Rightarrow> OrderedSet \<tau>
     | _ \<Rightarrow> OclAny)"
| "Bag \<tau> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Bag \<rho> \<Rightarrow> Bag (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Sequence \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OclVoid \<Rightarrow> Bag \<tau>
     | _ \<Rightarrow> OclAny)"
| "Sequence \<tau> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Collection \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Set \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OrderedSet \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Bag \<rho> \<Rightarrow> Collection (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | Sequence \<rho> \<Rightarrow> Sequence (\<tau> \<squnion>\<^sub>N\<^sub>E \<rho>)
     | OclVoid \<Rightarrow> Sequence \<tau>
     | _ \<Rightarrow> OclAny)"

| "Tuple \<pi> \<squnion>\<^sub>T \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> Tuple (fmmerge_fun (\<squnion>\<^sub>N\<^sub>E) \<pi> \<xi>)
     | OclVoid \<Rightarrow> Tuple \<pi>
     | _ \<Rightarrow> OclAny)"

| "Required \<tau> \<squnion>\<^sub>N \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Required (\<tau> \<squnion>\<^sub>T \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion>\<^sub>T \<rho>))"
| "Optional \<tau> \<squnion>\<^sub>N \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> Optional (\<tau> \<squnion>\<^sub>T \<rho>)
     | Optional \<rho> \<Rightarrow> Optional (\<tau> \<squnion>\<^sub>T \<rho>))"

| "ErrorFree \<tau> \<squnion>\<^sub>N\<^sub>E \<sigma> = (case \<sigma>
    of ErrorFree \<rho> \<Rightarrow> ErrorFree (\<tau> \<squnion>\<^sub>N \<rho>)
     | Errorable \<rho> \<Rightarrow> Errorable (\<tau> \<squnion>\<^sub>N \<rho>))"
| "Errorable \<tau> \<squnion>\<^sub>N\<^sub>E \<sigma> = (case \<sigma>
    of ErrorFree \<rho> \<Rightarrow> Errorable (\<tau> \<squnion>\<^sub>N \<rho>)
     | Errorable \<rho> \<Rightarrow> Errorable (\<tau> \<squnion>\<^sub>N \<rho>))"

print_theorems

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion>\<^sub>T \<sigma>"
  "\<tau>\<^sub>N \<le> \<tau>\<^sub>N \<squnion>\<^sub>N \<sigma>\<^sub>N"
  "\<tau>\<^sub>N\<^sub>E \<le> \<tau>\<^sub>N\<^sub>E \<squnion>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a::{order,semilattice_sup} type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
proof (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E arbitrary: \<sigma> and \<sigma>\<^sub>N and \<sigma>\<^sub>N\<^sub>E)
  case OclAny show ?case by auto
next
  case OclVoid show ?case by auto
next
  case Boolean show ?case by (cases \<sigma>; auto)
next
  case Real show ?case by (cases \<sigma>; auto)
next
  case Integer show ?case by (cases \<sigma>; auto)
next
  case UnlimitedNatural show ?case by (cases \<sigma>; auto)
next
  case String show ?case by (cases \<sigma>; auto)
next
  case (ObjectType \<C>) show ?case by (cases \<sigma>; auto)
next
  case (Enum \<E>) show ?case by (cases \<sigma>; auto)
next
  case (Collection \<tau>) thus ?case by (cases \<sigma>; auto)
next
  case (Set \<tau>) thus ?case by (cases \<sigma>; auto)
next
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; auto)
next
  case (Bag \<tau>) thus ?case by (cases \<sigma>; auto)
next
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; auto)
next
  case (Tuple \<pi>) thus ?case by (cases \<sigma>;
    auto simp del: type_less_eq_left_simps type_less_eq_right_simps)
next
  case (Required \<tau>) thus ?case by (cases \<sigma>\<^sub>N; auto)
next
  case (Optional \<tau>) thus ?case by (cases \<sigma>\<^sub>N; auto)
next
  case (ErrorFree \<tau>) thus ?case by (cases \<sigma>\<^sub>N\<^sub>E; auto)
next
  case (Errorable \<tau>) thus ?case by (cases \<sigma>\<^sub>N\<^sub>E; auto)
qed

lemma sup_commut_type:
  "\<tau> \<squnion>\<^sub>T \<sigma> = \<sigma> \<squnion>\<^sub>T \<tau>"
  "\<tau>\<^sub>N \<squnion>\<^sub>N \<sigma>\<^sub>N = \<sigma>\<^sub>N \<squnion>\<^sub>N \<tau>\<^sub>N"
  "\<tau>\<^sub>N\<^sub>E \<squnion>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E = \<sigma>\<^sub>N\<^sub>E \<squnion>\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a::semilattice_sup type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
proof (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E arbitrary: \<sigma> and \<sigma>\<^sub>N and \<sigma>\<^sub>N\<^sub>E)
  case OclAny show ?case by (cases \<sigma>; simp)
next
  case OclVoid show ?case by (cases \<sigma>; simp)
next
  case Boolean show ?case by (cases \<sigma>; simp)
next
  case Real show ?case by (cases \<sigma>; simp)
next
  case Integer show ?case by (cases \<sigma>; simp)
next
  case UnlimitedNatural show ?case by (cases \<sigma>; simp)
next
  case String show ?case by (cases \<sigma>; simp)
next
  case (ObjectType \<C>) show ?case by (cases \<sigma>; simp add: sup_commute)
next
  case (Enum \<E>) show ?case by (cases \<sigma>; simp)
next
  case (Collection \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Set \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Bag \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; simp)
next
  case (Tuple \<pi>) thus ?case apply (cases \<sigma>; simp)
    using fmmerge_commut by blast
next
  case (Required \<tau>) thus ?case by (cases \<sigma>\<^sub>N; simp)
next
  case (Optional \<tau>) thus ?case by (cases \<sigma>\<^sub>N; simp)
next
  case (ErrorFree \<tau>) thus ?case by (cases \<sigma>\<^sub>N\<^sub>E; simp)
next
  case (Errorable \<tau>) thus ?case by (cases \<sigma>\<^sub>N\<^sub>E; simp)
qed

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion>\<^sub>T \<sigma> \<le> \<rho>"
  "\<tau>\<^sub>N \<le> \<rho>\<^sub>N \<Longrightarrow> \<sigma>\<^sub>N \<le> \<rho>\<^sub>N \<Longrightarrow> \<tau>\<^sub>N \<squnion>\<^sub>N \<sigma>\<^sub>N \<le> \<rho>\<^sub>N"
  "\<tau>\<^sub>N\<^sub>E \<le> \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E \<le> \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<tau>\<^sub>N\<^sub>E \<squnion>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<le> \<rho>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> \<rho> :: "'a::semilattice_sup type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N \<rho>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  by (induct \<rho> and \<rho>\<^sub>N and \<rho>\<^sub>N\<^sub>E arbitrary: \<tau> \<sigma> and \<tau>\<^sub>N \<sigma>\<^sub>N and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E,
      auto simp: fmrel_on_fset_fmmerge1)

no_notation type_sup (infixl "\<squnion>" 65)
no_notation type_sup\<^sub>N (infixl "\<squnion>\<^sub>N" 65)
no_notation type_sup\<^sub>N\<^sub>E (infixl "\<squnion>\<^sub>N\<^sub>E" 65)

notation sup (infixl "\<squnion>" 65)

instantiation type :: (semilattice_sup) semilattice_sup
begin
definition sup_type where [simp, code]: "sup_type \<equiv> type_sup"
instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)
end

instantiation type\<^sub>N :: (semilattice_sup) semilattice_sup
begin
definition sup_type\<^sub>N where [simp, code]: "sup_type\<^sub>N \<equiv> type_sup\<^sub>N"
instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)
end

instantiation type\<^sub>N\<^sub>E :: (semilattice_sup) semilattice_sup
begin
definition sup_type\<^sub>N\<^sub>E where [simp, code]: "sup_type\<^sub>N\<^sub>E \<equiv> type_sup\<^sub>N\<^sub>E"
instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)
end

(*** Helper Relations *******************************************************)

section \<open>Helper Relations\<close>

abbreviation between ("_/ = _\<midarrow>_"  [51, 51, 51] 50) where
  "x = y\<midarrow>z \<equiv> y \<le> x \<and> x \<le> z"
(*
abbreviation "Collection\<^sub>N\<^sub>E \<tau> opt err \<equiv>
  if opt then
    if err
    then Errorable (Optional (Collection \<tau>))
    else ErrorFree (Optional (Collection \<tau>))
  else if err
    then Errorable (Required (Collection \<tau>))
    else ErrorFree (Required (Collection \<tau>))"

abbreviation "Set\<^sub>N\<^sub>E \<tau> opt err \<equiv>
  if opt then
    if err
    then Errorable (Optional (Set \<tau>))
    else ErrorFree (Optional (Set \<tau>))
  else if err
    then Errorable (Required (Set \<tau>))
    else ErrorFree (Required (Set \<tau>))"

abbreviation "OrderedSet\<^sub>N\<^sub>E \<tau> opt err \<equiv>
  if opt then
    if err
    then Errorable (Optional (OrderedSet \<tau>))
    else ErrorFree (Optional (OrderedSet \<tau>))
  else if err
    then Errorable (Required (OrderedSet \<tau>))
    else ErrorFree (Required (OrderedSet \<tau>))"

abbreviation "Bag\<^sub>N\<^sub>E \<tau> opt err \<equiv>
  if opt then
    if err
    then Errorable (Optional (Bag \<tau>))
    else ErrorFree (Optional (Bag \<tau>))
  else if err
    then Errorable (Required (Bag \<tau>))
    else ErrorFree (Required (Bag \<tau>))"

abbreviation "Sequence\<^sub>N\<^sub>E \<tau> opt err \<equiv>
  if opt then
    if err
    then Errorable (Optional (Sequence \<tau>))
    else ErrorFree (Optional (Sequence \<tau>))
  else if err
    then Errorable (Required (Sequence \<tau>))
    else ErrorFree (Required (Sequence \<tau>))"
*)
(*
inductive element_type :: "'a type \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool"
      and element_type\<^sub>N :: "'a type\<^sub>N \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool"
      and element_type\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool" where
  "element_type (Collection \<tau>) \<tau>"
| "element_type (Set \<tau>) \<tau>"
| "element_type (OrderedSet \<tau>) \<tau>"
| "element_type (Bag \<tau>) \<tau>"
| "element_type (Sequence \<tau>) \<tau>"

| "element_type \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N (Required \<tau>) \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N (Optional \<tau>) \<sigma>"

| "element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N\<^sub>E (ErrorFree \<tau>) \<sigma>"
| "element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N\<^sub>E (Errorable \<tau>) \<sigma>"
*)
(*
inductive element_type where
  "element_type (Collection\<^sub>N\<^sub>E \<tau>) \<tau>"
| "element_type (Set\<^sub>N\<^sub>E \<tau>) \<tau>"
| "element_type (OrderedSet\<^sub>N\<^sub>E \<tau>) \<tau>"
| "element_type (Bag\<^sub>N\<^sub>E \<tau>) \<tau>"
| "element_type (Sequence\<^sub>N\<^sub>E \<tau>) \<tau>"
*)
inductive element_type
      and element_type\<^sub>N
      and element_type\<^sub>N\<^sub>E where
  "element_type (Collection \<tau>) \<tau>"
| "element_type (Set \<tau>) \<tau>"
| "element_type (OrderedSet \<tau>) \<tau>"
| "element_type (Bag \<tau>) \<tau>"
| "element_type (Sequence \<tau>) \<tau>"

| "element_type \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N (Required \<tau>) \<sigma>"
| "element_type \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N (Optional \<tau>) \<sigma>"

| "element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N\<^sub>E (ErrorFree \<tau>) \<sigma>"
| "element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   element_type\<^sub>N\<^sub>E (Errorable \<tau>) \<sigma>"

print_theorems

lemma element_type_alt_simps:
  "element_type \<tau> \<sigma> = 
     (Collection \<sigma> = \<tau> \<or>
      Set \<sigma> = \<tau> \<or>
      OrderedSet \<sigma> = \<tau> \<or>
      Bag \<sigma> = \<tau> \<or>
      Sequence \<sigma> = \<tau>)"
  by (auto simp add: element_type.simps)

inductive is_collection\<^sub>N\<^sub>E where
  "element_type\<^sub>N\<^sub>E \<tau> \<sigma> \<Longrightarrow>
   is_collection\<^sub>N\<^sub>E \<tau>"

inductive to_single_type\<^sub>N\<^sub>E where
  "\<not> is_collection\<^sub>N\<^sub>E \<tau> \<Longrightarrow>
   to_single_type\<^sub>N\<^sub>E \<tau> \<tau>"
| "element_type\<^sub>N\<^sub>E \<tau> \<sigma> \<Longrightarrow> to_single_type\<^sub>N\<^sub>E \<sigma> \<rho> \<Longrightarrow>
   to_single_type\<^sub>N\<^sub>E \<tau> \<rho>"

inductive inner_element_type\<^sub>N\<^sub>E where
  "element_type\<^sub>N\<^sub>E \<tau> \<sigma> \<Longrightarrow>
   to_single_type\<^sub>N\<^sub>E \<sigma> \<rho> \<Longrightarrow>
   inner_element_type\<^sub>N\<^sub>E \<tau> \<rho>"

code_pred [show_modes] inner_element_type\<^sub>N\<^sub>E .

values "{x. inner_element_type\<^sub>N\<^sub>E (Boolean[?] :: nat type\<^sub>N\<^sub>E) x}"
values "{x. inner_element_type\<^sub>N\<^sub>E (Set (Boolean[?] :: nat type\<^sub>N\<^sub>E))[?!] x}"
values "{x. inner_element_type\<^sub>N\<^sub>E (Sequence (Set (Integer[1!] :: nat type\<^sub>N\<^sub>E))[?!])[1] x}"
values "{x. inner_element_type\<^sub>N\<^sub>E (Bag (Sequence (Set (Real[1] :: nat type\<^sub>N\<^sub>E))[?!])[1])[?] x}"

(*
inductive inner_element_type
      and inner_element_type\<^sub>N
      and inner_element_type\<^sub>N\<^sub>E
      and inner_element_type' where
  "\<not> element_type \<tau> \<sigma> \<Longrightarrow>
   inner_element_type' \<tau> \<tau>"

| "inner_element_type (Collection \<tau>) \<tau>"
| "inner_element_type (Set \<tau>) \<tau>"
| "inner_element_type (OrderedSet \<tau>) \<tau>"
| "inner_element_type (Bag \<tau>) \<tau>"
| "inner_element_type (Sequence \<tau>) \<tau>"

| "inner_element_type \<tau> \<sigma> \<Longrightarrow>
   inner_element_type\<^sub>N (Required \<tau>) \<sigma>"
| "inner_element_type \<tau> \<sigma> \<Longrightarrow>
   inner_element_type\<^sub>N (Optional \<tau>) \<sigma>"

| "inner_element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   inner_element_type\<^sub>N\<^sub>E (ErrorFree \<tau>) \<sigma>"
| "inner_element_type\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   inner_element_type\<^sub>N\<^sub>E (Errorable \<tau>) \<sigma>"
*)
(*
lemma element_type\<^sub>N\<^sub>E_alt_simps:
  "element_type\<^sub>N\<^sub>E \<tau> \<sigma> = 
     (Collection \<sigma> = \<tau> \<or>
      Set \<sigma> = \<tau> \<or>
      OrderedSet \<sigma> = \<tau> \<or>
      Bag \<sigma> = \<tau> \<or>
      Sequence \<sigma> = \<tau>)"
  by (auto simp add: element_type.simps)
*)
inductive update_element_type
      and update_element_type\<^sub>N
      and update_element_type\<^sub>N\<^sub>E where
  "update_element_type (Collection _) \<tau> (Collection \<tau>)"
| "update_element_type (Set _) \<tau> (Set \<tau>)"
| "update_element_type (OrderedSet _) \<tau> (OrderedSet \<tau>)"
| "update_element_type (Bag _) \<tau> (Bag \<tau>)"
| "update_element_type (Sequence _) \<tau> (Sequence \<tau>)"

| "update_element_type \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type\<^sub>N (Required \<tau>) \<sigma> (Required \<rho>)"
| "update_element_type \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type\<^sub>N (Optional \<tau>) \<sigma> (Optional \<rho>)"

| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type\<^sub>N\<^sub>E (ErrorFree \<tau>) \<sigma> (ErrorFree \<rho>)"
| "update_element_type\<^sub>N \<tau> \<sigma> \<rho> \<Longrightarrow>
   update_element_type\<^sub>N\<^sub>E (Errorable \<tau>) \<sigma> (Errorable \<rho>)"

code_pred [show_modes] update_element_type\<^sub>N\<^sub>E .

values "{x. update_element_type\<^sub>N\<^sub>E (Set Integer[1])[?!] (Boolean[?] :: nat type\<^sub>N\<^sub>E) x}"
values "{x. update_element_type\<^sub>N\<^sub>E (Sequence (Set Integer[1])[?!])[1] (Boolean[?] :: nat type\<^sub>N\<^sub>E) x}"

inductive to_unique_collection
      and to_unique_collection\<^sub>N
      and to_unique_collection\<^sub>N\<^sub>E where
  "to_unique_collection (Collection \<tau>) (Set \<tau>)"
| "to_unique_collection (Set \<tau>) (Set \<tau>)"
| "to_unique_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection (Bag \<tau>) (Set \<tau>)"
| "to_unique_collection (Sequence \<tau>) (OrderedSet \<tau>)"

| "to_unique_collection \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "to_unique_collection \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

| "to_unique_collection\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection\<^sub>N\<^sub>E (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_unique_collection\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_unique_collection\<^sub>N\<^sub>E (Errorable \<tau>) (Errorable \<sigma>)"

inductive to_nonunique_collection
      and to_nonunique_collection\<^sub>N
      and to_nonunique_collection\<^sub>N\<^sub>E where
  "to_nonunique_collection (Collection \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Set \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (OrderedSet \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection (Bag \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Sequence \<tau>) (Sequence \<tau>)"

| "to_nonunique_collection \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "to_nonunique_collection \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

| "to_nonunique_collection\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection\<^sub>N\<^sub>E (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_nonunique_collection\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_nonunique_collection\<^sub>N\<^sub>E (Errorable \<tau>) (Errorable \<sigma>)"

inductive to_ordered_collection
      and to_ordered_collection\<^sub>N
      and to_ordered_collection\<^sub>N\<^sub>E where
  "to_ordered_collection (Collection \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Set \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (Bag \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Sequence \<tau>) (Sequence \<tau>)"

| "to_ordered_collection \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection\<^sub>N (Required \<tau>) (Required \<sigma>)"
| "to_ordered_collection \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection\<^sub>N (Optional \<tau>) (Optional \<sigma>)"

| "to_ordered_collection\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection\<^sub>N\<^sub>E (ErrorFree \<tau>) (ErrorFree \<sigma>)"
| "to_ordered_collection\<^sub>N \<tau> \<sigma> \<Longrightarrow>
   to_ordered_collection\<^sub>N\<^sub>E (Errorable \<tau>) (Errorable \<sigma>)"

inductive tuple_element\<^sub>N\<^sub>E where
  "fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   tuple_element\<^sub>N\<^sub>E (Tuple \<pi>)[1] elem \<tau>"
| "fmlookup \<pi> elem = Some \<tau> \<Longrightarrow>
   tuple_element\<^sub>N\<^sub>E (Tuple \<pi>)[1!] elem \<tau>"

(*
inductive update_element_type where
  "update_element_type (Collection _) \<tau> (Collection \<tau>)"
| "update_element_type (Set _) \<tau> (Set \<tau>)"
| "update_element_type (OrderedSet _) \<tau> (OrderedSet \<tau>)"
| "update_element_type (Bag _) \<tau> (Bag \<tau>)"
| "update_element_type (Sequence _) \<tau> (Sequence \<tau>)"

inductive to_unique_collection where
  "to_unique_collection (Collection \<tau>) (Set \<tau>)"
| "to_unique_collection (Set \<tau>) (Set \<tau>)"
| "to_unique_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_unique_collection (Bag \<tau>) (Set \<tau>)"
| "to_unique_collection (Sequence \<tau>) (OrderedSet \<tau>)"

inductive to_nonunique_collection where
  "to_nonunique_collection (Collection \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Set \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (OrderedSet \<tau>) (Sequence \<tau>)"
| "to_nonunique_collection (Bag \<tau>) (Bag \<tau>)"
| "to_nonunique_collection (Sequence \<tau>) (Sequence \<tau>)"

inductive to_ordered_collection where
  "to_ordered_collection (Collection \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Set \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (OrderedSet \<tau>) (OrderedSet \<tau>)"
| "to_ordered_collection (Bag \<tau>) (Sequence \<tau>)"
| "to_ordered_collection (Sequence \<tau>) (Sequence \<tau>)"
*)
(*
inductive update_element_type where
  "update_element_type (Collection\<^sub>N\<^sub>E _ opt err) \<tau> (Collection\<^sub>N\<^sub>E \<tau> opt err)"
| "update_element_type (Set\<^sub>N\<^sub>E _ opt err) \<tau> (Set\<^sub>N\<^sub>E \<tau> opt err)"
| "update_element_type (OrderedSet\<^sub>N\<^sub>E _ opt err) \<tau> (OrderedSet\<^sub>N\<^sub>E \<tau> opt err)"
| "update_element_type (Bag\<^sub>N\<^sub>E _ opt err) \<tau> (Bag\<^sub>N\<^sub>E \<tau> opt err)"
| "update_element_type (Sequence\<^sub>N\<^sub>E _ opt err) \<tau> (Sequence\<^sub>N\<^sub>E \<tau> opt err)"

inductive to_unique_collection where
  "to_unique_collection (Collection\<^sub>N\<^sub>E \<tau> opt err) (Set\<^sub>N\<^sub>E \<tau> opt err)"
| "to_unique_collection (Set\<^sub>N\<^sub>E \<tau> opt err) (Set\<^sub>N\<^sub>E \<tau> opt err)"
| "to_unique_collection (OrderedSet\<^sub>N\<^sub>E \<tau> opt err) (OrderedSet\<^sub>N\<^sub>E \<tau> opt err)"
| "to_unique_collection (Bag\<^sub>N\<^sub>E \<tau> opt err) (Set\<^sub>N\<^sub>E \<tau> opt err)"
| "to_unique_collection (Sequence\<^sub>N\<^sub>E \<tau> opt err) (OrderedSet\<^sub>N\<^sub>E \<tau> opt err)"

inductive to_nonunique_collection where
  "to_nonunique_collection (Collection\<^sub>N\<^sub>E \<tau> opt err) (Bag\<^sub>N\<^sub>E \<tau> opt err)"
| "to_nonunique_collection (Set\<^sub>N\<^sub>E \<tau> opt err) (Bag\<^sub>N\<^sub>E \<tau> opt err)"
| "to_nonunique_collection (OrderedSet\<^sub>N\<^sub>E \<tau> opt err) (Sequence\<^sub>N\<^sub>E \<tau> opt err)"
| "to_nonunique_collection (Bag\<^sub>N\<^sub>E \<tau> opt err) (Bag\<^sub>N\<^sub>E \<tau> opt err)"
| "to_nonunique_collection (Sequence\<^sub>N\<^sub>E \<tau> opt err) (Sequence\<^sub>N\<^sub>E \<tau> opt err)"

inductive to_ordered_collection where
  "to_ordered_collection (Collection\<^sub>N\<^sub>E \<tau> opt err) (Sequence\<^sub>N\<^sub>E \<tau> opt err)"
| "to_ordered_collection (Set\<^sub>N\<^sub>E \<tau> opt err) (OrderedSet\<^sub>N\<^sub>E \<tau> opt err)"
| "to_ordered_collection (OrderedSet\<^sub>N\<^sub>E \<tau> opt err) (OrderedSet\<^sub>N\<^sub>E \<tau> opt err)"
| "to_ordered_collection (Bag\<^sub>N\<^sub>E \<tau> opt err) (Sequence\<^sub>N\<^sub>E \<tau> opt err)"
| "to_ordered_collection (Sequence\<^sub>N\<^sub>E \<tau> opt err) (Sequence\<^sub>N\<^sub>E \<tau> opt err)"
*)

(*
fun to_single_type where
  "to_single_type OclSuper = OclSuper"
| "to_single_type \<tau>[1] = \<tau>[1]"
| "to_single_type \<tau>[?] = \<tau>[?]"
| "to_single_type (Collection \<tau>) = to_single_type \<tau>"
| "to_single_type (Set \<tau>) = to_single_type \<tau>"
| "to_single_type (OrderedSet \<tau>) = to_single_type \<tau>"
| "to_single_type (Bag \<tau>) = to_single_type \<tau>"
| "to_single_type (Sequence \<tau>) = to_single_type \<tau>"
| "to_single_type (Tuple \<pi>) = Tuple \<pi>"

fun to_required_type where
  "to_required_type \<tau>[1] = \<tau>[1]"
| "to_required_type \<tau>[?] = \<tau>[1]"
| "to_required_type \<tau> = \<tau>"

fun to_optional_type_nested where
  "to_optional_type_nested OclSuper = OclSuper"
| "to_optional_type_nested \<tau>[1] = \<tau>[?]"
| "to_optional_type_nested \<tau>[?] = \<tau>[?]"
| "to_optional_type_nested (Collection \<tau>) = Collection (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Set \<tau>) = Set (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (OrderedSet \<tau>) = OrderedSet (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Bag \<tau>) = Bag (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Sequence \<tau>) = Sequence (to_optional_type_nested \<tau>)"
| "to_optional_type_nested (Tuple \<pi>) = Tuple (fmmap to_optional_type_nested \<pi>)"
*)
(*
fun to_single_type
and to_single_type\<^sub>N
and to_single_type\<^sub>N\<^sub>E where
  "to_single_type OclAny = OclAny"
| "to_single_type OclVoid = OclVoid"

| "to_single_type Boolean = Boolean"
| "to_single_type Real = Real"
| "to_single_type Integer = Integer"
| "to_single_type UnlimitedNatural = UnlimitedNatural"
| "to_single_type String = String"

| "to_single_type (ObjectType \<C>) = ObjectType \<C>"
| "to_single_type (Enum \<E>) = Enum \<E>"

| "to_single_type (Collection \<tau>) = to_single_type\<^sub>N\<^sub>E \<tau>"
| "to_single_type (Set \<tau>) = to_single_type\<^sub>N\<^sub>E \<tau>"
| "to_single_type (OrderedSet \<tau>) = to_single_type\<^sub>N\<^sub>E \<tau>"
| "to_single_type (Bag \<tau>) = to_single_type\<^sub>N\<^sub>E \<tau>"
| "to_single_type (Sequence \<tau>) = to_single_type\<^sub>N\<^sub>E \<tau>"

| "to_single_type (Tuple \<pi>) = Tuple \<pi>"

| "to_single_type\<^sub>N (Required \<tau>) = to_single_type \<tau>"
| "to_single_type\<^sub>N (Optional \<tau>) = to_single_type \<tau>"

| "to_single_type\<^sub>N\<^sub>E (ErrorFree \<tau>) = to_single_type\<^sub>N \<tau>"
| "to_single_type\<^sub>N\<^sub>E (Errorable \<tau>) = to_single_type\<^sub>N \<tau>"

value "to_single_type\<^sub>N\<^sub>E (Set (Integer[1] :: nat type\<^sub>N\<^sub>E))[?!]"
value "to_single_type\<^sub>N\<^sub>E (Sequence (Set (Integer[1] :: nat type\<^sub>N\<^sub>E))[?!])[1]"
*)


fun to_required_type\<^sub>N
and to_required_type\<^sub>N\<^sub>E where
  "to_required_type\<^sub>N (Required \<tau>) = Required \<tau>"
| "to_required_type\<^sub>N (Optional \<tau>) = Required \<tau>"

| "to_required_type\<^sub>N\<^sub>E (ErrorFree \<tau>) = ErrorFree (to_required_type\<^sub>N \<tau>)"
| "to_required_type\<^sub>N\<^sub>E (Errorable \<tau>) = Errorable (to_required_type\<^sub>N \<tau>)"

fun to_optional_type_nested
and to_optional_type_nested\<^sub>N
and to_optional_type_nested\<^sub>N\<^sub>E where
  "to_optional_type_nested OclAny = OclAny"
| "to_optional_type_nested OclVoid = OclVoid"

| "to_optional_type_nested Boolean = Boolean"
| "to_optional_type_nested Real = Real"
| "to_optional_type_nested Integer = Integer"
| "to_optional_type_nested UnlimitedNatural = UnlimitedNatural"
| "to_optional_type_nested String = String"

| "to_optional_type_nested (ObjectType \<C>) = ObjectType \<C>"
| "to_optional_type_nested (Enum \<E>) = Enum \<E>"

| "to_optional_type_nested (Collection \<tau>) = Collection (to_optional_type_nested\<^sub>N\<^sub>E \<tau>)"
| "to_optional_type_nested (Set \<tau>) = Set (to_optional_type_nested\<^sub>N\<^sub>E \<tau>)"
| "to_optional_type_nested (OrderedSet \<tau>) = OrderedSet (to_optional_type_nested\<^sub>N\<^sub>E \<tau>)"
| "to_optional_type_nested (Bag \<tau>) = Bag (to_optional_type_nested\<^sub>N\<^sub>E \<tau>)"
| "to_optional_type_nested (Sequence \<tau>) = Sequence (to_optional_type_nested\<^sub>N\<^sub>E \<tau>)"

| "to_optional_type_nested (Tuple \<pi>) = Tuple (fmmap to_optional_type_nested\<^sub>N\<^sub>E \<pi>)"

| "to_optional_type_nested\<^sub>N (Required \<tau>) = Optional (to_optional_type_nested \<tau>)"
| "to_optional_type_nested\<^sub>N (Optional \<tau>) = Optional (to_optional_type_nested \<tau>)"

| "to_optional_type_nested\<^sub>N\<^sub>E (ErrorFree \<tau>) = ErrorFree (to_optional_type_nested\<^sub>N \<tau>)"
| "to_optional_type_nested\<^sub>N\<^sub>E (Errorable \<tau>) = Errorable (to_optional_type_nested\<^sub>N \<tau>)"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

(*
lemma element_type_det:
  "element_type \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   element_type \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: element_type.induct; simp add: element_type.simps)

lemma update_element_type_det:
  "update_element_type \<tau> \<sigma> \<rho>\<^sub>1 \<Longrightarrow>
   update_element_type \<tau> \<sigma> \<rho>\<^sub>2 \<Longrightarrow> \<rho>\<^sub>1 = \<rho>\<^sub>2"
  by (induct rule: update_element_type.induct; simp add: update_element_type.simps)

lemma to_unique_collection_det:
  "to_unique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_unique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_unique_collection.induct; simp add: to_unique_collection.simps)

lemma to_nonunique_collection_det:
  "to_nonunique_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_nonunique_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_nonunique_collection.induct; simp add: to_nonunique_collection.simps)

lemma to_ordered_collection_det:
  "to_ordered_collection \<tau> \<sigma>\<^sub>1 \<Longrightarrow>
   to_ordered_collection \<tau> \<sigma>\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2"
  by (induct rule: to_ordered_collection.induct; simp add: to_ordered_collection.simps)
*)

lemma
  element_type_det:
    "element_type \<tau> \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
     element_type \<tau> \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E" and
  element_type\<^sub>N_det:
    "element_type\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
     element_type\<^sub>N \<tau>\<^sub>N \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E" and
  element_type\<^sub>N\<^sub>E_det:
    "element_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
     element_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E"
  by (induct arbitrary: \<rho>\<^sub>N\<^sub>E rule: element_type_element_type\<^sub>N_element_type\<^sub>N\<^sub>E.inducts,
      simp_all add: element_type.simps element_type\<^sub>N.simps element_type\<^sub>N\<^sub>E.simps)

lemma to_single_type\<^sub>N\<^sub>E_det:
  "to_single_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
   to_single_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E"
  apply (induct arbitrary: \<rho>\<^sub>N\<^sub>E rule: to_single_type\<^sub>N\<^sub>E.induct)
  using is_collection\<^sub>N\<^sub>E.intros to_single_type\<^sub>N\<^sub>E.cases apply blast
  by (metis element_type\<^sub>N\<^sub>E_det is_collection\<^sub>N\<^sub>E.intros to_single_type\<^sub>N\<^sub>E.cases)

lemma inner_element_type\<^sub>N\<^sub>E_det:
  "inner_element_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
   inner_element_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E"
  apply (induct arbitrary: \<rho>\<^sub>N\<^sub>E rule: inner_element_type\<^sub>N\<^sub>E.induct)
  by (meson inner_element_type\<^sub>N\<^sub>E.cases to_single_type\<^sub>N\<^sub>E.intros(2) to_single_type\<^sub>N\<^sub>E_det)

lemma
  update_element_type_det:
    "update_element_type \<tau> \<sigma>\<^sub>N\<^sub>E \<rho> \<Longrightarrow>
     update_element_type \<tau> \<sigma>\<^sub>N\<^sub>E \<upsilon> \<Longrightarrow> \<rho> = \<upsilon>" and
  update_element_type\<^sub>N_det:
    "update_element_type\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N\<^sub>E \<rho>\<^sub>N \<Longrightarrow>
     update_element_type\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N\<^sub>E \<upsilon>\<^sub>N \<Longrightarrow> \<rho>\<^sub>N = \<upsilon>\<^sub>N" and
  update_element_type\<^sub>N\<^sub>E_det:
    "update_element_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow>
     update_element_type\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<upsilon>\<^sub>N\<^sub>E \<Longrightarrow> \<rho>\<^sub>N\<^sub>E = \<upsilon>\<^sub>N\<^sub>E"
  for \<tau> :: "'a type" and \<rho> \<upsilon> :: "'b type"
  and \<tau>\<^sub>N :: "'a type\<^sub>N" and \<rho>\<^sub>N \<upsilon>\<^sub>N :: "'b type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E" and \<sigma>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<upsilon>\<^sub>N\<^sub>E :: "'b type\<^sub>N\<^sub>E"
  by (induct rule: update_element_type_update_element_type\<^sub>N_update_element_type\<^sub>N\<^sub>E.inducts,
      auto simp: update_element_type.simps update_element_type\<^sub>N.simps update_element_type\<^sub>N\<^sub>E.simps)

lemma
  to_unique_collection_det:
    "to_unique_collection \<tau> \<sigma> \<Longrightarrow>
     to_unique_collection \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>" and
  to_unique_collection\<^sub>N_det:
    "to_unique_collection\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N \<Longrightarrow>
     to_unique_collection\<^sub>N \<tau>\<^sub>N \<rho>\<^sub>N \<Longrightarrow> \<sigma>\<^sub>N = \<rho>\<^sub>N" and
  to_unique_collection\<^sub>N\<^sub>E_det:
    "to_unique_collection\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
     to_unique_collection\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  by (induct rule: to_unique_collection_to_unique_collection\<^sub>N_to_unique_collection\<^sub>N\<^sub>E.inducts,
      auto simp: to_unique_collection.simps to_unique_collection\<^sub>N.simps to_unique_collection\<^sub>N\<^sub>E.simps)

lemma
  to_nonunique_collection_det:
    "to_nonunique_collection \<tau> \<sigma> \<Longrightarrow>
     to_nonunique_collection \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>" and
  to_nonunique_collection\<^sub>N_det:
    "to_nonunique_collection\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N \<Longrightarrow>
     to_nonunique_collection\<^sub>N \<tau>\<^sub>N \<rho>\<^sub>N \<Longrightarrow> \<sigma>\<^sub>N = \<rho>\<^sub>N" and
  to_nonunique_collection\<^sub>N\<^sub>E_det:
    "to_nonunique_collection\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
     to_nonunique_collection\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  by (induct rule: to_nonunique_collection_to_nonunique_collection\<^sub>N_to_nonunique_collection\<^sub>N\<^sub>E.inducts,
      auto simp: to_nonunique_collection.simps to_nonunique_collection\<^sub>N.simps to_nonunique_collection\<^sub>N\<^sub>E.simps)

lemma
  to_ordered_collection_det:
    "to_ordered_collection \<tau> \<sigma> \<Longrightarrow>
     to_ordered_collection \<tau> \<rho> \<Longrightarrow> \<sigma> = \<rho>" and
  to_ordered_collection\<^sub>N_det:
    "to_ordered_collection\<^sub>N \<tau>\<^sub>N \<sigma>\<^sub>N \<Longrightarrow>
     to_ordered_collection\<^sub>N \<tau>\<^sub>N \<rho>\<^sub>N \<Longrightarrow> \<sigma>\<^sub>N = \<rho>\<^sub>N" and
  to_ordered_collection\<^sub>N\<^sub>E_det:
    "to_ordered_collection\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow>
     to_ordered_collection\<^sub>N\<^sub>E \<tau>\<^sub>N\<^sub>E \<rho>\<^sub>N\<^sub>E \<Longrightarrow> \<sigma>\<^sub>N\<^sub>E = \<rho>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  by (induct rule: to_ordered_collection_to_ordered_collection\<^sub>N_to_ordered_collection\<^sub>N\<^sub>E.inducts,
      auto simp: to_ordered_collection.simps to_ordered_collection\<^sub>N.simps to_ordered_collection\<^sub>N\<^sub>E.simps)

lemma tuple_element\<^sub>N\<^sub>E_det:
  "tuple_element\<^sub>N\<^sub>E \<tau> elem \<sigma> \<Longrightarrow>
   tuple_element\<^sub>N\<^sub>E \<tau> elem \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  by (induct rule: tuple_element\<^sub>N\<^sub>E.induct; erule tuple_element\<^sub>N\<^sub>E.cases; auto)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred subtype .

lemma Tuple_measure_intro [intro]:
  assumes "fmlookup \<xi> k = Some \<sigma>"
    shows "(Inr (Inr (\<tau>, \<sigma>)), Inl (Tuple \<pi>, Tuple \<xi>)) \<in>
   case_sum (type_size \<circ> snd)
    (case_sum (type_size\<^sub>N \<circ> snd) (type_size\<^sub>N\<^sub>E \<circ> snd)) <*mlex*> {}"
proof -
  have "fmlookup \<xi> k = Some \<sigma> \<Longrightarrow> type_size\<^sub>N\<^sub>E \<sigma> < type_size (Tuple \<xi>)"
    by (simp add: elem_le_ffold' fmran'I)
  with assms show ?thesis
    unfolding mlex_prod_def less_eq by simp
qed

function subtype_fun :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool"
     and subtype\<^sub>N_fun :: "'a type\<^sub>N \<Rightarrow> 'a type\<^sub>N \<Rightarrow> bool"
     and subtype\<^sub>N\<^sub>E_fun :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> bool" where

  "subtype_fun OclAny _ = False"
| "subtype_fun OclVoid \<sigma> = (\<sigma> \<noteq> OclVoid)"

| "subtype_fun Boolean \<sigma> = (\<sigma> = OclAny)"
| "subtype_fun Real \<sigma> = (\<sigma> = OclAny)"
| "subtype_fun Integer \<sigma> = (\<sigma> = Real \<or> \<sigma> = OclAny)"
| "subtype_fun UnlimitedNatural \<sigma> = (\<sigma> = Integer \<or> \<sigma> = Real \<or> \<sigma> = OclAny)"
| "subtype_fun String \<sigma> = (\<sigma> = OclAny)"

| "subtype_fun \<langle>\<C>\<rangle>\<^sub>\<T> \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | \<langle>\<D>\<rangle>\<^sub>\<T> \<Rightarrow> \<C> < \<D>
     | _ \<Rightarrow> False)"
| "subtype_fun (Enum _) \<sigma> = (\<sigma> = OclAny)"

| "subtype_fun (Collection \<tau>) \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Set \<tau>) \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Set \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (OrderedSet \<tau>) \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | OrderedSet \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Bag \<tau>) \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Bag \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"
| "subtype_fun (Sequence \<tau>) \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | Collection \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho> \<or> \<tau> = \<rho>
     | Sequence \<rho> \<Rightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<rho>
     | _ \<Rightarrow> False)"

| "subtype_fun (Tuple \<pi>) \<sigma> = (case \<sigma>
    of OclAny \<Rightarrow> True
     | Tuple \<xi> \<Rightarrow> strict_subtuple_fun (\<lambda>\<tau> \<sigma>. subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>
     | _ \<Rightarrow> False)"

| "subtype\<^sub>N_fun (Required \<tau>) \<sigma> = (case \<sigma>
    of Required \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>
     | Optional \<rho> \<Rightarrow> subtype_fun \<tau> \<rho> \<or> \<tau> = \<rho>)"
| "subtype\<^sub>N_fun (Optional \<tau>) \<sigma>\<^sub>N = (case \<sigma>\<^sub>N
    of Required \<rho> \<Rightarrow> False
     | Optional \<rho> \<Rightarrow> subtype_fun \<tau> \<rho>)"

| "subtype\<^sub>N\<^sub>E_fun (ErrorFree \<tau>) \<sigma> = (case \<sigma>
    of ErrorFree \<rho> \<Rightarrow> subtype\<^sub>N_fun \<tau> \<rho>
     | Errorable \<rho> \<Rightarrow> subtype\<^sub>N_fun \<tau> \<rho> \<or> \<tau> = \<rho>)"
| "subtype\<^sub>N\<^sub>E_fun (Errorable \<tau>) \<sigma>\<^sub>N = (case \<sigma>\<^sub>N
    of ErrorFree \<rho> \<Rightarrow> False
     | Errorable \<rho> \<Rightarrow> subtype\<^sub>N_fun \<tau> \<rho>)"
  by pat_completeness auto
termination
  apply (relation "case_sum (size \<circ> snd) (case_sum (size \<circ> snd) (size \<circ> snd)) <*mlex*> {}")
  by (auto simp add: wf_mlex mlex_less)

lemma subtuple_subtype\<^sub>N\<^sub>E_fun_intro [simp]:
  assumes "(\<And>\<tau> \<sigma>\<^sub>N\<^sub>E. \<tau> \<in> fmran' \<pi> \<Longrightarrow> \<tau> < \<sigma>\<^sub>N\<^sub>E \<Longrightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma>\<^sub>N\<^sub>E)"
      and "subtuple (\<le>) \<pi> \<xi>"
    shows "subtuple (\<lambda>\<tau> \<sigma>. subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>"
proof -
  have "subtuple (\<le>) \<pi> \<xi> \<longrightarrow> subtuple (\<lambda>\<tau> \<sigma>. subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>"
    apply (rule subtuple_mono)
    using assms(1) by auto
  with assms(2) show ?thesis by simp
qed

lemma subtuple_subtype\<^sub>N\<^sub>E_fun_drule [simp]:
  assumes "(\<And>\<tau> \<sigma>\<^sub>N\<^sub>E. \<tau> \<in> fmran' \<pi> \<Longrightarrow> subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma>\<^sub>N\<^sub>E \<Longrightarrow> \<tau> < \<sigma>\<^sub>N\<^sub>E)"
      and "subtuple (\<lambda>\<tau> \<sigma>. subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi>"
    shows "subtuple (\<le>) \<pi> \<xi>"
proof -
  have "subtuple (\<lambda>\<tau> \<sigma>. subtype\<^sub>N\<^sub>E_fun \<tau> \<sigma> \<or> \<tau> = \<sigma>) \<pi> \<xi> \<longrightarrow> subtuple (\<le>) \<pi> \<xi>"
    apply (rule subtuple_mono)
    by (simp add: assms(1) order.strict_implies_order)
  with assms(2) show ?thesis by simp
qed

lemma subtype_fun_intro:
  "\<tau> < \<sigma> \<Longrightarrow> subtype_fun \<tau> \<sigma>"
  "\<tau>\<^sub>N < \<sigma>\<^sub>N \<Longrightarrow> subtype\<^sub>N_fun \<tau>\<^sub>N \<sigma>\<^sub>N"
  "\<tau>\<^sub>N\<^sub>E < \<sigma>\<^sub>N\<^sub>E \<Longrightarrow> subtype\<^sub>N\<^sub>E_fun \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a::order type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
  by (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E arbitrary: \<sigma> and \<sigma>\<^sub>N and \<sigma>\<^sub>N\<^sub>E, auto)

lemma subtype_fun_drule:
  "subtype_fun \<tau> \<sigma> \<Longrightarrow> \<tau> < \<sigma>"
  "subtype\<^sub>N_fun \<tau>\<^sub>N \<sigma>\<^sub>N \<Longrightarrow> \<tau>\<^sub>N < \<sigma>\<^sub>N"
  "subtype\<^sub>N\<^sub>E_fun \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E \<Longrightarrow> \<tau>\<^sub>N\<^sub>E < \<sigma>\<^sub>N\<^sub>E"
  for \<tau> \<sigma> :: "'a::order type"
  and \<tau>\<^sub>N \<sigma>\<^sub>N :: "'a type\<^sub>N"
  and \<tau>\<^sub>N\<^sub>E \<sigma>\<^sub>N\<^sub>E :: "'a type\<^sub>N\<^sub>E"
proof (induct \<tau> and \<tau>\<^sub>N and \<tau>\<^sub>N\<^sub>E arbitrary: \<sigma> and \<sigma>\<^sub>N and \<sigma>\<^sub>N\<^sub>E)
  case OclAny thus ?case by auto
next
  case OclVoid thus ?case by auto
next
  case Boolean thus ?case by auto
next
  case Real thus ?case by auto
next
  case Integer thus ?case by auto
next
  case UnlimitedNatural thus ?case by auto
next
  case String thus ?case by auto
next
  case (ObjectType \<C>) thus ?case by (cases \<sigma>; auto)
next
  case (Enum \<E>) thus ?case by auto
next
  case (Collection \<tau>) thus ?case by (cases \<sigma>; auto)
next
  case (Set \<tau>) thus ?case by (cases \<sigma>; auto simp: less_imp_le)
next
  case (OrderedSet \<tau>) thus ?case by (cases \<sigma>; auto simp: less_imp_le)
next
  case (Bag \<tau>) thus ?case by (cases \<sigma>; auto simp: less_imp_le)
next
  case (Sequence \<tau>) thus ?case by (cases \<sigma>; auto simp: less_imp_le)
next
  case (Tuple \<pi>) thus ?case by (cases \<sigma>; auto)
next
  case (Required \<tau>) thus ?case by (cases \<sigma>\<^sub>N; auto simp: order.strict_implies_order)
next
  case (Optional \<tau>) thus ?case by (cases \<sigma>\<^sub>N; auto)
next
  case (ErrorFree \<tau>) thus ?case by (cases \<sigma>\<^sub>N\<^sub>E; auto simp: order.strict_implies_order)
next
  case (Errorable \<tau>) thus ?case by (cases \<sigma>\<^sub>N\<^sub>E; auto)
qed

lemma less_type_code [code]:
  "(<) = subtype_fun"
  "(<) = subtype\<^sub>N_fun"
  "(<) = subtype\<^sub>N\<^sub>E_fun"
  by (intro ext iffI; simp add: subtype_fun_intro subtype_fun_drule)+

lemma less_eq_type_code [code]:
  "(\<le>) = (\<lambda>x y. subtype_fun x y \<or> x = y)"
  unfolding dual_order.order_iff_strict less_type_code
  by auto

code_pred element_type .
code_pred update_element_type .
code_pred to_unique_collection .
code_pred to_nonunique_collection .
code_pred to_ordered_collection .

end

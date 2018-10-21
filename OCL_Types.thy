theory OCL_Types
  imports
    Main
    Transitive_Closure_Ext
    OCL_Basic_Types
    (*"~~/src/HOL/Library/Finite_Map"*)
begin

(*
  Тут много определений и теорем для систем типов:
  http://gallium.inria.fr/~remy/mpri/cours1.pdf
*)

(* В разделе 8.2 спецификации OCL:
   Note that in contrast with invalid, null is a valid value and as such can be owned by collections.
   Какой-то бред. Получается для коллекций нужно делать отдельные простые типы, не допускающие ошибки?
   Или достаточно сделать ещё правило валидации для коллекций дополнительно к проверке типа элементов?

   Кортежи нужны в основном для операций с out параметрами
*)

notation
  sup (infixl "\<squnion>" 65)

(*type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)*)

(*** Types ******************************************************************)

(* OclState не реализуем. В A.2.6 написано, что он похож на перечисление
   В спецификации кортежи определяются в одном разделе с коллекциями.
   Также они не могут быть опциональными. И ещё они OclAny не является их супертипом
   По-этому описываем их тут, а не в базовых типах

   MessageType и TemplateParameterType не реализуем

   Приложение A информативное, по-этому если там что-то неправильно,
   это видимо можно игнорировать, но отметить в статье
 *)

datatype 'a type =
  SupType
| OclInvalid
| OclVoid
| Required "'a basic_type" ("_[1]" [1000] 1000)
| Optional "'a basic_type" ("_[?]" [1000] 1000)
| Collection "'a type"
| Set "'a type"
| OrderedSet "'a type" (* Этого типа почему-то нет в A.2.5, но есть в 8.2 *)
| Bag "'a type"
| Sequence "'a type"
| Tuple "'a type list"
(*| Tuple "vname \<rightharpoonup>\<^sub>f type"*)

term "Set Real[?]"
term "Set Real[1]"

(* Иерархия типов описана в A.2.7 Type Hierarchy *)

datatype t = A | B | C "t list"
(*
definition "only_one p xs ys \<equiv>
  let xys = zip xs ys in
  length xs = length ys \<and>
  xs \<noteq> [] \<and>
  list_all2 (\<lambda>(x, y). x = y \<or> p x y) xys \<and>
  length xs =
    length (takeWhile (\<lambda>(x, y). x = y) xys) +
    length (takeWhile (\<lambda>(x, y). x = y) (rev xys)) + 1"

primrec find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option" where
"find _ [] = None" |
"find P (x#xs) = (if P x then Some x else find P xs)"
*)
(*
inductive only_one :: "bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "only_one True p [] []"
| "x = y \<Longrightarrow>
   only_one found p xs ys \<Longrightarrow>
   only_one found p (x#xs) (y#ys)"
| "p x y \<Longrightarrow>
   found = False \<Longrightarrow>
   only_one True p xs ys \<Longrightarrow>
   only_one found p (x#xs) (y#ys)"

code_pred [show_modes] only_one .
*)
(*
definition "only_one p xs ys \<equiv>
  let xys = zip xs ys in
  length xs = length ys \<and>
  xs \<noteq> [] \<and>
  list_all2 (\<lambda>x y. x = y \<or> p x y) xs ys \<and>
  length xs =
    length (takeWhile (\<lambda>(x, y). x = y) xys) +
    length (takeWhile (\<lambda>(x, y). x = y) (rev xys)) + 1"

lemma only_one_mono[mono]: "(\<And> x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> p x y \<longrightarrow> q x y) \<Longrightarrow>
  only_one p xs ys \<longrightarrow> only_one q xs ys"
  apply (auto simp add: only_one_def)
  by (metis (mono_tags, lifting) list.rel_mono_strong)

lemma q:
  "only_one p xs ys \<Longrightarrow> xs = xh@[x]@xt \<Longrightarrow> ys = xh@[y]@xt \<Longrightarrow> x \<noteq> y \<Longrightarrow> p x y"

inductive prec_t ("_ \<prec> _" [65, 65] 65) where
  "A \<prec> B"
| "C [B] \<prec> B"
| "C (xs@[B]) \<prec> C xs"
| "only_one (\<lambda>x y. x \<prec> y) xs ys \<Longrightarrow>
   C xs \<prec> C ys"

inductive prec_t ("_ \<prec> _" [65, 65] 65) where
  "A \<prec> B"
| "C [B] \<prec> B"
| "C (B#xs) \<prec> C xs"
| "list_all2 (\<lambda>x y. x = y \<or> x \<prec> y) xs ys \<Longrightarrow>
   length xs = length ys \<Longrightarrow>
   xs \<noteq> []  \<Longrightarrow>
   C xs \<prec> C ys"
*)
(*
primrec only_one' :: "bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "only_one' found p xs [] = (case xs of [] \<Rightarrow> found | _ \<Rightarrow> False)"
| "only_one' found p xs (y # ys) = (case xs of [] \<Rightarrow> False | z # zs \<Rightarrow>
    if z = y then only_one' found p zs ys else
    let found' = p z y in
    if found \<and> found' then False else only_one' found' p zs ys)"

abbreviation "only_one \<equiv> only_one' False"

datatype t = A | B | C "t list"

inductive prec_t ("_ \<prec> _" [65, 65] 65) where
  "A \<prec> B"
| "C [B] \<prec> B"
| "C (B#xs) \<prec> C xs"
| "only_one (\<lambda>x y. x \<prec> y) xs ys \<Longrightarrow>
   C xs \<prec> C ys"
*)
(*
definition "only_one p xs ys \<equiv>
  let xys = zip xs ys in
  length xs = length ys \<and>
  list_all (\<lambda>(x, y). x = y \<or> p x y) xys \<and>
  length xs =
    length (takeWhile (\<lambda>(x, y). x = y) xys) +
    length (takeWhile (\<lambda>(x, y). x = y) (rev xys)) + 1"

datatype t = A | B | C "t list"

lemma q:
  "mono only_one"
  apply (rule monoI)
  apply (auto simp add: only_one_def)

lemma q11:
  "x \<le> y \<Longrightarrow>
   length xa = length ya \<Longrightarrow>
   list_all (\<lambda>(xa, y). xa = y \<or> x xa y) (zip xa ya) \<Longrightarrow>
   list_all (\<lambda>(x, ya). x = ya \<or> y x ya) (zip xa ya)"
  by (smt Ball_set case_prod_conv predicate2D split_cong)

lemma q12:
  "x \<le> y \<Longrightarrow>
          length xa = length ya \<Longrightarrow>
          list_all (\<lambda>(xa, y). xa = y \<or> x xa y) (zip xa ya) \<Longrightarrow>
          length xa =
          Suc (length (takeWhile (\<lambda>(x, y). x = y) (zip xa ya)) +
               length
                (takeWhile (\<lambda>(x, y). x = y) (rev (zip xa ya)))) \<Longrightarrow>
          list_all (\<lambda>(x, ya). x = ya \<or> y x ya) (zip xa ya) \<and>
          length xa =
          Suc (length (takeWhile (\<lambda>(x, y). x = y) (zip xa ya)) +
               length
                (takeWhile (\<lambda>(x, y). x = y) (rev (zip xa ya))))"
  by (auto simp add: q11)

lemma q:
  "mono
 (\<lambda>p x1 x2.
     x1 = A \<and> x2 = B \<or>
     x1 = C [B] \<and> x2 = B \<or>
     (\<exists>xs. x1 = C (B # xs) \<and> x2 = C xs) \<or>
     (\<exists>xs ys. x1 = C xs \<and> x2 = C ys \<and> only_one p xs ys))"
  apply (rule monoI)
  apply (auto)
  apply (auto simp add: only_one_def)


inductive prec_t ("_ \<prec> _" [65, 65] 65) where
  "A \<prec> B"
| "C [B] \<prec> B"
| "C (B#xs) \<prec> C xs"
| "only_one (\<lambda>x y. x \<prec> y) xs ys \<Longrightarrow>
   C xs \<prec> C ys"

inductive prec_t ("_ \<prec> _" [65, 65] 65) where
  "A \<prec> B"
| "C [B] \<prec> B"
| "C (xs@[B]) \<prec> C xs"
| "only_one (\<lambda>x y. x \<prec> y) xs ys \<Longrightarrow>
   C xs \<prec> C ys"
*)
(*
definition "only_one p xs ys \<equiv>
  list_all2 (\<lambda>x y. x = y \<or> p x y) xs ys \<and>
  length (filter (\<lambda>(x, y). p x y) (zip xs ys)) = 1"
*)
(*
primrec only_one :: "bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "only_one found p xs [] = (case xs of [] \<Rightarrow> found | _ \<Rightarrow> False)"
| "only_one found p xs (y # ys) = (case xs of [] \<Rightarrow> False | z # zs \<Rightarrow>
    if z = y then only_one found p zs ys else
    let found' = p z y in
    if found \<and> found' then False else only_one found' p zs ys)"

value "only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2] [1::nat,2]"
value "only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2,3] [1::nat,2,3]"
value "only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2,3] [1::nat,2,4]"
value "only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2,3,5] [1::nat,2,4,5]"
value "only_one False (\<lambda>x y. x \<noteq> y) [1::nat,3] [2::nat,3]"
value "only_one False (\<lambda>x y. x \<noteq> y) [1::nat] [2::nat]"
*)
(*
inductive only_one :: "bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "only_one True p [] []"
| "x = y \<Longrightarrow>
   only_one found p xs ys \<Longrightarrow>
   only_one found p (x#xs) (y#ys)"
| "p x y \<Longrightarrow>
   found = False \<Longrightarrow>
   only_one True p xs ys \<Longrightarrow>
   only_one found p (x#xs) (y#ys)"

code_pred [show_modes] only_one .

values "{t. only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2] [1::nat,2]}"
values "{t. only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2,3] [1::nat,2,3]}"
values "{t. only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2,3] [1::nat,2,4]}"
values "{t. only_one False (\<lambda>x y. x \<noteq> y) [1::nat,2,3,5] [1::nat,2,4,5]}"
values "{t. only_one False (\<lambda>x y. x \<noteq> y) [1::nat,3] [2::nat,3]}"
values "{t. only_one False (\<lambda>x y. x \<noteq> y) [1::nat] [2::nat]}"
*)
(*
definition "only_one p xs ys \<equiv>
  length xs = length ys \<and>
  xs \<noteq> ys \<and>
  length xs > 0 \<and>
  list_all2 (\<lambda>x y. x = y \<or> p x y) xs ys"

lemma only_one_mono:
  "mono only_one"
*)
(*
primrec only_one' :: "bool \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "only_one' found p xs [] = (case xs of [] \<Rightarrow> found | _ \<Rightarrow> False)"
| "only_one' found p xs (y # ys) = (case xs of [] \<Rightarrow> False | z # zs \<Rightarrow>
    if z = y then only_one' found p zs ys else
    let found' = p z y in
    if found \<and> found' then False else only_one' found' p zs ys)"

abbreviation "only_one \<equiv> only_one' False"
*)
(*
lemma only_one_mono: "(\<And> x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> p x y \<longrightarrow> q x y) \<Longrightarrow>
  only_one p xs ys \<longrightarrow> only_one q xs ys"
*)

definition "only_one p xs ys \<equiv>
  \<exists>h t x y. xs = h@[x]@t \<and> ys = h@[y]@t \<and> x \<noteq> y \<and> p x y"

definition "only_one' p xs ys \<equiv>
  let h = map fst (takeWhile (\<lambda>(x, y). x = y) (zip xs ys)) in
  \<exists>x y t. xs = h@[x]@t \<and> ys = h@[y]@t \<and> x \<noteq> y \<and> p x y"

definition "only_one'' p xs ys \<equiv>
  length xs = length ys \<and>
  xs \<noteq> [] \<and>
  list_all2 (\<lambda>x y. x = y \<or> p x y) xs ys"

lemma only_one_simp'':
  "only_one p xs ys \<Longrightarrow> only_one'' p xs ys"
  unfolding only_one_def only_one''_def
  by (auto simp add: list.rel_refl list_all2_appendI)

(*
definition "only_one p xs ys \<equiv>
  \<exists>h t x y. xs = h@[x]@t \<and> ys = h@[y]@t \<and> (x = y \<or> p x y)"
*)
lemma takeWhile_zip_simp:
  "x \<noteq> y \<Longrightarrow> map fst (takeWhile (\<lambda>(x, y). x = y) (zip h h @ (x, y) # zip t t)) = h"
proof -
  assume a1: "x \<noteq> y"
  have f2: "\<forall>ps p psa. (\<exists>pa. (pa::'a \<times> 'a) \<in> set ps \<and> \<not> p pa) \<or> takeWhile p (ps @ psa) = ps @ takeWhile p psa"
    by (meson takeWhile_append2)
  have "\<forall>as asa. (as = asa) = (length as = length asa \<and> (\<forall>p. p \<notin> set (zip as asa) \<or> (case p of (a::'a, aa) \<Rightarrow> a = aa)))"
by (simp add: Ball_def_raw list_eq_iff_zip_eq)
then have "\<forall>p. p \<notin> set (zip h h) \<or> (case p of (a, aa) \<Rightarrow> a = aa)"
  by (metis (full_types))
  then have "takeWhile (\<lambda>(aa, a). aa = a) (zip h h @ []) = zip h h @ takeWhile (\<lambda>(aa, a). aa = a) []"
  using f2 by meson
then show ?thesis
using a1 by simp
qed
(*
lemma only_one_simp:
  "only_one p xs ys = only_one' p xs ys"
  unfolding only_one_def only_one'_def
  apply auto
  apply (simp add: takeWhile_zip_simp)
  by meson
*)
lemma only_one_mono [mono]: "(\<And> x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> p x y \<longrightarrow> q x y) \<Longrightarrow>
  only_one p xs ys \<longrightarrow> only_one q xs ys"
  by (smt UnCI list.set_intros(1) only_one_def set_append)


inductive direct_subtype :: "'a::order type \<Rightarrow> 'a type \<Rightarrow> bool" ("_ \<sqsubset> _" [65, 65] 65) where
  "OclInvalid \<sqsubset> OclVoid"
| "(*is_min_basic_type \<sigma> \<Longrightarrow>*) OclInvalid \<sqsubset> Required \<sigma>"
| "(*is_min_basic_type \<sigma> \<Longrightarrow>*) OclVoid \<sqsubset> Optional \<sigma>"
| "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow> Required \<tau> \<sqsubset> Required \<sigma>"
| "\<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow> Optional \<tau> \<sqsubset> Optional \<sigma>"
| "Required \<tau> \<sqsubset> Optional \<tau>"
| "OclInvalid \<sqsubset> Set OclInvalid"
| "OclInvalid \<sqsubset> OrderedSet OclInvalid"
| "OclInvalid \<sqsubset> Bag OclInvalid"
| "OclInvalid \<sqsubset> Sequence OclInvalid"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Set \<tau> \<sqsubset> Set \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> OrderedSet \<tau> \<sqsubset> OrderedSet \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Bag \<tau> \<sqsubset> Bag \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Sequence \<tau> \<sqsubset> Sequence \<sigma>"
| "\<tau> \<sqsubset> \<sigma> \<Longrightarrow> Collection \<tau> \<sqsubset> Collection \<sigma>"
| "Set \<tau> \<sqsubset> Collection \<tau>"
| "OrderedSet \<tau> \<sqsubset> Collection \<tau>"
| "Bag \<tau> \<sqsubset> Collection \<tau>"
| "Sequence \<tau> \<sqsubset> Collection \<tau>"
| "Optional OclAny \<sqsubset> SupType"
| "Collection SupType \<sqsubset> SupType"
| "Tuple [SupType] \<sqsubset> SupType"
| "Tuple (\<pi>@[SupType]) \<sqsubset> Tuple \<pi>"
(*| "\<pi> = xh@[x]@xt \<Longrightarrow>
   \<xi> = xh@[y]@xt \<Longrightarrow>
   x \<sqsubset> y \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>" (* TODO: Check that only one type is changed *)*)
| "only_one (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>" (* TODO: Check that only one type is changed *)
(*| "length \<pi> = length \<xi> \<Longrightarrow>
   \<pi> \<noteq> \<xi> \<Longrightarrow>
   length \<pi> > 0 \<Longrightarrow>
   list_all2 (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>" (* Попробовать встроить only_one сюда *)*)
| "OclInvalid \<sqsubset> Tuple \<pi>" (* HACK *)
| "Tuple \<pi> \<sqsubset> SupType" (* HACK *)
(*| "only_one False (\<lambda>\<tau> \<sigma>. \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"*)
(*| "list_all2 (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma>) \<pi> \<xi> \<Longrightarrow>
   length (filter (\<lambda>(\<tau>, \<sigma>). \<tau> \<sqsubset> \<sigma>) (zip \<pi> \<xi>)) = 1 \<Longrightarrow>
   Tuple \<pi> \<sqsubset> Tuple \<xi>"*)
(*| "fmran \<pi> = {|SupType|} \<Longrightarrow>
   Tuple \<pi> \<sqsubset> SupType"
| "Tuple (fmupd x SupType \<pi>) \<sqsubset> Tuple \<pi>"*)
(*| "Tuple (fmupd x SupType fmempty) \<sqsubset> SupType"
| "Tuple (fmupd x SupType \<pi>) \<sqsubset> Tuple \<pi>"*)
(*| "Tuple (fmap_of_list [(x, SupType)]) \<sqsubset> SupType"*)

(* OclVoid не может быть подтипом для Tuple при используемом подходе,
   потому что у кортежей при спуске по иерархии типов элементов становится всё больше.
   Это интересная проблема, нужно обязательно написать о ней в статье
   А, вот, SupType - это как раз наоборот не проблема и он нужен для полиморфизма

   Множественное наследование сейчас есть и без кортережей: void, optional, collection
   Кортежи в этом отношении ничего не усложняют
   Сложность только в том, что у кортежа несколько параметров
   И эта множественность должна учитываться в одном правиле, а не разных как для других типов

   Для простоты вместо fmap можно использовать список
   По сути просто заменяем имена свойств натуральными числами
 *)

code_pred [show_modes] direct_subtype .

inductive_cases direct_subtype_x_OclInvalid[elim]: "\<tau> \<sqsubset> OclInvalid"
inductive_cases direct_subtype_OclInvalid_x[elim]: "OclInvalid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_OclVoid[elim]: "\<tau> \<sqsubset> OclVoid"
inductive_cases direct_subtype_OclVoid_x[elim]: "OclVoid \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Required[elim]: "\<tau> \<sqsubset> \<sigma>[1]"
inductive_cases direct_subtype_Required_x[elim]: "\<tau>[1] \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Optional[elim]: "\<tau> \<sqsubset> \<sigma>[?]"
inductive_cases direct_subtype_Optional_x[elim]: "\<tau>[?] \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Collection[elim]: "\<tau> \<sqsubset> Collection \<sigma>"
inductive_cases direct_subtype_Collection_x[elim]: "Collection \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Set[elim]: "\<tau> \<sqsubset> Set \<sigma>"
inductive_cases direct_subtype_Set_x[elim]: "Set \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_OrderedSet[elim]: "\<tau> \<sqsubset> OrderedSet \<sigma>"
inductive_cases direct_subtype_OrderedSet_x[elim]: "OrderedSet \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Bag[elim]: "\<tau> \<sqsubset> Bag \<sigma>"
inductive_cases direct_subtype_Bag_x[elim]: "Bag \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Sequence[elim]: "\<tau> \<sqsubset> Sequence \<sigma>"
inductive_cases direct_subtype_Sequence_x[elim]: "Sequence \<tau> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_Tuple[elim]: "\<tau> \<sqsubset> Tuple \<pi>"
inductive_cases direct_subtype_Tuple_x[elim]: "Tuple \<pi> \<sqsubset> \<sigma>"
inductive_cases direct_subtype_x_SupType[elim]: "\<tau> \<sqsubset> SupType"
inductive_cases direct_subtype_SupType_x[elim]: "SupType \<sqsubset> \<sigma>"
(*
lemma direct_subtype_antisym_Tuple:
  "Tuple \<xi> \<sqsubset> Tuple \<pi> \<Longrightarrow>
   length \<pi> = length \<xi> \<Longrightarrow>
   \<pi> \<noteq> \<xi> \<Longrightarrow>
   \<xi> \<noteq> [] \<Longrightarrow>
   list_all2 (\<lambda>\<tau> \<sigma>. \<tau> = \<sigma> \<or> \<tau> \<sqsubset> \<sigma> \<and> \<not> \<sigma> \<sqsubset> \<tau>) \<pi> \<xi> \<Longrightarrow>
   (\<And>\<tau> \<sigma>. \<tau> \<sqsubset>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<sqsubset>\<^sub>s \<tau> \<Longrightarrow> False) \<Longrightarrow> False"
  apply (erule direct_subtype.cases; auto)
  by (simp add: list_all2_append)
(*  by (metis (mono_tags, lifting) list_all2_antisym)*)

lemma q:
  "Tuple (xh @ x # xt) \<sqsubset> Tuple (xh @ y # xt) \<Longrightarrow> x \<sqsubset> y"
  apply (induct xh; induct xt; auto)
(*  apply (smt Nil_is_append_conv butlast.simps(2) butlast_append direct_subtype_x_Tuple hd_append list.distinct(1) list.sel(1) list.sel(3) type.inject(8) type.simps(46))*)

lemma q11:
  "Tuple [x] \<sqsubset> Tuple [y] \<Longrightarrow> x \<sqsubset> y"
(*  apply (smt Nil_is_append_conv butlast.simps(2) butlast_append direct_subtype_x_Tuple hd_append list.distinct(1) list.sel(1) list.sel(3) type.inject(8) type.simps(46))*)
  done
*)
lemma q21:
  "x # xs = yh @ xa # yt \<Longrightarrow>
   y # xs = yh @ ya # yt \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   yh = []"
  by (metis hd_append list.sel(1))

lemma q22:
  "x # xs = yh @ xa # yt \<Longrightarrow>
   y # xs = yh @ ya # yt \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   xs = yt"
  by (metis append_eq_Cons_conv list.inject)

lemma q23:
  "x # xs = yh @ xa # yt \<Longrightarrow>
   y # xs = yh @ ya # yt \<Longrightarrow>
   x \<noteq> y \<Longrightarrow>
   x = xa \<and> y = ya"
  by (metis hd_append list.sel(1))

lemma direct_subtype_antisym:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset> \<tau> \<Longrightarrow>
   False"
  apply (induct rule: direct_subtype.induct)
  using direct_basic_subtype_antisym apply auto
  apply (erule direct_subtype_Tuple_x)
  apply auto[1]
  apply auto[1]
  apply (auto simp add: only_one_def)[1]
  apply auto[1]
  unfolding only_one_def
  apply auto[1]
  apply (erule direct_subtype_Tuple_x)
  apply auto[1]
  apply auto[1]
  unfolding only_one_def
  apply auto[1]
  apply (smt append.assoc append.right_neutral append_Nil2 append_assoc append_eq_append_conv2 append_same_eq list.inject q22 q23 same_append_eq self_append_conv2)
  by auto

(*
lemma direct_subtype_not_trans:
  "\<tau> \<sqsubset> \<sigma> \<Longrightarrow>
   \<sigma> \<sqsubset> \<rho> \<Longrightarrow>
   \<not> \<rho> \<sqsubset> \<tau>"
  apply (induct arbitrary: \<rho> rule: direct_subtype.induct)
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
  using direct_basic_subtype.simps apply auto[1]
(*  using direct_basic_subtype.simps apply auto*)
*)
instantiation type :: (order) order
begin

definition "less_type \<equiv> direct_subtype\<^sup>+\<^sup>+"

definition "less_eq_type \<equiv> direct_subtype\<^sup>*\<^sup>*"

(*** Introduction Rules *****************************************************)

lemma subtype_x_OclVoid_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> OclVoid"
  "\<tau> = OclVoid \<Longrightarrow> \<tau> \<le> OclVoid"
  unfolding less_eq_type_def
  apply (simp add: direct_subtype.intros(1) r_into_rtranclp)
  by (simp)

lemma subtype_x_OclVoid_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < OclVoid"
  unfolding less_type_def
  by (simp add: direct_subtype.intros(1) tranclp.r_into_trancl)

lemma subtype_x_Required_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[1]"
  apply (auto)
  apply (induct \<sigma>)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  unfolding less_eq_basic_type_def less_eq_type_def
  by (metis direct_subtype.intros(4) fun_preserve_morphism_composition)
(*
  apply (metis direct_basic_subtype.intros(5) direct_subtype.intros(2) direct_subtype.intros(4) is_min_basic_type_code less_eq_type_def rtranclp.simps)
  apply (metis direct_basic_subtype_x_Boolean direct_subtype.intros(2) is_min_basic_type_def less_eq_type_def tranclp.r_into_trancl tranclp_into_rtranclp)
  apply (metis direct_basic_subtype.intros(2) direct_basic_subtype.intros(3) direct_subtype.intros(2) direct_subtype.intros(4) is_min_basic_type_code less_eq_type_def rtranclp.simps)
  apply (metis direct_basic_subtype.intros(2) direct_subtype.intros(2) direct_subtype.intros(4) is_min_basic_type_code less_eq_type_def rtranclp.simps)
  apply (simp add: direct_subtype.intros(2) is_min_basic_type_code less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) is_min_basic_type_code less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) less_eq_type_def r_into_rtranclp)
  unfolding less_eq_basic_type_def less_eq_type_def
  by (metis direct_subtype.intros(4) fun_preserve_morphism_composition)
*)
lemma subtype_x_Required_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < \<sigma>[1]"
  "\<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < \<sigma>[1]"
  unfolding less_type_def
  apply (simp add: direct_subtype.intros(2) tranclp.r_into_trancl)
  by (metis direct_subtype.intros(4) fun_preserve_morphism_composition' less_basic_type_def)
(*  apply (metis less_eq_type_def rtranclpD subtype_x_Required_intro'(1) type.distinct(23))
  by (metis less_eq_type_def less_imp_le rtranclpD subtype_x_Required_intro'(2) sup.strict_order_iff type.inject(1))*)
(*  apply (metis less_eq_type_def less_type_def rtranclpD subtype_x_Required_intro'(1) type.distinct(25))
  by (metis less_eq_type_def less_imp_le less_type_def rtranclpD subtype_x_Required_intro'(2) sup.strict_order_iff type.inject(1))*)

lemma subtype_x_Optional_intro' [intro]:
  "\<tau> = OclVoid \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> \<sigma>[?]"
  apply (auto)
  apply (simp add: direct_subtype.intros(3) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(6) less_eq_type_def rtranclp.rtrancl_into_rtrancl)
  unfolding less_eq_type_def less_eq_basic_type_def
  by (metis direct_subtype.intros(5) fun_preserve_morphism_composition)
(*  apply (induct \<sigma>)
  apply (metis String_is_min direct_basic_subtype.intros(5) direct_subtype.intros(3) direct_subtype.intros(5) less_eq_type_def rtranclp.simps)
  apply (simp add: direct_subtype.intros(3) less_eq_type_def r_into_rtranclp)
  apply (simp add: less_eq_type_def)
  apply (rule_tac ?y="UnlimitedNatural[?]" in rtranclp_trans)
  apply (simp add: direct_subtype.intros(3) r_into_rtranclp)
  apply (metis direct_basic_subtype.intros(2) direct_basic_subtype.intros(3) direct_subtype.intros(5) rtranclp.simps)
  apply (metis UnlimitedNatural_is_min direct_basic_subtype.intros(2) direct_subtype.intros(3) direct_subtype.intros(5) less_eq_type_def rtranclp_into_tranclp1 subtype_x_OclVoid_intro'(2) tranclp_into_rtranclp)
  apply (simp add: direct_subtype.intros(3) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(3) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(3) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(3) less_eq_type_def r_into_rtranclp)
  apply (simp add: direct_subtype.intros(6) less_eq_type_def rtranclp.rtrancl_into_rtrancl)
  unfolding less_eq_type_def less_eq_basic_type_def
  by (metis direct_subtype.intros(5) fun_preserve_morphism_composition)*)

lemma subtype_x_Optional_intro [intro]:
  "\<tau> = OclVoid \<Longrightarrow> \<tau> < \<sigma>[?]"
  "\<tau> < \<sigma>[1] \<Longrightarrow> \<tau> < \<sigma>[?]"
  "\<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < \<sigma>[?]"
  apply (simp add: direct_subtype.intros(3) less_type_def tranclp.r_into_trancl)
  apply (simp add: direct_subtype.intros(6) less_type_def tranclp.trancl_into_trancl)
  by (metis (mono_tags) less_eq_type_def less_le less_type_def rtranclpD subtype_x_Optional_intro'(3) type.inject(2))
(*  apply (metis less_eq_type_def less_type_def rtranclpD subtype_x_Optional_intro'(1) type.distinct(41))
  apply (simp add: direct_subtype.intros(6) less_type_def tranclp.trancl_into_trancl)
  by (metis less_eq_type_def less_imp_le less_type_def rtranclpD subtype_x_Optional_intro'(3) sup.strict_order_iff type.inject(2))*)

lemma subtype_OclInvalid_x_intro' [intro]:
  "OclInvalid \<le> \<sigma>"
  unfolding less_eq_type_def
  apply (induct \<sigma>)
  apply (metis direct_subtype.intros(22) direct_subtype.intros(25) rtranclp.simps)
  apply simp
  apply (simp add: direct_subtype.intros(1) r_into_rtranclp)
  apply (simp add: direct_subtype.intros(2) r_into_rtranclp)
  apply (metis (mono_tags) direct_subtype.intros(3) less_eq_type_def rtranclp.simps subtype_x_OclVoid_intro'(1))
  apply (rule_tac ?b="Set \<sigma>" in rtranclp.rtrancl_into_rtrancl)
  apply (metis (no_types, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(11) direct_subtype.intros(7) fun_preserve_morphism_composition)
  apply (simp add: direct_subtype.intros(16))
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(11) direct_subtype.intros(7) fun_preserve_morphism_composition)
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(12) direct_subtype.intros(8) fun_preserve_morphism_composition)
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(13) direct_subtype.intros(9) fun_preserve_morphism_composition)
  apply (metis (mono_tags, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(14) direct_subtype.intros(10) fun_preserve_morphism_composition)
  by (simp add: direct_subtype.intros(25) r_into_rtranclp)
(*  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]
  apply (rule_tac ?b="Set \<sigma>" in rtranclp.rtrancl_into_rtrancl)
  apply (metis (no_types, lifting) converse_rtranclp_into_rtranclp direct_subtype.intros(11) direct_subtype.intros(7) fun_preserve_morphism_composition)
  apply (simp add: direct_subtype.intros(16))
  apply (metis converse_rtranclp_into_rtranclp direct_subtype.intros(11) direct_subtype.intros(7) fun_preserve_morphism_composition)
  apply (metis converse_rtranclp_into_rtranclp direct_subtype.intros(12) direct_subtype.intros(8) fun_preserve_morphism_composition)
  apply (metis converse_rtranclp_into_rtranclp direct_subtype.intros(13) direct_subtype.intros(9) fun_preserve_morphism_composition)
  apply (metis converse_rtranclp_into_rtranclp direct_subtype.intros(14) direct_subtype.intros(10) fun_preserve_morphism_composition)
  apply (simp add: direct_subtype.intros(25) r_into_rtranclp)
  done*)

lemma subtype_OclInvalid_x_intro [intro]:
  "\<sigma> \<noteq> OclInvalid \<Longrightarrow> OclInvalid < \<sigma>"
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_OclInvalid_x_intro')

lemma subtype_OclVoid_x_intro' [intro]:
  "\<sigma> = OclVoid \<Longrightarrow> OclVoid \<le> \<sigma>"
  "\<sigma> = \<rho>[?] \<Longrightarrow> OclVoid \<le> \<sigma>"
  "\<sigma> = SupType \<Longrightarrow> OclVoid \<le> \<sigma>"
  apply (simp add: less_eq_type_def)
  apply (simp add: subtype_x_Optional_intro'(1))
  by (metis (mono_tags) direct_subtype.intros(20) less_eq_type_def rtranclp.simps subtype_x_Optional_intro'(1))

lemma subtype_OclVoid_x_intro [intro]:
  "\<sigma> = \<rho>[?] \<Longrightarrow> OclVoid < \<sigma>"
  "\<sigma> = SupType \<Longrightarrow> OclVoid < \<sigma>"
  apply (simp add: subtype_x_Optional_intro(1))
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_OclVoid_x_intro'(3) type.distinct(4))

lemma subtype_Optional_x_intro' [intro]:
  "\<sigma> = \<rho>[?] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> \<tau>[?] \<le> \<sigma>"
  "\<sigma> = SupType \<Longrightarrow> \<tau>[?] \<le> \<sigma>"
  apply (auto)
  apply (simp add: less_eq_type_def)
  apply (rule_tac ?b="OclAny[?]" in rtranclp.rtrancl_into_rtrancl)
  apply (induct \<tau>)
  apply simp
  apply (simp add: direct_basic_subtype.intros(1) direct_subtype.intros(5) r_into_rtranclp)
  apply (simp add: direct_basic_subtype.intros(4) direct_subtype.intros(5) r_into_rtranclp)
  apply (metis (mono_tags) less_eq_type_def order.strict_implies_order subtype_Integer_x_intro(2) subtype_x_Optional_intro'(3))
  apply (metis (mono_tags) less_eq_type_def order.strict_implies_order subtype_UnlimitedNatural_x_intro(3) subtype_x_Optional_intro'(3))
  apply (simp add: direct_basic_subtype.intros(5) direct_subtype.intros(5) r_into_rtranclp)
  apply (simp add: direct_basic_subtype.intros(6) direct_subtype.intros(5) r_into_rtranclp)
  apply (simp add: direct_basic_subtype.intros(8) direct_subtype.intros(5) r_into_rtranclp)
  by (simp add: direct_subtype.intros(20))
(*  using less_eq_type_def less_imp_le subtype_Integer_x_intro(2) apply auto[1]
  using less_eq_type_def less_imp_le subtype_UnlimitedNatural_x_intro(3) apply auto[1]
  apply (simp add: direct_basic_subtype.intros(5) direct_subtype.intros(5) r_into_rtranclp)
  apply (simp add: direct_basic_subtype.intros(6) direct_subtype.intros(5) r_into_rtranclp)
  apply (simp add: direct_basic_subtype.intros(7) direct_subtype.intros(5) r_into_rtranclp)
  by (simp add: direct_subtype.intros(20))*)

lemma subtype_Optional_x_intro [intro]:
  "\<sigma> = \<rho>[?] \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> \<tau>[?] < \<sigma>"
  "\<sigma> = SupType \<Longrightarrow> \<tau>[?] < \<sigma>"
  apply (simp add: subtype_x_Optional_intro(3))
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_Optional_x_intro'(2) type.distinct(8))

lemma subtype_Required_x_intro' [intro]:
  "\<sigma> = \<rho>[1] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> \<tau>[1] \<le> \<sigma>"
  "\<sigma> = \<rho>[?] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> \<tau>[1] \<le> \<sigma>"
  "\<sigma> = SupType \<Longrightarrow> \<tau>[1] \<le> \<sigma>"
  apply (auto)
  by (metis (mono_tags) converse_rtranclp_into_rtranclp direct_subtype.intros(6) less_eq_type_def subtype_Optional_x_intro'(2))
(*  by (metis direct_subtype.intros(6) less_eq_type_def rtranclp.rtrancl_refl rtranclp_into_tranclp1 subtype_Optional_x_intro'(2) tranclp_into_rtranclp tranclp_rtranclp_tranclp)*)

lemma subtype_Required_x_intro [intro]:
  "\<sigma> = \<rho>[1] \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> \<tau>[1] < \<sigma>"
  "\<sigma> = \<rho>[?] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> \<tau>[1] < \<sigma>"
  "\<sigma> = SupType \<Longrightarrow> \<tau>[1] < \<sigma>"
  apply (auto)
  apply (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_Required_x_intro'(2) type.distinct(55))
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_Required_x_intro'(3) type.distinct(6))

(*** Introduction Rules for Collection Types ********************************)

lemma subtype_x_Set_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Set \<sigma>"
  apply (auto)
  apply (simp add: less_eq_type_def)
  by (metis direct_subtype.intros(11) fun_preserve_morphism_composition)

lemma subtype_x_Set_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < Set \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Set \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro)
  apply (simp add: less_type_def)
  by (metis direct_subtype.intros(11) fun_preserve_morphism_composition')

lemma subtype_x_OrderedSet_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> OrderedSet \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro')
  apply (simp add: less_eq_type_def)
  by (metis direct_subtype.intros(12) fun_preserve_morphism_composition)

lemma subtype_x_OrderedSet_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < OrderedSet \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < OrderedSet \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro)
  apply (simp add: less_type_def)
  by (metis direct_subtype.intros(12) fun_preserve_morphism_composition')

lemma subtype_x_Bag_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Bag \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro')
  apply (simp add: less_eq_type_def)
  by (metis direct_subtype.intros(13) fun_preserve_morphism_composition)

lemma subtype_x_Bag_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < Bag \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Bag \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro)
  apply (simp add: less_type_def)
  by (metis direct_subtype.intros(13) fun_preserve_morphism_composition')

lemma subtype_x_Sequence_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Sequence \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro')
  apply (simp add: less_eq_type_def)
  by (metis direct_subtype.intros(14) fun_preserve_morphism_composition)

lemma subtype_x_Sequence_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < Sequence \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Sequence \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro)
  apply (simp add: less_type_def)
  by (metis direct_subtype.intros(14) fun_preserve_morphism_composition')

lemma subtype_x_Collection_intro' [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> \<le> Collection \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro')
  apply (metis (mono_tags, lifting) direct_subtype.intros(16) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Set_intro'(2))
  apply (metis (mono_tags, lifting) direct_subtype.intros(17) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_OrderedSet_intro'(2))
  apply (metis (mono_tags, lifting) direct_subtype.intros(18) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Bag_intro'(2))
  apply (metis (mono_tags, lifting) direct_subtype.intros(19) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Sequence_intro'(2))
  apply (simp add: less_eq_type_def)
  by (metis direct_subtype.intros(15) fun_preserve_morphism_composition)

lemma subtype_x_Collection_intro [intro]:
  "\<tau> = OclInvalid \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  "\<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> \<tau> < Collection \<sigma>"
  apply (simp add: subtype_OclInvalid_x_intro)
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def rtranclpD subtype_x_Collection_intro'(2) type.distinct(81))
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def rtranclpD subtype_x_Collection_intro'(3) type.distinct(83))
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def rtranclpD subtype_x_Collection_intro'(4) type.distinct(85))
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def rtranclpD subtype_x_Collection_intro'(5) type.distinct(87))
  apply (simp add: less_type_def)
  by (metis direct_subtype.intros(15) fun_preserve_morphism_composition')

lemma subtype_x_SupType_intro' [intro]:
  "\<tau> \<le> SupType"
  apply (induct \<tau>)
  apply (simp add: less_eq_type_def)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (metis (mono_tags, lifting) direct_subtype.intros(21) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Collection_intro'(6))
  apply (metis (mono_tags, lifting) direct_subtype.intros(21) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Collection_intro'(2))
  apply (metis (mono_tags, lifting) direct_subtype.intros(21) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Collection_intro'(3))
  apply (metis (mono_tags, lifting) direct_subtype.intros(21) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Collection_intro'(4))
  apply (metis (mono_tags, lifting) direct_subtype.intros(21) less_eq_type_def rtranclp.rtrancl_into_rtrancl subtype_x_Collection_intro'(5))
  apply (simp add: direct_subtype.intros(26) less_eq_type_def r_into_rtranclp)
  done

lemma subtype_x_SupType_intro [intro]:
  "\<tau> \<noteq> SupType \<Longrightarrow> \<tau> < SupType"
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def rtranclpD subtype_x_SupType_intro')

(*** Elemination Rules ******************************************************)

lemma subtype_SupType_x' [elim]:
  "SupType \<le> \<sigma> \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (erule converse_rtranclpE; auto)

lemma subtype_SupType_x [elim]:
  "SupType < \<sigma> \<Longrightarrow> False"
  unfolding less_type_def
  by (drule tranclpD; auto)

lemma subtype_OclInvalid_x [elim]:
  "OclInvalid < \<sigma> \<Longrightarrow>
   (\<sigma> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Tuple \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: tranclp_induct; blast)

lemma subtype_OclVoid_x' [elim]:
  "OclVoid \<le> \<sigma> \<Longrightarrow>
   (\<sigma> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (induct rule: rtranclp_induct; blast)

lemma subtype_OclVoid_x [elim]:
  "OclVoid < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (induct rule: tranclp_induct; blast)

lemma subtype_Required_x [elim]:
  "\<tau>[1] < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[1] \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (metis direct_subtype_Required_x less_basic_type_def order_refl_basic_type tranclp.r_into_trancl)
  apply (simp add: less_basic_type_def less_eq_basic_type_def)
  by (smt direct_subtype_Optional_x direct_subtype_Required_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl tranclp.trancl_into_trancl tranclp_into_rtranclp)

lemma subtype_Optional_x [elim]:
  "\<tau>[?] < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = \<rho>[?] \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (metis direct_subtype_Optional_x less_basic_type_def tranclp.r_into_trancl)
  by (metis (full_types) direct_subtype_Optional_x direct_subtype_SupType_x less_basic_type_def tranclp.simps)

lemma subtype_Collection_x' [elim]:
  "Collection \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)[1]
  by (metis direct_subtype_Collection_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl)

lemma subtype_Collection_x [elim]:
  "Collection \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)[1]
  by (metis direct_subtype_Collection_x direct_subtype_SupType_x tranclp.trancl_into_trancl)

lemma subtype_Set_x' [elim]:
  "Set \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_Set_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl)

lemma subtype_Set_x [elim]:
  "Set \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Set \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_Set_x direct_subtype_SupType_x tranclp.simps)

lemma subtype_OrderedSet_x' [elim]:
  "OrderedSet \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_OrderedSet_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl)

lemma subtype_OrderedSet_x [elim]:
  "OrderedSet \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = OrderedSet \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_eq_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_OrderedSet_x direct_subtype_SupType_x tranclp.simps)

lemma subtype_Bag_x [elim]:
  "Bag \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_Bag_x direct_subtype_SupType_x tranclp.simps)

lemma subtype_Sequence_x [elim]:
  "Sequence \<tau> < \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> = \<rho> \<or> \<tau> < \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (induct rule: tranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_Sequence_x direct_subtype_SupType_x tranclp.simps)

lemma subtype_Bag_x' [elim]:
  "Bag \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Bag \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_Bag_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl)

lemma subtype_Sequence_x' [elim]:
  "Sequence \<tau> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Sequence \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<sigma> = Collection \<rho> \<Longrightarrow> \<tau> \<le> \<rho> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  apply (induct rule: rtranclp_induct)
  apply (auto)
  by (smt direct_subtype_Collection_x direct_subtype_Sequence_x direct_subtype_SupType_x rtranclp.rtrancl_into_rtrancl)

(*  by (smt append_eq_append_conv append_self_conv length_append list.size(4) not_Cons_self2 only_one_def)*)

(*
lemma Tuple_functor:
  "functor_under_rel direct_subtype direct_subtype Tuple"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Required rangeI tranclp.simps)
*)


(*length \<xi> \<le> length \<pi> \<and>*)
definition "subtuple (\<pi>::'a type list) \<xi> \<equiv>
  list_all2 (\<le>) (take (length \<xi>) \<pi>) \<xi>"

lemma subtype_Tuple_x'' [elim]:
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def subtuple_def
  apply (induct rule: rtranclp_induct)
  apply (simp add: less_eq_type_def list.rel_refl subtuple_def)
  by blast

lemma subtype_Tuple_tr [elim]:
  "direct_subtype\<^sup>*\<^sup>* (Tuple x) y \<Longrightarrow>
   direct_subtype\<^sup>*\<^sup>* y (Tuple z) \<Longrightarrow>
   \<exists>a. y = Tuple a"
  by (metis (mono_tags) OCL_Types.subtype_SupType_x' OCL_Types.subtype_Tuple_x'' less_eq_type_def)
(*
lemma subtype_Tuple_x''' [elim]:
  "Tuple \<pi> \<le> Tuple \<xi> \<Longrightarrow> subtuple \<pi> \<xi>"
  unfolding less_eq_type_def subtuple_def
  apply (drule rtranclpD)
  apply (auto)
    apply (simp add: list_all2_refl)
  apply (erule tranclp_trans_induct)
*)
(*
lemma rel_limited_under_Tuple:
 "rel_limited_under direct_subtype Tuple"
  unfolding rel_limited_under_def
  apply auto
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.simps)

lemma inj_Tuple:
  "inj Tuple"
  by (simp add: inj_def)
*)
lemma direct_subtype_preserve_Tuple:
  "direct_subtype\<^sup>+\<^sup>+ (Tuple x) (Tuple y) \<Longrightarrow>
   (\<lambda>x y. Tuple x \<sqsubset> Tuple y)\<^sup>+\<^sup>+ x y"
  apply (rule tranclp_fun_preserve_gen_1)
  apply (simp add: inj_def)
  unfolding rel_limited_under_def
  apply auto[1]
  apply (metis (mono_tags, lifting) direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.simps)
  by simp
(*  apply (metis direct_subtype_x_OclInvalid direct_subtype_x_Tuple rangeI tranclp.simps)
  apply auto[1]
  done*)

lemma direct_subtype_preserve_Tuple':
  "(\<lambda>x y. Tuple x \<sqsubset> Tuple y)\<^sup>+\<^sup>+ x y \<Longrightarrow>
   length x \<ge> length y"
  apply (erule tranclp_trans_induct)
  apply (erule direct_subtype_Tuple_x; auto)
  apply (smt eq_iff length_append list.size(4) only_one_def)
  by auto

lemma direct_subtype_preserve_Tuple'':
  "direct_subtype\<^sup>+\<^sup>+ (Tuple x) (Tuple y) \<Longrightarrow>
   length x \<ge> length y"
  by (simp add: direct_subtype_preserve_Tuple direct_subtype_preserve_Tuple')

lemma direct_subtype_preserve_Tuple''':
  "direct_subtype\<^sup>*\<^sup>* (Tuple x) (Tuple y) \<Longrightarrow>
   length x \<ge> length y"
  by (metis Nitpick.rtranclp_unfold direct_subtype_preserve_Tuple'' eq_refl type.inject(8))
(*
lemma direct_subtype_preserve_Tuple_a:
  "(\<lambda>x y. Tuple x \<sqsubset> Tuple y)\<^sup>+\<^sup>+ \<pi> \<xi> \<Longrightarrow>
   list_all2 direct_subtype\<^sup>*\<^sup>* \<pi> \<xi>"
*)
lemma list_all2_direct_subtype_tr:
  "list_all2 direct_subtype\<^sup>*\<^sup>* x y \<Longrightarrow>
   list_all2 direct_subtype\<^sup>*\<^sup>* y z \<Longrightarrow>
   list_all2 direct_subtype\<^sup>*\<^sup>* x z"
  by (smt list_all2_trans rtranclp_trans)

thm direct_subtype_Tuple_x

lemma list_all2_direct_subtype_simp1:
  "(list_all2 direct_subtype)\<^sup>*\<^sup>* x y \<Longrightarrow> list_all2 direct_subtype\<^sup>*\<^sup>* x y"
  apply (induct rule: rtranclp_induct)
  apply (simp add: list_all2_refl)
  by (metis list_all2_direct_subtype_tr list_all2_mono r_into_rtranclp)
  (*by (smt Nitpick.rtranclp_unfold list_all2_refl list_all2_trans rtranclp_induct rtranclp_into_tranclp1)*)

(*
lemma list_all2_direct_subtype_simp2:
  "list_all2 direct_subtype\<^sup>*\<^sup>* x y \<Longrightarrow> (list_all2 direct_subtype)\<^sup>*\<^sup>* x y"
*)
(*
lemma only_one_direct_subtype_simp1:
  "only_one direct_subtype\<^sup>*\<^sup>* x y \<Longrightarrow> (only_one direct_subtype)\<^sup>*\<^sup>* x y"
  apply (auto simp add: only_one_def)

lemma only_one_direct_subtype_simp2:
  "(only_one direct_subtype)\<^sup>*\<^sup>* x y \<Longrightarrow> only_one direct_subtype\<^sup>*\<^sup>* x y"
  apply (induct rule: rtranclp_induct)
   apply (auto simp add: only_one_def)
*)
lemma only_one_implies_list_all1:
  "only_one direct_subtype x y \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> direct_subtype x y) x y"
  apply (auto simp add: only_one_def)
  by (simp add: list.rel_refl list_all2_appendI)

lemma only_one_implies_list_all2:
  "only_one direct_subtype x y \<Longrightarrow>
   list_all2 (\<lambda>x y. x = y \<or> direct_subtype x y)\<^sup>*\<^sup>* x y"
  by (metis (mono_tags, lifting) list_all2_mono only_one_implies_list_all1 r_into_rtranclp)

lemma only_one_implies_list_all3:
  "only_one direct_subtype x y \<Longrightarrow>
   list_all2 direct_subtype\<^sup>*\<^sup>* x y"
  by (metis (mono_tags, lifting) Nitpick.rtranclp_unfold list.rel_mono_strong only_one_implies_list_all1 r_into_rtranclp)

lemma only_one_implies_list_all4:
  "only_one direct_subtype\<^sup>*\<^sup>* x y \<Longrightarrow>
   list_all2 direct_subtype\<^sup>*\<^sup>* x y"
  by (smt Nitpick.rtranclp_unfold list.rel_mono_strong only_one''_def only_one_simp'')
(*
lemma list_all_implies_only_one1:
  "list_all2 direct_subtype x y \<Longrightarrow>
   (only_one direct_subtype)\<^sup>*\<^sup>* x y"

lemma list_all_implies_only_one2:
  "(\<lambda>x y. list_all2 direct_subtype x y)\<^sup>*\<^sup>* x y \<Longrightarrow>
   (\<lambda>x y. only_one direct_subtype x y)\<^sup>*\<^sup>* x y"
*)

lemma list_all2_direct_subtype:
  fixes x :: "'a type list"
    and y :: "'a type list"
  assumes prem: "direct_subtype\<^sup>*\<^sup>* (Tuple x) (Tuple y)"
  shows "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length y) x) y"
proof -
  obtain P where P: "(P :: 'a type list \<Rightarrow> 'a type list \<Rightarrow> bool) = (\<lambda>x y. list_all2 direct_subtype\<^sup>*\<^sup>* (take (length y) x) y)" by auto
  obtain r where r: "(r :: 'a type list \<Rightarrow> 'a type list \<Rightarrow> bool) = (\<lambda>x y. direct_subtype (Tuple x) (Tuple y))" by auto
  from prem r have major: "r\<^sup>*\<^sup>* x y"
    by (metis Nitpick.rtranclp_unfold direct_subtype_preserve_Tuple type.inject(8))
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y"
    apply auto
    apply (erule direct_subtype_Tuple_x; auto)
    apply (simp add: list.rel_refl)
    using list_all2_lengthD only_one_implies_list_all3 by fastforce
  from P have cases_2: "\<And>x y z. r\<^sup>*\<^sup>* x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>*\<^sup>* y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    apply auto
  proof -
    fix xa :: "'a type list" and ya :: "'a type list" and z :: "'a type list"
    assume a1: "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length ya) xa) ya"
    assume a2: "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length z) ya) z"
    then have f3: "length (take (length z) ya) = length z"
by (metis list_all2_lengthD)
  have f4: "\<forall>n ts. length (take n (ts::'a type list)) = min (length ts) n"
    by (metis length_take)
  then have f5: "min (length ya) (length z) = length z"
    using f3 by metis
  then have f6: "take (length z) xa @ [] = take (min (length ya) (length z)) (take (length ya) xa @ drop (length ya) xa)"
    by auto
  have f7: "length (take (length ya) xa) = length ya"
    using a1 by (metis list_all2_lengthD)
  then have "length z = min (min (length xa) (length ya)) (min (length ya) (length z))"
    using f3 by auto
  then have "length (take (length z) xa) = min (length ya) (length z)"
    using f5 f4 by (metis (no_types) min.assoc)
  then show "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length z) xa) z"
    using f7 f6 f4 f3 a2 a1 by (metis (no_types) append_eq_append_conv list_all2_direct_subtype_tr list_all2_takeI take_append)
qed
  from major cases_1 cases_2 have inv_conc: "P x y"
    by (smt P converse_rtranclpE converse_rtranclp_into_rtranclp direct_subtype_preserve_Tuple''' list_all2_direct_subtype_simp1 r_into_rtranclp rtranclp.rtrancl_refl rtranclp_induct take_all)
  with P show ?thesis by simp
qed

(*
lemma list_all2_direct_subtype:
  assumes prem: "direct_subtype\<^sup>*\<^sup>* (Tuple x) (Tuple y)"
  shows "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length y) x) y"
proof -
  obtain P where P: "P = (\<lambda>x y. list_all2 direct_subtype\<^sup>*\<^sup>* (take (length y) x) y)" by auto
  obtain r where r: "r = (\<lambda>x y. direct_subtype (Tuple x) (Tuple y))" by auto
  from prem r have major: "r\<^sup>*\<^sup>* x y"
    by (metis Nitpick.rtranclp_unfold direct_subtype_preserve_Tuple type.inject(8))
  from P r have cases_1: "\<And>x y. r x y \<Longrightarrow> P x y"
    apply auto
    apply (erule direct_subtype_Tuple_x; auto)
    apply (simp add: list.rel_refl)
    using list_all2_lengthD only_one_implies_list_all3 by fastforce
  from P have cases_2: "\<And>x y z. r\<^sup>*\<^sup>* x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>*\<^sup>* y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    apply auto
  proof -
    fix xa :: "OCL_Types.type list" and ya :: "OCL_Types.type list" and z :: "OCL_Types.type list"
    assume a1: "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length ya) xa) ya"
    assume a2: "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length z) ya) z"
    then have f3: "length (take (length z) ya) = length z"
by (metis list_all2_lengthD)
  have f4: "\<forall>n ts. length (take n (ts::OCL_Types.type list)) = min (length ts) n"
    by (metis length_take)
  then have f5: "min (length ya) (length z) = length z"
    using f3 by metis
  then have f6: "take (length z) xa @ [] = take (min (length ya) (length z)) (take (length ya) xa @ drop (length ya) xa)"
    by auto
  have f7: "length (take (length ya) xa) = length ya"
    using a1 by (metis list_all2_lengthD)
  then have "length z = min (min (length xa) (length ya)) (min (length ya) (length z))"
    using f3 by auto
  then have "length (take (length z) xa) = min (length ya) (length z)"
    using f5 f4 by (metis (no_types) min.assoc)
  then show "list_all2 direct_subtype\<^sup>*\<^sup>* (take (length z) xa) z"
    using f7 f6 f4 f3 a2 a1 by (metis (no_types) append_eq_append_conv list_all2_direct_subtype_tr list_all2_takeI take_append)
qed
  from major cases_1 cases_2 have inv_conc: "P x y"
    by (smt P converse_rtranclpE converse_rtranclp_into_rtranclp direct_subtype_preserve_Tuple''' list_all2_direct_subtype_simp1 r_into_rtranclp rtranclp.rtrancl_refl rtranclp_induct take_all)
  with P show ?thesis by simp
qed
*)
(*
lemma direct_subtype_preserve_Tuple_a:
  "(\<lambda>x y. Tuple x \<sqsubset> Tuple y)\<^sup>*\<^sup>* \<pi> \<xi> \<Longrightarrow>
   list_all2 direct_subtype\<^sup>*\<^sup>* \<pi> \<xi>"
  apply (erule converse_rtranclpE)
  apply (simp add: list.rel_refl)
*)
lemma subtype_Tuple_x' [elim]:
  "Tuple \<pi> \<le> \<sigma> \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> subtuple \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def subtuple_def
  apply (induct rule: rtranclp_induct)
  apply (simp add: less_eq_type_def list.rel_refl subtuple_def)
  by (metis (mono_tags) less_eq_type_def list_all2_direct_subtype rtranclp.rtrancl_into_rtrancl subtype_Tuple_x'')

lemma q:
  "direct_subtype\<^sup>*\<^sup>* z \<sigma> \<Longrightarrow>
   Tuple \<pi> \<sqsubset> z \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> \<pi> \<noteq> \<xi> \<Longrightarrow> list_all2 (\<le>) (take (length \<xi>) \<pi>) \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: rtranclp_induct)
  apply (metis (mono_tags, lifting) direct_subtype_antisym less_eq_type_def rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl subtuple_def subtype_Tuple_x')
  apply auto
(*  by (smt converse_rtranclp_into_rtranclp less_eq_type_def rtranclp.rtrancl_into_rtrancl subtuple_def subtype_Tuple_x')*)

lemma subtype_Tuple_x [elim]:
  "Tuple \<pi> < \<sigma> \<Longrightarrow>
   (\<And>\<xi>. \<sigma> = Tuple \<xi> \<Longrightarrow> \<pi> \<noteq> \<xi> \<Longrightarrow> subtuple \<pi> \<xi> \<Longrightarrow> P) \<Longrightarrow>
   (\<sigma> = SupType \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def subtuple_def
  apply (drule tranclpD; auto)
(*  apply (induct rule: tranclp_induct)
  apply (metis (mono_tags, lifting) direct_subtype_antisym less_eq_type_def rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl subtuple_def subtype_Tuple_x')
  apply (simp add: less_type_def list.rel_refl subtuple_def)
*)

lemma Required_functor:
  "functor_under_rel direct_basic_subtype direct_subtype Required"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Required rangeI tranclp.simps)

lemma Optional_functor:
  "functor_under_rel direct_basic_subtype direct_subtype Optional"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis (mono_tags) OCL_Types.subtype_Optional_x direct_subtype_SupType_x less_type_def rangeI)

lemma Required_Optional_natural:
  "natural_under_rel direct_basic_subtype direct_subtype Required Optional"
  apply (auto simp add: natural_under_rel_def Required_functor Optional_functor direct_subtype.intros(6))
  apply (metis (mono_tags) OCL_Types.subtype_Optional_x less_type_def type.simps(14) type.simps(64))
  by (metis (mono_tags) OCL_Types.subtype_Required_x direct_subtype_SupType_x less_type_def tranclpD)

lemma Set_functor:
  "functor_under_rel direct_subtype direct_subtype Set"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Set rangeI tranclp.cases)

lemma OrderedSet_functor:
  "functor_under_rel direct_subtype direct_subtype OrderedSet"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_OrderedSet rangeI tranclp.cases)

lemma Bag_functor:
  "functor_under_rel direct_subtype direct_subtype Bag"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Bag rangeI tranclp.cases)

lemma Sequence_functor:
  "functor_under_rel direct_subtype direct_subtype Sequence"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis direct_subtype_x_OclInvalid direct_subtype_x_Sequence rangeI tranclp.cases)

lemma Collection_functor:
  "functor_under_rel direct_subtype direct_subtype Collection"
  apply (auto simp add: functor_under_rel_def rel_limited_under_def inj_def)
  by (metis (mono_tags) OCL_Types.subtype_Collection_x direct_subtype_SupType_x less_type_def rangeI)

lemma Set_Collection_natural:
  "natural_under_rel direct_subtype direct_subtype Set Collection"
  apply (auto simp add: natural_under_rel_def Set_functor Collection_functor)
  apply (simp add: direct_subtype.intros(16))
  apply (metis (mono_tags) OCL_Types.subtype_Collection_x less_type_def type.simps(20) type.simps(90))
  by (metis (mono_tags) OCL_Types.subtype_Set_x direct_subtype_SupType_x less_type_def tranclpD)


lemma subtype_x_OclInvalid' [elim]:
  "\<tau> \<le> OclInvalid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (metis direct_subtype_x_OclInvalid rtranclp.cases)

lemma subtype_x_OclInvalid [elim]:
  "\<tau> < OclInvalid \<Longrightarrow> False"
  unfolding less_type_def
  by (metis direct_subtype_x_OclInvalid tranclp.cases)

lemma subtype_x_OclVoid' [elim]:
  "\<tau> \<le> OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_eq_type_def
  by (metis (mono_tags, lifting) direct_subtype_x_OclVoid less_eq_type_def rtranclp.cases subtype_x_OclInvalid')

lemma subtype_x_OclVoid [elim]:
  "\<tau> < OclVoid \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  by (metis (mono_tags, lifting) direct_subtype_x_OclVoid less_type_def subtype_x_OclInvalid tranclp.simps)

lemma subtype_x_Required':
  "\<tau> < \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
  apply (drule tranclpD; auto)
  apply (erule direct_subtype.cases; auto)
  apply (metis (mono_tags) less_type_def rtranclpD subtype_Optional_x type.simps(14) type.simps(64))
  apply (metis (mono_tags) less_type_def rtranclpD subtype_Optional_x type.simps(14) type.simps(64))
  apply (metis (mono_tags) OCL_Types.subtype_Set_x' less_eq_type_def type.distinct(5) type.distinct(57) type.distinct(59))
  apply (metis (mono_tags) OCL_Types.subtype_OrderedSet_x' less_eq_type_def type.distinct(5) type.distinct(57) type.distinct(61))
  apply (metis (mono_tags) OCL_Types.subtype_Bag_x' less_eq_type_def type.distinct(5) type.distinct(57) type.distinct(63))
  apply (metis (mono_tags) OCL_Types.subtype_Sequence_x' less_eq_type_def type.distinct(5) type.distinct(57) type.distinct(65))
  apply (metis (mono_tags) less_eq_type_def subtype_Collection_x' type.distinct(5) type.simps(66))
  apply (metis (mono_tags) less_eq_type_def subtype_Collection_x' type.distinct(5) type.simps(66))
  apply (metis (mono_tags) less_eq_type_def subtype_Collection_x' type.distinct(5) type.simps(66))
  apply (metis (mono_tags) less_eq_type_def subtype_Collection_x' type.distinct(5) type.simps(66))
  apply (metis (mono_tags) less_eq_type_def subtype_Collection_x' type.distinct(5) type.simps(66))
  apply (metis (mono_tags) less_eq_type_def subtype_SupType_x' type.simps(14))
  apply (metis (mono_tags) less_eq_type_def subtype_SupType_x' type.simps(14))
  apply (metis (mono_tags) less_eq_type_def subtype_SupType_x' type.simps(14))
  apply (metis (mono_tags) less_eq_type_def subtype_Tuple_x'' type.simps(14) type.simps(76))
  apply (metis (mono_tags) OCL_Types.subtype_Tuple_x' less_eq_type_def type.distinct(5) type.simps(76))
  by (metis (mono_tags) less_eq_type_def subtype_SupType_x' type.simps(14))
(*  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_type_def rtranclpD apply fastforce
  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]
  using less_eq_type_def apply auto[1]*)

lemma subtype_x_Required'' [elim]:
  "\<tau> < \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def less_basic_type_def
  by (metis (mono_tags) Required_functor less_type_def subtype_x_Required' tranclp_fun_preserve_gen_1a)

lemma subtype_x_Required''' [elim]:
  "\<tau> \<le> \<sigma>[1] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (mono_tags, lifting) Nitpick.rtranclp_unfold less_eq_type_def less_imp_le less_type_def order_eq_refl subtype_x_Required'')

lemma subtype_x_Optional':
  "\<tau> < \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<exists>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> P) \<Longrightarrow> 
   (\<exists>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding less_type_def
(*  apply (drule tranclpD; auto)
  apply (erule direct_subtype.cases)
  using less_eq_type_def apply auto
  apply (metis  less_eq_type_def subtype_Set_x' type.distinct(69) type.distinct(7) type.distinct(71))
  apply (metis (full_types) less_eq_type_def subtype_Set_x' type.distinct(69) type.distinct(7) type.distinct(71))
*)
  done

lemma subtype_x_Optional'':
  "\<tau> < \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> = \<sigma> \<or> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis le_imp_less_or_eq subtype_Optional_x subtype_Required_x subtype_x_Optional' type.distinct(55) type.distinct(7) type.inject(2))

lemma subtype_x_Optional [elim]:
  "\<tau> < \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis eq_refl less_imp_le subtype_x_Optional'')

lemma subtype_x_Optional''' [elim]:
  "\<tau> \<le> \<sigma>[?] \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<tau> = OclVoid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = \<rho>[1] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = \<rho>[?] \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (mono_tags, lifting) Nitpick.rtranclp_unfold eq_refl less_eq_type_def less_imp_le less_type_def subtype_x_Optional'')

lemma subtype_x_Set' [elim]:
  "\<tau> \<le> Set \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  apply (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_Required_x type.distinct(59) type.simps(20) type.simps(80))
  by (metis (mono_tags) less_eq_type_def less_type_def rtranclpD subtype_Optional_x type.distinct(11) type.distinct(71))

lemma subtype_x_Set [elim]:
  "\<tau> < Set \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  using subtype_SupType_x apply auto[1]
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_x_Set' tranclp_into_rtranclp type.simps(106) type.simps(46))

lemma subtype_x_OrderedSet' [elim]:
  "\<tau> \<le> OrderedSet \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  apply (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def less_type_def subtype_Required_x type.distinct(61) type.simps(22) type.simps(82))
  by (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def less_type_def subtype_Optional_x type.distinct(13) type.distinct(73))

lemma subtype_x_OrderedSet [elim]:
  "\<tau> < OrderedSet \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  using subtype_SupType_x apply auto
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_x_OrderedSet' tranclp_into_rtranclp type.simps(112) type.simps(46))

lemma subtype_x_Bag' [elim]:
  "\<tau> \<le> Bag \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  apply (metis (mono_tags) direct_subtype.intros(18) less_eq_type_def less_type_def rtranclp_into_tranclp1 subtype_Required_x type.simps(18) type.simps(66) type.simps(78))
  by (metis (mono_tags) direct_subtype.intros(18) less_eq_type_def less_type_def rtranclp_into_tranclp1 subtype_Optional_x type.distinct(69) type.distinct(9))

lemma subtype_x_Bag [elim]:
  "\<tau> < Bag \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  using subtype_SupType_x apply auto
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_x_Bag' tranclp_into_rtranclp type.simps(116) type.simps(46))

lemma subtype_x_Sequence' [elim]:
  "\<tau> \<le> Sequence \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  apply (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def less_type_def subtype_Required_x type.distinct(65) type.simps(26) type.simps(86))
  by (metis (mono_tags) direct_subtype.intros(19) less_eq_type_def less_type_def rtranclp_into_tranclp1 subtype_Optional_x type.distinct(69) type.distinct(9))

lemma subtype_x_Sequence [elim]:
  "\<tau> < Sequence \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  using subtype_SupType_x apply auto
  by (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_x_Sequence' tranclp_into_rtranclp type.simps(118) type.simps(46))

lemma subtype_x_Collection' [elim]:
  "\<tau> \<le> Collection \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  apply (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def less_type_def subtype_Required_x type.distinct(57) type.distinct(69) type.distinct(9))
  by (metis (mono_tags) Nitpick.rtranclp_unfold less_eq_type_def less_type_def subtype_Optional_x type.distinct(69) type.simps(18))

lemma subtype_x_Collection [elim]:
  "\<tau> < Collection \<sigma> \<Longrightarrow>
   (\<tau> = OclInvalid \<Longrightarrow> P) \<Longrightarrow>
   (\<And>\<rho>. \<tau> = Set \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = OrderedSet \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Bag \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Sequence \<rho> \<Longrightarrow> \<rho> \<le> \<sigma> \<Longrightarrow> P) \<Longrightarrow> 
   (\<And>\<rho>. \<tau> = Collection \<rho> \<Longrightarrow> \<rho> < \<sigma> \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct \<tau>; auto)
  using subtype_SupType_x apply auto[1]
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_Set_x' tranclp_into_rtranclp type.inject(3) type.simps(18) type.simps(90))
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_OrderedSet_x' tranclp_into_rtranclp type.inject(3) type.simps(18) type.simps(92))
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_Bag_x' tranclp_into_rtranclp type.inject(3) type.simps(18) type.simps(94))
  apply (metis (mono_tags, lifting) less_eq_type_def less_type_def subtype_Sequence_x' tranclp_into_rtranclp type.inject(3) type.simps(18) type.simps(96))
  by (metis (mono_tags) less_eq_type_def less_type_def subtype_Tuple_x'' tranclp_into_rtranclp type.simps(18) type.simps(98))


lemma direct_subtype_acyclic':
  "direct_subtype\<^sup>+\<^sup>+ \<tau> \<tau> \<Longrightarrow> False"
  using less_type_def 
  apply (induct \<tau>; auto)

lemma direct_subtype_acyclic:
  "acyclicP direct_subtype"
  apply (rule acyclicI)
  apply (auto simp add: trancl_def)
  apply (erule direct_subtype_acyclic')
  done




lemma less_le_not_le_type:
  "\<tau> < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  for \<tau> \<sigma> :: "'a type"
  apply (rule iffI; auto simp add: less_type_def less_eq_type_def)
  apply (meson direct_subtype_acyclic' tranclp_rtranclp_tranclp)
  by (metis rtranclpD)

lemma order_refl_type [iff]:
  "\<tau> \<le> \<tau>"
  for \<tau> :: "'a type"
  by (simp add: less_eq_type_def)

lemma order_trans_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: "'a type"
  by (auto simp add: less_eq_type_def)

lemma antisym_type:
  "\<tau> \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  for \<tau> \<sigma> :: "'a type"
  by (metis (mono_tags, lifting) less_eq_type_def less_le_not_le_type less_type_def rtranclpD)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  done

end

instantiation type :: (semilattice_sup) semilattice_sup
begin

(*definition "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else SupType))"*)

fun sup_type where
  "OclInvalid \<squnion> \<sigma> = \<sigma>"
| "OclVoid \<squnion> \<sigma> = (case \<sigma>
    of OclVoid \<Rightarrow> OclVoid
     | OclInvalid \<Rightarrow> OclVoid
     | Required \<rho> \<Rightarrow> Optional \<rho>
     | Optional \<rho> \<Rightarrow> Optional \<rho>
     | _ \<Rightarrow> SupType)"
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
| "Set \<tau> \<squnion> \<sigma> = (case \<sigma>
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
| "Tuple \<pi> \<squnion> \<sigma> = (case \<sigma>
    of Tuple \<xi> \<Rightarrow> Tuple (\<tau> \<squnion> \<rho>)
     | OclInvalid \<Rightarrow> Tuple \<pi>
     | _ \<Rightarrow> SupType)"
| "SupType \<squnion> \<sigma> = SupType"
  by pat_completeness auto
  termination by lexicographic_order

lemma OclVoid_less_eq_sup:
  "OclVoid \<le> OclVoid \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Required_less_eq_sup:
  "Required \<tau> \<le> Required \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Optional_less_eq_sup:
  "Optional \<tau> \<le> Optional \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Set_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Set \<tau> \<le> Set \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma OrderedSet_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   OrderedSet \<tau> \<le> OrderedSet \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Bag_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Bag \<tau> \<le> Bag \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Sequence_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Sequence \<tau> \<le> Sequence \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma Collection_less_eq_sup:
  "(\<And>\<sigma>. \<tau> \<le> \<tau> \<squnion> \<sigma>) \<Longrightarrow>
   Collection \<tau> \<le> Collection \<tau> \<squnion> \<sigma>"
  by (induct \<sigma>; auto)

lemma sup_ge1_type:
  "\<tau> \<le> \<tau> \<squnion> \<sigma>"
  for \<tau> \<sigma> :: type
  apply (induct \<tau> arbitrary: \<sigma>)
  apply simp
  apply (simp add: subtype_OclInvalid_x_intro')
  using OclVoid_less_eq_sup apply auto[1]
  using Required_less_eq_sup apply auto[1]
  using Optional_less_eq_sup apply auto[1]
  using Collection_less_eq_sup apply auto[1]
  using Set_less_eq_sup apply auto[1]
  using OrderedSet_less_eq_sup apply auto[1]
  using Bag_less_eq_sup apply auto[1]
  using Sequence_less_eq_sup apply auto[1]
  done

lemma OclVoid_sup_commut:
  "OclVoid \<squnion> \<sigma> = \<sigma> \<squnion> OclVoid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma OclInvalid_sup_commut:
  "OclInvalid \<squnion> \<sigma> = \<sigma> \<squnion> OclInvalid"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma Required_sup_commut:
  "Required \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Required \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma Optional_sup_commut:
  "Optional \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Optional \<tau>"
  by (cases \<sigma>; simp add: sup_commute)

lemma Set_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Set \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Set \<tau>"
  by (cases \<sigma>; simp)

lemma OrderedSet_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   OrderedSet \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> OrderedSet \<tau>"
  by (cases \<sigma>; simp)

lemma Bag_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Bag \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Bag \<tau>"
  by (cases \<sigma>; simp)

lemma Sequence_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Sequence \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Sequence \<tau>"
  by (cases \<sigma>; simp)

lemma Collection_sup_commut:
  "(\<And>\<sigma>. \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>) \<Longrightarrow>
   Collection \<tau> \<squnion> \<sigma> = \<sigma> \<squnion> Collection \<tau>"
  by (cases \<sigma>; simp)

lemma Sup_sup_commut:
  "SupType \<squnion> \<sigma> = \<sigma> \<squnion> SupType"
  by (cases \<sigma>; simp add: less_eq_type_def)

lemma sup_commut_type:
  "\<tau> \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  for \<tau> \<sigma> :: type
  apply (induct \<tau> arbitrary: \<sigma>)
  using Sup_sup_commut apply auto[1]
  using OclInvalid_sup_commut apply auto[1]
  using OclVoid_sup_commut apply auto[1]
  using Required_sup_commut apply auto[1]
  using Optional_sup_commut apply auto[1]
  using Collection_sup_commut apply auto[1]
  using Set_sup_commut apply auto[1]
  using OrderedSet_sup_commut apply auto[1]
  using Bag_sup_commut apply auto[1]
  using Sequence_sup_commut apply auto[1]
  done

lemma sup_least_type:
  "\<tau> \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  for \<tau> \<sigma> \<rho> :: type
  apply (induct \<rho> arbitrary: \<tau> \<sigma>)
  apply (simp add: subtype_x_SupType_intro')
  apply fastforce
  apply (erule subtype_x_OclVoid'; erule subtype_x_OclVoid'; auto)
  apply (erule subtype_x_Required'''; erule subtype_x_Required'''; auto)
  apply (erule subtype_x_Optional'''; erule subtype_x_Optional'''; auto)
  apply (erule subtype_x_Collection'; erule subtype_x_Collection'; auto)
  apply (erule subtype_x_Set'; erule subtype_x_Set'; auto)
  apply (erule subtype_x_OrderedSet'; erule subtype_x_OrderedSet'; auto)
  apply (erule subtype_x_Bag'; erule subtype_x_Bag'; auto)
  apply (erule subtype_x_Sequence'; erule subtype_x_Sequence'; auto)
  done

instance
  apply intro_classes
  apply (simp add: sup_ge1_type)
  apply (simp add: sup_commut_type sup_ge1_type)
  by (simp add: sup_least_type)

end


fun subtype_fun :: "type \<Rightarrow> type \<Rightarrow> bool" where
  "subtype_fun OclInvalid \<sigma> = (\<sigma> \<noteq> OclInvalid)"
| "subtype_fun OclVoid (Optional \<sigma>) = True"
| "subtype_fun OclVoid SupType = True"
| "subtype_fun OclVoid _ = False"
| "subtype_fun (Required \<tau>) (Required \<sigma>) = basic_subtype_fun \<tau> \<sigma>"
| "subtype_fun (Required \<tau>) (Optional \<sigma>) = (\<tau> = \<sigma> \<or> basic_subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Required \<tau>) SupType = True"
| "subtype_fun (Required \<tau>) _ = False"
| "subtype_fun (Optional \<tau>) (Optional \<sigma>) = basic_subtype_fun \<tau> \<sigma>"
| "subtype_fun (Optional \<tau>) SupType = True"
| "subtype_fun (Optional \<tau>) _ = False"
| "subtype_fun (Set \<tau>) (Set \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Set \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Set \<tau>) SupType = True"
| "subtype_fun (Set \<tau>) _ = False"
| "subtype_fun (OrderedSet \<tau>) (OrderedSet \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (OrderedSet \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (OrderedSet \<tau>) SupType = True"
| "subtype_fun (OrderedSet \<tau>) _ = False"
| "subtype_fun (Bag \<tau>) (Bag \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Bag \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Bag \<tau>) SupType = True"
| "subtype_fun (Bag \<tau>) _ = False"
| "subtype_fun (Sequence \<tau>) (Sequence \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Sequence \<tau>) (Collection \<sigma>) = (\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma>)"
| "subtype_fun (Sequence \<tau>) SupType = True"
| "subtype_fun (Sequence \<tau>) _ = False"
| "subtype_fun (Collection \<tau>) (Collection \<sigma>) = subtype_fun \<tau> \<sigma>"
| "subtype_fun (Collection \<tau>) SupType = True"
| "subtype_fun (Collection \<tau>) _ = False"
| "subtype_fun SupType _ = False"


lemma less_type_code [code_abbrev, simp]:
  "subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> < \<sigma>"
  apply (rule iffI)
  apply (induct rule: subtype_fun.induct; auto)
  apply (induct \<tau> arbitrary: \<sigma>)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (erule subtype_Required_x; auto)
  using less_eq_basic_type_code less_basic_type_code apply auto[1]
  apply (erule subtype_Optional_x; simp)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  done

lemma less_eq_type_code [code_abbrev]:
  "\<tau> = \<sigma> \<or> subtype_fun \<tau> \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma>"
  using le_less by auto


value "Optional OclAny \<sqsubset> SupType"
value "Collection (Optional OclAny) \<sqsubset> SupType"
value "Collection (Optional OclAny) < SupType"
value "Collection (Collection (Optional OclAny)) \<sqsubset> SupType"
value "Collection (Collection (Optional OclAny)) < SupType"
value "Collection SupType \<sqsubset> SupType"
value "Set OclInvalid \<sqsubset> Set (OrderedSet OclInvalid)"
value "Collection (Collection SupType) \<sqsubset> Collection SupType"
value "Collection (Collection (Collection SupType)) \<sqsubset> Collection (Collection SupType)"
value "Collection (Collection (Collection (Collection SupType))) \<sqsubset> Collection (Collection (Collection SupType))"
value "Collection (Collection (Collection SupType)) \<sqsubset> Collection SupType"
value "Set (Required Integer) \<sqsubset> Collection (Optional Real)"
value "Set (Required Integer) \<sqsubset> Set (Required Real)"
value "Required Integer \<squnion> Optional Real"
value "(Set (Required Integer)) \<squnion> (Set (Required Real))"
value "(Set (Required Integer)) \<squnion> (Bag (Optional Boolean))"
value "(Set (Required Integer)) \<squnion> Optional Real"

end

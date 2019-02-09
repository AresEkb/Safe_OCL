(*  Title:       Safe OCL
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Expressions Normal Form\<close>
theory OCL_Normal_Form
  imports OCL_Typing
begin

text \<open>
  \autoref{tab:norm_rules} describes normalization rules for OCL expressions.
  The following variables are used in the table:
\begin{itemize}
\item \<^verbatim>\<open>x\<close> is a non-nullable value.
\item \<^verbatim>\<open>n\<close> is a nullable value. 
\item \<^verbatim>\<open>xs\<close> is a collection of non-nullable values.
\item \<^verbatim>\<open>ns\<close> is a collection of nullable values. 
\end{itemize}

\begin{table}[h!]
  \begin{center}
    \caption{Normalization rules}
    \label{tab:norm_rules}
    \begin{tabular}{c|c}
      \textbf{Original expression} & \textbf{Normalized expression}\\
      \hline
      \<^verbatim>\<open>x.op()\<close> & \<^verbatim>\<open>x.op()\<close>\\
      \<^verbatim>\<open>n.op()\<close> & ---\\
      \<^verbatim>\<open>x?.op()\<close> & ---\\
      \<^verbatim>\<open>n?.op()\<close> & \<^verbatim>\<open>if n <> null then n.op() else null endif\<close>\\
      \<^verbatim>\<open>x->op()\<close> & \<^verbatim>\<open>x.oclAsSet()->op()\<close>\\
      \<^verbatim>\<open>n->op()\<close> & \<^verbatim>\<open>n.oclAsSet()->op()\<close>\\
      \<^verbatim>\<open>x?->op()\<close> & ---\\
      \<^verbatim>\<open>n?->op()\<close> & ---\\
      \hline
      \<^verbatim>\<open>xs.op()\<close> & \<^verbatim>\<open>xs->collect(x | x.op())\<close>\\
      \<^verbatim>\<open>ns.op()\<close> & ---\\
      \<^verbatim>\<open>xs?.op()\<close> & ---\\
      \<^verbatim>\<open>ns?.op()\<close> & \<^verbatim>\<open>ns->excluding(null)->collect(x | x.op())\<close>\\
      \<^verbatim>\<open>xs->op()\<close> & \<^verbatim>\<open>xs->op()\<close>\\
      \<^verbatim>\<open>ns->op()\<close> & \<^verbatim>\<open>ns->op()\<close>\\
      \<^verbatim>\<open>xs?->op()\<close> & ---\\
      \<^verbatim>\<open>ns?->op()\<close> & \<^verbatim>\<open>ns->excluding(null)->op()\<close>\\
    \end{tabular}
  \end{center}
\end{table}\<close>

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition "new_vname \<equiv> String.implode \<circ> string_of_nat \<circ> fcard \<circ> fmdom"

inductive normalize
    :: "('a :: ocl_object_model) type env \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> bool"
    ("_ \<turnstile> _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_call ("_ \<turnstile>\<^sub>C _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_expr_list ("_ \<turnstile>\<^sub>L _ \<Rrightarrow>/ _" [51,51,51] 50)
    where
 LiteralN:
  "\<Gamma> \<turnstile> Literal a \<Rrightarrow> Literal a"
|LetN:
  "\<Gamma> \<turnstile> init\<^sub>1 \<Rrightarrow> init\<^sub>2 \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Let v \<tau> init\<^sub>1 body\<^sub>1 \<Rrightarrow> Let v \<tau> init\<^sub>2 body\<^sub>2"
|VarN:
  "\<Gamma> \<turnstile> Var v \<Rrightarrow> Var v"
|IfN:
  "\<Gamma> \<turnstile> a\<^sub>1 \<Rrightarrow> a\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> b\<^sub>1 \<Rrightarrow> b\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> c\<^sub>1 \<Rrightarrow> c\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> If a\<^sub>1 b\<^sub>1 c\<^sub>1 \<Rrightarrow> If a\<^sub>2 b\<^sub>2 c\<^sub>2"

|MetaOperationCallN:
  "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> MetaOperationCall \<tau> op"
|StaticOperationCallN:
  "\<Gamma> \<turnstile>\<^sub>L params\<^sub>1 \<Rrightarrow> params\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> StaticOperationCall \<tau> op params\<^sub>1 \<Rrightarrow> StaticOperationCall \<tau> op params\<^sub>2"

|OclAnyDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[1] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 DotCall call\<^sub>1 \<Rrightarrow> Call src\<^sub>2 DotCall call\<^sub>2"
|OclAnySafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   OclVoid[?] \<le> \<tau> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 SafeDotCall call\<^sub>1 \<Rrightarrow>
       If (OperationCall src\<^sub>2 DotCall NotEqualOp [NullLiteral])
          (Call src\<^sub>2 DotCall call\<^sub>2)
          NullLiteral"
|OclAnyArrowDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 ArrowCall call\<^sub>1 \<Rrightarrow>
       Call (OperationCall src\<^sub>2 DotCall OclAsSetOp []) ArrowCall call\<^sub>2"

|CollectionArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> _ \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 ArrowCall call\<^sub>1 \<Rrightarrow> Call src\<^sub>2 ArrowCall call\<^sub>2"
|CollectionSafeArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 SafeArrowCall call\<^sub>1 \<Rrightarrow>
    Call (OperationCall src\<^sub>2 ArrowCall ExcludingOp [NullLiteral])
      ArrowCall call\<^sub>2"
|CollectionDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   \<not> OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 DotCall call\<^sub>1 \<Rrightarrow> CollectIteratorCall src\<^sub>2 [it]
          (Call (Var it) DotCall call\<^sub>2)"
|CollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 SafeDotCall call\<^sub>1 \<Rrightarrow>
      CollectIteratorCall (OperationCall src\<^sub>2 ArrowCall ExcludingOp [NullLiteral])
        [it] (Call (Var it) DotCall call\<^sub>2)"

|TypeOperationN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C TypeOperation op ty \<Rrightarrow> TypeOperation op ty"
|AttributeN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Attribute attr \<Rrightarrow> Attribute attr"
|AssociationEndN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C AssociationEnd role \<Rrightarrow> AssociationEnd role"
|OperationN:
  "\<Gamma> \<turnstile>\<^sub>L as \<Rrightarrow> bs \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> Operation op bs"
|TupleElementN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C TupleElement elem \<Rrightarrow> TupleElement elem"

|IterateN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> res_init\<^sub>1 \<Rrightarrow> res_init\<^sub>2 \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile>
      Let res res_t res_init\<^sub>1 body\<^sub>1 \<Rrightarrow> Let res res_t res_init\<^sub>2 body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its res res_t res_init\<^sub>1 body\<^sub>1 \<Rrightarrow>
      Iterate its res res_t res_init\<^sub>2 body\<^sub>2"
|IteratorN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2  \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its body\<^sub>1 \<Rrightarrow> Iterator iter its body\<^sub>2"

|ExprListNilN:
  "\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> []"
|ExprListConsN:
  "\<Gamma> \<turnstile> x \<Rrightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> y # ys"

inductive_cases LiteralNE [elim]: "\<Gamma> \<turnstile> Literal a \<Rrightarrow> b"
inductive_cases LetNE [elim]: "\<Gamma> \<turnstile> Let v t init body \<Rrightarrow> b"
inductive_cases VarNE [elim]: "\<Gamma> \<turnstile> Var v \<Rrightarrow> b"
inductive_cases IfNE [elim]: "\<Gamma> \<turnstile> If a b c \<Rrightarrow> d"
inductive_cases MetaOperationCallNE [elim]: "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> b"
inductive_cases StaticOperationCallNE [elim]: "\<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> b"
inductive_cases DotCallNE [elim]: "\<Gamma> \<turnstile> Call src DotCall call \<Rrightarrow> b"
inductive_cases SafeDotCallNE [elim]: "\<Gamma> \<turnstile> Call src SafeDotCall call \<Rrightarrow> b"
inductive_cases ArrowCallNE [elim]: "\<Gamma> \<turnstile> Call src ArrowCall call \<Rrightarrow> b"
inductive_cases SafeArrowCallNE [elim]: "\<Gamma> \<turnstile> Call src SafeArrowCall call \<Rrightarrow> b"

inductive_cases CallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C call \<Rrightarrow> b"
inductive_cases OperationCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call"
inductive_cases IterateCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its res res_t res_init body \<Rrightarrow> call"
inductive_cases IteratorCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its body \<Rrightarrow> call"

inductive_cases ExprListNilNE [elim]: "\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> zs"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma any_has_not_element_type:
  "element_type \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> OclAny[?] \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type':
  "element_type \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> OclAny[1] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type'':
  "element_type \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type''':
  "element_type \<tau> \<sigma> \<Longrightarrow> OclVoid[?] \<le> \<tau> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma
  normalize_det:
    "\<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> expr\<^sub>1 = expr\<^sub>2" and
  normalize_call_det:
    "\<Gamma>_\<tau> \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>1 \<Longrightarrow> \<Gamma>_\<tau> \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>2 \<Longrightarrow> call\<^sub>1 = call\<^sub>2" and
  normalize_expr_list_det:
    "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> zs \<Longrightarrow> ys = zs"
  for \<Gamma> :: "('a :: ocl_object_model) type env"
  and \<Gamma>_\<tau> :: "('a :: ocl_object_model) type env \<times> 'a type"
proof (induct \<Gamma> expr expr\<^sub>1 and \<Gamma>_\<tau> call call\<^sub>1
       arbitrary: expr\<^sub>2 and call\<^sub>2 and zs
       rule: normalize_normalize_call_normalize_expr_list.inducts)
  case (LiteralN \<Gamma> a) thus ?case by auto
next
  case (LetN \<Gamma> init\<^sub>1 init\<^sub>2 v \<tau> body\<^sub>1 body\<^sub>2) thus ?case by blast
next
  case (VarN \<Gamma> v) thus ?case by auto
next
  case (IfN \<Gamma> a\<^sub>1 a\<^sub>2 b\<^sub>1 b\<^sub>2 c\<^sub>1 c\<^sub>2) thus ?case
    apply (insert IfN.prems)
    apply (erule IfNE)
    by (simp add: IfN.hyps)
next
  case (MetaOperationCallN \<Gamma> \<tau> op) thus ?case by auto
next
  case (StaticOperationCallN \<Gamma> as bs \<tau> op) thus ?case by blast
next
  case (OclAnyDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert OclAnyDotCallN.prems)
    apply (erule DotCallNE)
    using OclAnyDotCallN.hyps typing_det apply metis
    using OclAnyDotCallN.hyps any_has_not_element_type' typing_det by metis
next
  case (OclAnySafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert OclAnySafeDotCallN.prems)
    apply (erule SafeDotCallNE)
    using OclAnySafeDotCallN.hyps typing_det comp_apply
    apply (metis (no_types, lifting) list.simps(8) list.simps(9))
    using OclAnySafeDotCallN.hyps typing_det any_has_not_element_type''' by metis
next
  case (OclAnyArrowDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert OclAnyArrowDotCallN.prems)
    apply (erule ArrowCallNE)
    using OclAnyArrowDotCallN.hyps typing_det comp_apply apply metis
    using OclAnyArrowDotCallN.hyps typing_det any_has_not_element_type'' by metis
next
  case (CollectionArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2 uu) show ?case
    apply (insert CollectionArrowCallN.prems)
    apply (erule ArrowCallNE)
    using CollectionArrowCallN.hyps typing_det any_has_not_element_type'' apply metis
    using CollectionArrowCallN.hyps typing_det by metis
next
  case (CollectionSafeArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2 \<sigma>) show ?case
    apply (insert CollectionSafeArrowCallN.prems)
    apply (erule SafeArrowCallNE)
    using CollectionSafeArrowCallN.hyps typing_det comp_apply
    by (metis (no_types, lifting) list.simps(8) list.simps(9))
next
  case (CollectionDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2 \<sigma> it) show ?case
    apply (insert CollectionDotCallN.prems)
    apply (erule DotCallNE)
    using CollectionDotCallN.hyps typing_det any_has_not_element_type' apply metis
    using CollectionDotCallN.hyps typing_det by metis
next
  case (CollectionSafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2 \<sigma> it) show ?case
    apply (insert CollectionSafeDotCallN.prems)
    apply (erule SafeDotCallNE)
    using CollectionSafeDotCallN.hyps typing_det any_has_not_element_type''' apply metis
    using CollectionSafeDotCallN.hyps typing_det comp_apply
    by (metis (no_types, lifting) list.simps(8) list.simps(9))
next
  case (TypeOperationN \<Gamma> \<tau> op ty) thus ?case by auto
next
  case (AttributeN \<Gamma> \<tau> attr) thus ?case by auto
next
  case (AssociationEndN \<Gamma> \<tau> role) thus ?case by auto
next
  case (OperationN \<Gamma> as bs \<tau> op) show ?case
    apply (insert OperationN.prems)
    apply (erule OperationCallNE)
    by (simp add: OperationN.hyps)
next
  case (TupleElementN \<Gamma> \<tau> elem) thus ?case by auto
next
  case (IterateN \<tau> \<sigma> \<Gamma> res_init\<^sub>1 res_init\<^sub>2 its res res_t body\<^sub>1 body\<^sub>2)
  show ?case
    apply (insert IterateN.prems)
    apply (erule IterateCallNE)
    using IterateN.hyps element_type_det by blast
next
  case (IteratorN \<tau> \<sigma> \<Gamma> its body\<^sub>1 body\<^sub>2 iter)
  show ?case
    apply (insert IteratorN.prems)
    apply (erule IteratorCallNE)
    using IteratorN.hyps element_type_det by blast
next
  case (ExprListNilN \<Gamma>) thus ?case
    using normalize_expr_list.cases by auto
next
  case (ExprListConsN \<Gamma> x y xs ys) thus ?case by blast
qed

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred [show_modes] normalize .

end

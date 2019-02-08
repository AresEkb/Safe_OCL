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
  "\<Gamma> \<turnstile> init1 \<Rrightarrow> init2 \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile> body1 \<Rrightarrow> body2 \<Longrightarrow>
   \<Gamma> \<turnstile> Let v \<tau> init1 body1 \<Rrightarrow> Let v \<tau> init2 body2"
|VarN:
  "\<Gamma> \<turnstile> Var v \<Rrightarrow> Var v"
|IfN:
  "\<Gamma> \<turnstile> a1 \<Rrightarrow> a2 \<Longrightarrow>
   \<Gamma> \<turnstile> b1 \<Rrightarrow> b2 \<Longrightarrow>
   \<Gamma> \<turnstile> c1 \<Rrightarrow> c2 \<Longrightarrow>
   \<Gamma> \<turnstile> If a1 b1 c1 \<Rrightarrow> If a2 b2 c2"

|MetaOperationCallN:
  "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> MetaOperationCall \<tau> op"
|StaticOperationCallN:
  "\<Gamma> \<turnstile>\<^sub>L as \<Rrightarrow> bs \<Longrightarrow>
   \<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> StaticOperationCall \<tau> op bs"

|OclAnyDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[1] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 DotCall call1 \<Rrightarrow> Call src2 DotCall call2"
|OclAnySafeDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   OclVoid[?] \<le> \<tau> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 SafeDotCall call1 \<Rrightarrow>
       If (OperationCall src2 DotCall NotEqualOp [NullLiteral])
          (Call src2 DotCall call2)
          NullLiteral"
|OclAnyArrowDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 ArrowCall call1 \<Rrightarrow>
       Call (OperationCall src2 DotCall OclAsSetOp []) ArrowCall call2"

|CollectionArrowCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   element_type \<tau> _ \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 ArrowCall call1 \<Rrightarrow> Call src2 ArrowCall call2"
|CollectionSafeArrowCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 SafeArrowCall call1 \<Rrightarrow>
    Call (OperationCall src2 ArrowCall ExcludingOp [NullLiteral])
      ArrowCall call2"
|CollectionDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   \<not> OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 DotCall call1 \<Rrightarrow> CollectIteratorCall src2 [it]
          (Call (Var it) DotCall call2)"
|CollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 SafeDotCall call1 \<Rrightarrow>
      CollectIteratorCall (OperationCall src2 ArrowCall ExcludingOp [NullLiteral])
        [it] (Call (Var it) DotCall call2)"

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
   \<Gamma> \<turnstile> res_init1 \<Rrightarrow> res_init2 \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile>
      Let res res_t res_init1 body1 \<Rrightarrow> Let res res_t res_init2 body2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its res res_t res_init1 body1 \<Rrightarrow>
      Iterate its res res_t res_init2 body2"
|IteratorN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile> body1 \<Rrightarrow> body2  \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its body1 \<Rrightarrow> Iterator iter its body2"

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
inductive_cases OperationCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call2"
inductive_cases IterateCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its res res_t res_init1 body1 \<Rrightarrow> call2"
inductive_cases IteratorCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its body1 \<Rrightarrow> call2"

inductive_cases ExprListNilNE [elim]: "\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> zs"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma any_has_not_element_type:
  "\<tau> \<le> OclAny[?] \<Longrightarrow> element_type \<tau> \<sigma> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type':
  "\<tau> \<le> OclAny[1] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow> element_type \<tau> \<sigma> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type'':
  "\<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow> element_type \<tau> \<sigma> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type''':
  "OclVoid[?] \<le> \<tau> \<Longrightarrow> element_type \<tau> \<sigma> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma
  normalize_det: "\<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> expr\<^sub>1 = expr\<^sub>2" and
  normalize_call_det: "\<Gamma>_\<tau> \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>1 \<Longrightarrow> \<Gamma>_\<tau> \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>2 \<Longrightarrow> call\<^sub>1 = call\<^sub>2" and
  normalize_expr_list_det: "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> zs \<Longrightarrow> ys = zs"
  for \<Gamma> :: "('a :: ocl_object_model) type env"
  and \<Gamma>_\<tau> :: "('a :: ocl_object_model) type env \<times> 'a type"
proof (induct \<Gamma> expr expr\<^sub>1 and \<Gamma>_\<tau> call call\<^sub>1
       arbitrary: expr\<^sub>2 and call\<^sub>2 and zs
       rule: normalize_normalize_call_normalize_expr_list.inducts)
  case (LiteralN \<Gamma> a) thus ?case by auto
next
  case (LetN \<Gamma> init1 init2 v \<tau> body1 body2) thus ?case by blast
next
  case (VarN \<Gamma> v) thus ?case by auto
next
  case (IfN \<Gamma> a1 a2 b1 b2 c1 c2) thus ?case
    apply (insert IfN.prems)
    apply (erule IfNE)
    by (simp add: IfN.hyps(2) IfN.hyps(4) IfN.hyps(6))
next
  case (MetaOperationCallN \<Gamma> \<tau> op) thus ?case by auto
next
  case (StaticOperationCallN \<Gamma> as bs \<tau> op) thus ?case by blast
next
  case (OclAnyDotCallN \<Gamma> src1 src2 \<tau> call1 call2) show ?case
    apply (insert OclAnyDotCallN.prems)
    apply (erule DotCallNE)
    apply (metis OclAnyDotCallN.hyps(2) OclAnyDotCallN.hyps(3) OclAnyDotCallN.hyps(6) typing_det)
    by (metis OclAnyDotCallN.hyps(2) OclAnyDotCallN.hyps(3) OclAnyDotCallN.hyps(4) any_has_not_element_type' typing_det)
next
  case (OclAnySafeDotCallN \<Gamma> src1 src2 \<tau> call1 call2) show ?case
    apply (insert OclAnySafeDotCallN.prems)
    apply (erule SafeDotCallNE)
    apply (metis (no_types, lifting) OclAnySafeDotCallN.hyps(2) OclAnySafeDotCallN.hyps(3) OclAnySafeDotCallN.hyps(6) comp_apply list.simps(8) list.simps(9) typing_det)
    by (metis OclAnySafeDotCallN.hyps(2) OclAnySafeDotCallN.hyps(3) OclAnySafeDotCallN.hyps(4) any_has_not_element_type''' typing_det)
next
  case (OclAnyArrowDotCallN \<Gamma> src1 src2 \<tau> call1 call2) show ?case
    apply (insert OclAnyArrowDotCallN.prems)
    apply (erule ArrowCallNE)
    apply (metis OclAnyArrowDotCallN.hyps(2) OclAnyArrowDotCallN.hyps(3) OclAnyArrowDotCallN.hyps(6) comp_apply typing_det)
    by (metis OclAnyArrowDotCallN.hyps(2) OclAnyArrowDotCallN.hyps(3) OclAnyArrowDotCallN.hyps(4) any_has_not_element_type'' typing_det)
next
  case (CollectionArrowCallN \<Gamma> src1 src2 \<tau> call1 call2 uu) show ?case
    apply (insert CollectionArrowCallN.prems)
    apply (erule ArrowCallNE)
    apply (metis CollectionArrowCallN.hyps(2) CollectionArrowCallN.hyps(3) CollectionArrowCallN.hyps(4) any_has_not_element_type'' typing_det)
    using CollectionArrowCallN.hyps(2) CollectionArrowCallN.hyps(3) CollectionArrowCallN.hyps(6) typing_det by fastforce
next
  case (CollectionSafeArrowCallN \<Gamma> src1 src2 \<tau> call1 call2 \<sigma>) show ?case
    apply (insert CollectionSafeArrowCallN.prems)
    apply (erule SafeArrowCallNE)
    by (smt CollectionSafeArrowCallN.hyps(2) CollectionSafeArrowCallN.hyps(3) CollectionSafeArrowCallN.hyps(7) comp_assoc comp_eq_dest_lhs list.simps(8) list.simps(9) typing_det)
next
  case (CollectionDotCallN \<Gamma> src1 src2 \<tau> call1 call2 \<sigma> it) show ?case
    apply (insert CollectionDotCallN.prems)
    apply (erule DotCallNE)
    apply (metis CollectionDotCallN.hyps(2) CollectionDotCallN.hyps(3) CollectionDotCallN.hyps(4) any_has_not_element_type' typing_det)
    using CollectionDotCallN.hyps(2) CollectionDotCallN.hyps(3) CollectionDotCallN.hyps(7) CollectionDotCallN.hyps(8) typing_det by fastforce
next
  case (CollectionSafeDotCallN \<Gamma> src1 src2 \<tau> call1 call2 \<sigma> it) show ?case
    apply (insert CollectionSafeDotCallN.prems)
    apply (erule SafeDotCallNE)
    apply (metis CollectionSafeDotCallN.hyps(2) CollectionSafeDotCallN.hyps(3) CollectionSafeDotCallN.hyps(4) any_has_not_element_type''' typing_det)
    by (metis (no_types, lifting) CollectionSafeDotCallN.hyps(2) CollectionSafeDotCallN.hyps(3) CollectionSafeDotCallN.hyps(7) CollectionSafeDotCallN.hyps(8) comp_apply list.simps(8) list.simps(9) typing_det)
next
  case (TypeOperationN \<Gamma> \<tau> op ty) thus ?case by auto
next
  case (IterateN \<tau> \<sigma> \<Gamma> res_init1 res_init2 its res res_t body1 body2)
  show ?case
    apply (insert IterateN.prems)
    apply (erule IterateCallNE)
    using IterateN.hyps(1) IterateN.hyps(5) element_type_det by blast
next
  case (IteratorN \<tau> \<sigma> \<Gamma> its body1 body2 iter)
  show ?case
    apply (insert IteratorN.prems)
    apply (erule IteratorCallNE)
    using IteratorN.hyps(1) IteratorN.hyps(3) element_type_det by auto
next
  case (AttributeN \<Gamma> \<tau> attr) thus ?case by auto
next
  case (AssociationEndN \<Gamma> \<tau> role) thus ?case by auto
next
  case (OperationN \<Gamma> as bs \<tau> op) show ?case
    apply (insert OperationN.prems)
    apply (erule OperationCallNE)
    by (simp add: OperationN.hyps(2))
next
  case (TupleElementN \<Gamma> \<tau> elem) thus ?case by auto
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

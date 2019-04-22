(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Normalization\<close>
theory OCL_Normalization
  imports OCL_Typing
begin

(*** Normalization Rules ****************************************************)

section \<open>Normalization Rules\<close>

text \<open>
  The following expression normalization rules includes two kinds of an
  abstract syntax tree transformations:
\begin{itemize}
\item determination of implicit types of variables, iterators, and
      tuple elements,
\item unfolding of navigation shorthands and safe navigation operators,
      described in \autoref{tab:norm_rules}.
\end{itemize}

  The following variables are used in the table:
\begin{itemize}
\item \<^verbatim>\<open>x\<close> is a non-nullable value,
\item \<^verbatim>\<open>n\<close> is a nullable value,
\item \<^verbatim>\<open>xs\<close> is a collection of non-nullable values,
\item \<^verbatim>\<open>ns\<close> is a collection of nullable values. 
\end{itemize}

\begin{table}[h!]
  \begin{center}
    \caption{Expression Normalization Rules}
    \label{tab:norm_rules}
    \begin{threeparttable}
    \begin{tabular}{c|c}
      \textbf{Orig. expr.} & \textbf{Normalized expression}\\
      \hline
      \<^verbatim>\<open>x.op()\<close> & \<^verbatim>\<open>x.op()\<close>\\
      \<^verbatim>\<open>n.op()\<close> & \<^verbatim>\<open>n.op()\<close>\tnote{*}\\
      \<^verbatim>\<open>x?.op()\<close> & ---\\
      \<^verbatim>\<open>n?.op()\<close> & \<^verbatim>\<open>if n <> null then n.oclAsType(T[1]).op() else null endif\<close>\tnote{**}\\
      \<^verbatim>\<open>x->op()\<close> & \<^verbatim>\<open>x.oclAsSet()->op()\<close>\\
      \<^verbatim>\<open>n->op()\<close> & \<^verbatim>\<open>n.oclAsSet()->op()\<close>\\
      \<^verbatim>\<open>x?->op()\<close> & ---\\
      \<^verbatim>\<open>n?->op()\<close> & ---\\
      \hline
      \<^verbatim>\<open>xs.op()\<close> & \<^verbatim>\<open>xs->collect(x | x.op())\<close>\\
      \<^verbatim>\<open>ns.op()\<close> & \<^verbatim>\<open>ns->collect(n | n.op())\<close>\tnote{*}\\
      \<^verbatim>\<open>xs?.op()\<close> & ---\\
      \<^verbatim>\<open>ns?.op()\<close> & \<^verbatim>\<open>ns->selectByKind(T[1])->collect(x | x.op())\<close>\\
      \<^verbatim>\<open>xs->op()\<close> & \<^verbatim>\<open>xs->op()\<close>\\
      \<^verbatim>\<open>ns->op()\<close> & \<^verbatim>\<open>ns->op()\<close>\\
      \<^verbatim>\<open>xs?->op()\<close> & ---\\
      \<^verbatim>\<open>ns?->op()\<close> & \<^verbatim>\<open>ns->selectByKind(T[1])->op()\<close>\\
    \end{tabular}
    \begin{tablenotes}
    \item[*] The resulting expression will be ill-typed if the operation is unsafe.
    An unsafe operation is an operation which is well-typed for
    a non-nullable source only.
    \item[**] It would be a good idea to prohibit such a transformation
    for safe operations. A safe operation is an operation which is well-typed
    for a nullable source. However, it is hard to define safe operations
    formally considering operations overloading, complex relations between
    operation parameters types (please see the typing rules for the equality
    operator), and user-defined operations.
    \end{tablenotes}
    \end{threeparttable}
  \end{center}
\end{table}

  Please take a note that name resolution of variables, types,
  attributes, and associations is out of scope of this section.
  It should be done on a previous phase during transformation
  of a concrete syntax tree to an abstract syntax tree.\<close>

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)]
      else string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition "new_vname \<equiv> String.implode \<circ> string_of_nat \<circ> fcard \<circ> fmdom"

inductive normalize_closure_body ("_ \<turnstile>\<^sub>B _ \<Rrightarrow>/ _" [51,51,51] 50) where
 SingleClosureBodyN:
  "\<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> NonCollection()[_] \<Longrightarrow>
   (\<Gamma>, _) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>1\<^bold>.oclAsSet()"
|CollectionClosureBodyN:
  "\<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection(\<sigma>)[_] \<Longrightarrow>
   (\<Gamma>, ArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>1"
|NullFreeNullFreeClosureBodyN:
  "\<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   required_type \<sigma> \<Longrightarrow>
   (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>1"
|NullFreeNullableClosureBodyN:
  "\<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection(\<sigma>)[1] \<Longrightarrow>
   optional_type \<sigma> \<Longrightarrow>
   (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>1->selectByKind(to_required_type \<sigma>)"
|NullableNullFreeClosureBodyN:
  "\<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[?] \<Longrightarrow>
   required_type \<sigma> \<Longrightarrow>
   (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow>
      if body\<^sub>1 <> null
      then body\<^sub>1\<^bold>.oclAsType(to_required_type \<tau>)
      else CollectionLiteral k [] endif"
|NullableNullableClosureBodyN:
  "\<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Collection\<^bsub>k\<^esub>(\<sigma>)[?] \<Longrightarrow>
   optional_type \<sigma> \<Longrightarrow>
   (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow>
      if body\<^sub>1 <> null
      then body\<^sub>1\<^bold>.oclAsType(to_required_type \<tau>)->selectByKind(to_required_type \<sigma>)
      else CollectionLiteral k [] endif"

inductive normalize
    :: "('a :: ocl_object_model) type\<^sub>N\<^sub>E env \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> bool"
    ("_ \<turnstile> _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_call ("_ \<turnstile>\<^sub>C _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_loop ("_ \<turnstile>\<^sub>I _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_expr_list ("_ \<turnstile>\<^sub>L _ \<Rrightarrow>/ _" [51,51,51] 50)
    where
 LiteralN:
  "\<Gamma> \<turnstile> Literal a \<Rrightarrow> Literal a"
|ExplicitlyTypedLetN:
  "\<Gamma> \<turnstile> init\<^sub>1 \<Rrightarrow> init\<^sub>2 \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> let v : \<tau> = init\<^sub>1 in body\<^sub>1 \<Rrightarrow> let v : \<tau> = init\<^sub>2 in body\<^sub>2"
|ImplicitlyTypedLetN:
  "\<Gamma> \<turnstile> init\<^sub>1 \<Rrightarrow> init\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E init\<^sub>2 : \<tau> \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> let v = init\<^sub>1 in body\<^sub>1 \<Rrightarrow> let v : \<tau> = init\<^sub>2 in body\<^sub>2"
|VarN:
  "\<Gamma> \<turnstile> Var v \<Rrightarrow> Var v"
|IfN:
  "\<Gamma> \<turnstile> cnd\<^sub>1 \<Rrightarrow> cnd\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> thn\<^sub>1 \<Rrightarrow> thn\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> els\<^sub>1 \<Rrightarrow> els\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> if cnd\<^sub>1 then thn\<^sub>1 else els\<^sub>1 endif \<Rrightarrow> if cnd\<^sub>2 then thn\<^sub>2 else els\<^sub>2 endif"

|MetaOperationCallN:
  "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> MetaOperationCall \<tau> op"
|StaticOperationCallN:
  "\<Gamma> \<turnstile>\<^sub>L params\<^sub>1 \<Rrightarrow> params\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> StaticOperationCall \<tau> op params\<^sub>1 \<Rrightarrow> StaticOperationCall \<tau> op params\<^sub>2"

|SingleDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> NonIterable()[_] \<Longrightarrow>
   (\<Gamma>, \<tau>, DotCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1\<^bold>.call\<^sub>1 \<Rrightarrow> src\<^sub>2\<^bold>.call\<^sub>2"
|SingleSafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> NonIterable()[?] \<Longrightarrow>
   (\<Gamma>, to_required_type \<tau>, SafeDotCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow>
      if src\<^sub>2 <> null
      then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)\<^bold>.call\<^sub>2
      else null endif"
|SingleArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> NonIterable()[_] \<Longrightarrow>
   src\<^sub>3 = src\<^sub>2\<^bold>.oclAsSet() \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>3 : \<sigma> \<Longrightarrow>
   (\<Gamma>, \<sigma>, ArrowCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1->call\<^sub>1 \<Rrightarrow> src\<^sub>3->call\<^sub>2"

|CollectionDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[1] \<Longrightarrow>
   (\<Gamma>, \<sigma>, DotCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1\<^bold>.call\<^sub>1 \<Rrightarrow> src\<^sub>2->collect(it : \<sigma> | \<lparr>it\<rparr>\<^bold>.call\<^sub>2)"
|CollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[1] \<Longrightarrow>
   optional_type \<sigma> \<Longrightarrow>
   \<rho> = to_required_type \<sigma> \<Longrightarrow>
   (\<Gamma>, \<rho>, SafeDotCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow> src\<^sub>2->selectByKind(\<rho>)->collect(it : \<rho> | \<lparr>it\<rparr>\<^bold>.call\<^sub>2)"
|CollectionArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(_)[_] \<Longrightarrow>
   (\<Gamma>, \<tau>, ArrowCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1->call\<^sub>1 \<Rrightarrow> src\<^sub>2->call\<^sub>2"
|CollectionSafeArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[1] \<Longrightarrow>
   optional_type \<sigma> \<Longrightarrow>
   src\<^sub>3 = src\<^sub>2->selectByKind(to_required_type \<sigma>) \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>3 : \<rho> \<Longrightarrow>
   (\<Gamma>, \<rho>, SafeArrowCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?->call\<^sub>1 \<Rrightarrow> src\<^sub>3->call\<^sub>2"

|NullableCollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[?] \<Longrightarrow>
   required_type \<sigma> \<Longrightarrow>
   (\<Gamma>, \<sigma>, SafeDotCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow>
      if src\<^sub>2 <> null
      then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->collect(it : \<sigma> | \<lparr>it\<rparr>\<^bold>.call\<^sub>2)
      else null endif"
|NullableNullableCollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[?] \<Longrightarrow>
   optional_type \<sigma> \<Longrightarrow>
   \<rho> = to_required_type \<sigma> \<Longrightarrow>
   (\<Gamma>, \<rho>, SafeDotCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow>
      if src\<^sub>2 <> null
      then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->selectByKind(\<rho>)->
                  collect(it : \<rho> | \<lparr>it\<rparr>\<^bold>.call\<^sub>2)
      else null endif"
|NullableCollectionSafeArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[?] \<Longrightarrow>
   required_type \<sigma> \<Longrightarrow>
   (\<Gamma>, to_required_type \<tau>, SafeArrowCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?->call\<^sub>1 \<Rrightarrow>
      if src\<^sub>2 <> null
      then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->call\<^sub>2
      else null endif"
|NullableNullableCollectionSafeArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<hookrightarrow> Iterable(\<sigma>)[?] \<Longrightarrow>
   optional_type \<sigma> \<Longrightarrow>
   src\<^sub>3 = src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->selectByKind(to_required_type \<sigma>) \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>3 : \<rho> \<Longrightarrow>
   (\<Gamma>, \<rho>, SafeArrowCall) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> src\<^sub>1?->call\<^sub>1 \<Rrightarrow>
      if src\<^sub>2 <> null
      then src\<^sub>3->call\<^sub>2
      else null endif"

|TypeOperationN:
  "(\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C TypeOperation op ty \<Rrightarrow> TypeOperation op ty"
|AttributeN:
  "(\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Attribute attr \<Rrightarrow> Attribute attr"
|AssociationEndN:
  "(\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C AssociationEnd role from \<Rrightarrow> AssociationEnd role from"
|AssociationClassN:
  "(\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C AssociationClass \<A> from \<Rrightarrow> AssociationClass \<A> from"
|AssociationClassEndN:
  "(\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C AssociationClassEnd role \<Rrightarrow> AssociationClassEnd role"
|OperationN:
  "\<Gamma> \<turnstile>\<^sub>L params\<^sub>1 \<Rrightarrow> params\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Operation op params\<^sub>1 \<Rrightarrow> Operation op params\<^sub>2"
|TupleElementN:
  "(\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C TupleElement elem \<Rrightarrow> TupleElement elem"

|IterateN:
  "\<Gamma> \<turnstile> res_init\<^sub>1 \<Rrightarrow> res_init\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, its_ty\<^sub>1, Let res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1) \<Rrightarrow>
      (its, its_ty\<^sub>2, Let res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2) \<Longrightarrow>
   (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Iterate its its_ty\<^sub>1 res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1 \<Rrightarrow>
      Iterate its its_ty\<^sub>2 res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2"
|ClosureIterationN:
  "iter = ClosureIter \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, its_ty\<^sub>1, body\<^sub>1) \<Rrightarrow> (its, its_ty\<^sub>2, body\<^sub>2) \<Longrightarrow>
   its_ty\<^sub>2 = (Some \<sigma>, None) \<Longrightarrow>
   (\<Gamma> ++\<^sub>f iterators its \<sigma>, k) \<turnstile>\<^sub>B body\<^sub>2 \<Rrightarrow> body\<^sub>3 \<Longrightarrow>
   (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Iterator iter its its_ty\<^sub>1 body\<^sub>1 \<Rrightarrow> Iterator iter its its_ty\<^sub>2 body\<^sub>3"
|IterationN:
  "iter \<noteq> ClosureIter \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, its_ty\<^sub>1, body\<^sub>1) \<Rrightarrow> (its, its_ty\<^sub>2, body\<^sub>2) \<Longrightarrow>
   (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Iterator iter its its_ty\<^sub>1 body\<^sub>1 \<Rrightarrow> Iterator iter its its_ty\<^sub>2 body\<^sub>2"

|ExplicitlyTypedCollectionLoopN:
  "\<tau> \<hookrightarrow> Collection(_)[_] \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its \<sigma> \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<sigma>, None), body\<^sub>1) \<Rrightarrow> (its, (Some \<sigma>, None), body\<^sub>2)"
|ImplicitlyTypedCollectionLoopN:
  "\<tau> \<hookrightarrow> Collection(\<sigma>)[_] \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its \<sigma> \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, None), body\<^sub>1) \<Rrightarrow> (its, (Some \<sigma>, None), body\<^sub>2)"

|ExplicitlyTypedMapLoopN:
  "\<tau> \<hookrightarrow> Map(_, _)[_] \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its \<sigma> ++\<^sub>f coiterators its \<rho> \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<sigma>, Some \<rho>), body\<^sub>1) \<Rrightarrow> (its, (Some \<sigma>, Some \<rho>), body\<^sub>2)"
|ImplicitlyTypedMapKeyLoopN:
  "\<tau> \<hookrightarrow> Map(\<sigma>, _)[_] \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its \<sigma> ++\<^sub>f coiterators its \<rho> \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, Some \<rho>), body\<^sub>1) \<Rrightarrow> (its, (Some \<sigma>, Some \<rho>), body\<^sub>2)"
|ImplicitlyTypedMapValueLoopN:
  "\<tau> \<hookrightarrow> Map(_, \<rho>)[_] \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its \<sigma> ++\<^sub>f coiterators its \<rho> \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<sigma>, None), body\<^sub>1) \<Rrightarrow> (its, (Some \<sigma>, Some \<rho>), body\<^sub>2)"
|ImplicitlyTypedMapLoopN:
  "\<tau> \<hookrightarrow> Map(\<sigma>, \<rho>)[_] \<Longrightarrow>
   \<Gamma> ++\<^sub>f iterators its \<sigma> ++\<^sub>f coiterators its \<rho> \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, None), body\<^sub>1) \<Rrightarrow> (its, (Some \<sigma>, Some \<rho>), body\<^sub>2)"

|ExprListNilN:
  "\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> []"
|ExprListConsN:
  "\<Gamma> \<turnstile> x \<Rrightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> y # ys"

(*** Elimination Rules ******************************************************)

section \<open>Elimination Rules\<close>

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
inductive_cases IterateCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its its_ty res res_t res_init body \<Rrightarrow> call"
inductive_cases IterationCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its its_ty body \<Rrightarrow> call"

inductive_cases LoopNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, its_ty, body) \<Rrightarrow> b"

inductive_cases ClosureBodyNE [elim]: "(\<Gamma>, k) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2"

inductive_cases ExprListNE [elim]: "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys"

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>

inductive_simps normalize_closure_body_alt_simps:
"(\<Gamma>, DotCall) \<turnstile>\<^sub>B a \<Rrightarrow> b"
"(\<Gamma>, SafeDotCall) \<turnstile>\<^sub>B a \<Rrightarrow> b"
"(\<Gamma>, ArrowCall) \<turnstile>\<^sub>B a \<Rrightarrow> b"
"(\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B a \<Rrightarrow> b"

inductive_simps normalize_alt_simps:
"\<Gamma> \<turnstile> Literal a \<Rrightarrow> b"
"\<Gamma> \<turnstile> Let v t init body \<Rrightarrow> b"
"\<Gamma> \<turnstile> Var v \<Rrightarrow> b"
"\<Gamma> \<turnstile> If a b c \<Rrightarrow> d"

"\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> b"
"\<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src DotCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src SafeDotCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src ArrowCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src SafeArrowCall call \<Rrightarrow> b"

"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C call \<Rrightarrow> b"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its its_ty res res_t res_init body \<Rrightarrow> call"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its its_ty body \<Rrightarrow> call"

"(\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, None), body) \<Rrightarrow> b"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<tau>, None), body) \<Rrightarrow> b"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, Some \<sigma>), body) \<Rrightarrow> b"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<tau>, Some \<sigma>), body) \<Rrightarrow> b"

"\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> ys"
"\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> ys"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma normalize_closure_body_det:
  "\<Gamma>_k \<turnstile>\<^sub>B body \<Rrightarrow> body\<^sub>1 \<Longrightarrow>
   \<Gamma>_k \<turnstile>\<^sub>B body \<Rrightarrow> body\<^sub>2 \<Longrightarrow> body\<^sub>1 = body\<^sub>2"
proof (induct rule: normalize_closure_body.inducts)
  case (SingleClosureBodyN \<Gamma> body\<^sub>1 \<tau> uu k)
  have "\<And>body\<^sub>2. (\<Gamma>, k) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
        body\<^sub>1\<^bold>.oclAsSet() = body\<^sub>2"
    apply (erule ClosureBodyNE)
    apply simp
    using SingleClosureBodyN.hyps(1) SingleClosureBodyN.hyps(2)
          collection_type_non_collection_type_distinct
          is_collection_type.intros typing_det by blast+
  thus ?case by (simp add: SingleClosureBodyN.prems)
next
  case (CollectionClosureBodyN \<Gamma> body\<^sub>1 \<tau> \<sigma> n)
  have "\<And>body\<^sub>2. (\<Gamma>, ArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
        body\<^sub>1 = body\<^sub>2"
    apply (erule ClosureBodyNE)
    using CollectionClosureBodyN.hyps is_collection_type.intros
          collection_type_non_collection_type_distinct
          typing_det by blast+
  thus ?case by (simp add: CollectionClosureBodyN.prems)
next
  case (NullFreeNullFreeClosureBodyN \<Gamma> body\<^sub>1 \<tau> \<sigma>)
  have "\<And>body\<^sub>2. (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
        body\<^sub>1 = body\<^sub>2"
    apply (erule ClosureBodyNE)
    using NullFreeNullFreeClosureBodyN.hyps typing_det
          collection_type_non_collection_type_distinct apply blast
    using NullFreeNullFreeClosureBodyN.hyps typing_det
          collection_type_non_collection_type_distinct apply blast
    using NullFreeNullFreeClosureBodyN.hyps typing_det
          collection_type_non_collection_type_distinct apply blast
    using NullFreeNullFreeClosureBodyN.hyps
          any_collection_type_det typing_det apply blast
    by (metis NullFreeNullFreeClosureBodyN.hyps(1)
              NullFreeNullFreeClosureBodyN.hyps(2)
              any_collection_type.cases collection_type_det(1) typing_det)+
  thus ?case by (simp add: NullFreeNullFreeClosureBodyN.prems)
next
  case (NullFreeNullableClosureBodyN \<Gamma> body\<^sub>1 \<tau> \<sigma>)
  have "\<And>body\<^sub>2. (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
        body\<^sub>1->selectByKind(to_required_type \<sigma>) = body\<^sub>2"
    apply (erule ClosureBodyNE)
    using NullFreeNullableClosureBodyN.hyps typing_det
          collection_type_non_collection_type_distinct apply blast
    apply simp
    using NullFreeNullableClosureBodyN.hyps typing_det
          any_collection_type_det apply blast
    using NullFreeNullableClosureBodyN.hyps typing_det
          any_collection_type_det apply blast
    by (metis NullFreeNullableClosureBodyN.hyps(1)
              NullFreeNullableClosureBodyN.hyps(2)
              any_collection_type.cases collection_type_det(1) typing_det)+
  thus ?case by (simp add: NullFreeNullableClosureBodyN.prems)
next
  case (NullableNullFreeClosureBodyN \<Gamma> body\<^sub>1 \<tau> k \<sigma>)
  have body_type_det: "\<And>\<tau>'. \<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau>' \<Longrightarrow> \<tau>' = \<tau>"
    by (simp add: NullableNullFreeClosureBodyN.hyps(1) typing_det)
  have "\<And>body\<^sub>2. (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
        if body\<^sub>1 <> null
        then body\<^sub>1\<^bold>.oclAsType(to_required_type \<tau>)
        else CollectionLiteral k [] endif = body\<^sub>2"
    apply (erule ClosureBodyNE)
    using NullableNullFreeClosureBodyN.hyps(2) body_type_det
          is_collection_type.intros apply blast
    apply simp
    apply (metis NullableNullFreeClosureBodyN.hyps(2) body_type_det
                 any_collection_type.cases collection_type_det(1))
    using NullableNullFreeClosureBodyN.hyps(2) body_type_det
          any_collection_type.simps collection_type_det(1) apply blast
    using NullableNullFreeClosureBodyN.hyps(2) body_type_det
          collection_type_det(1) apply fastforce
    using NullableNullFreeClosureBodyN.hyps(2)
          NullableNullFreeClosureBodyN.hyps(3)
          body_type_det collection_type_det(1) by blast
  thus ?case by (simp add: NullableNullFreeClosureBodyN.prems)
next
  case (NullableNullableClosureBodyN \<Gamma> body\<^sub>1 \<tau> k \<sigma>)
  have body_type_det: "\<And>\<tau>'. \<Gamma> \<turnstile>\<^sub>E body\<^sub>1 : \<tau>' \<Longrightarrow> \<tau>' = \<tau>"
    by (simp add: NullableNullableClosureBodyN.hyps(1) typing_det)
  have "\<And>body\<^sub>2. (\<Gamma>, SafeArrowCall) \<turnstile>\<^sub>B body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
        if body\<^sub>1 <> null
        then body\<^sub>1\<^bold>.oclAsType(to_required_type \<tau>)->selectByKind(to_required_type \<sigma>)
        else CollectionLiteral k [] endif = body\<^sub>2"
    apply (erule ClosureBodyNE)
    using NullableNullableClosureBodyN.hyps(2) body_type_det
          is_collection_type.intros apply blast
    apply simp
    using NullableNullableClosureBodyN.hyps(2) body_type_det
          any_collection_type.simps collection_type_det(1) apply blast
    using NullableNullableClosureBodyN.hyps(2) body_type_det
          any_collection_type.simps collection_type_det(1) apply blast
    using NullableNullableClosureBodyN.hyps(2)
          NullableNullableClosureBodyN.hyps(3) body_type_det
          collection_type_det(1) apply blast
    using NullableNullableClosureBodyN.hyps(2) body_type_det
          collection_type_det(1) by fastforce
  thus ?case by (simp add: NullableNullableClosureBodyN.prems)
qed

lemma
  normalize_det:
    "\<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>1 \<Longrightarrow>
     \<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> expr\<^sub>1 = expr\<^sub>2" and
  normalize_call_det:
    "\<Gamma>_\<tau>_k \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>1 \<Longrightarrow>
     \<Gamma>_\<tau>_k \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>2 \<Longrightarrow> call\<^sub>1 = call\<^sub>2" and
  normalize_loop_det:
    "\<Gamma>_\<tau> \<turnstile>\<^sub>I (its, its_ty, body) \<Rrightarrow> ms \<Longrightarrow>
     \<Gamma>_\<tau> \<turnstile>\<^sub>I (its, its_ty, body) \<Rrightarrow> ns \<Longrightarrow> ms = ns" and
  normalize_expr_list_det:
    "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> zs \<Longrightarrow> ys = zs"
  for \<Gamma> :: "('a :: ocl_object_model) type\<^sub>N\<^sub>E env"
  and \<Gamma>_\<tau> :: "('a :: ocl_object_model) type\<^sub>N\<^sub>E env \<times> 'a type\<^sub>N\<^sub>E"
  and \<Gamma>_\<tau>_k :: "('a :: ocl_object_model) type\<^sub>N\<^sub>E env \<times> 'a type\<^sub>N\<^sub>E \<times> call_kind"
  and \<Gamma>_k :: "('a :: ocl_object_model) type\<^sub>N\<^sub>E env \<times> call_kind"
proof (induct arbitrary: expr\<^sub>2 and call\<^sub>2 and ns and zs
       rule: normalize_normalize_call_normalize_loop_normalize_expr_list.inducts)
  case (LiteralN \<Gamma> a) thus ?case by auto
next
  case (ExplicitlyTypedLetN \<Gamma> init\<^sub>1 init\<^sub>2 v \<tau> body\<^sub>1 body\<^sub>2) thus ?case by blast
next
  case (ImplicitlyTypedLetN \<Gamma> init\<^sub>1 init\<^sub>2 \<tau> v body\<^sub>1 body\<^sub>2)
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> let v = init\<^sub>1 in body\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        let v : \<tau> = init\<^sub>2 in body\<^sub>2 = expr\<^sub>2"
    apply (erule LetNE)
    using ImplicitlyTypedLetN.hyps typing_det by blast+
  thus ?case by (simp add: ImplicitlyTypedLetN.prems)
next
  case (VarN \<Gamma> v) thus ?case by auto
next
  case (IfN \<Gamma> cnd\<^sub>1 cnd\<^sub>2 thn\<^sub>1 thn\<^sub>2 els\<^sub>1 els\<^sub>2)
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> if cnd\<^sub>1 then thn\<^sub>1 else els\<^sub>1 endif \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
          if cnd\<^sub>2 then thn\<^sub>2 else els\<^sub>2 endif = expr\<^sub>2"
    by (erule IfNE; simp add: IfN.hyps)
  thus ?case by (simp add: IfN.prems)
next
  case (MetaOperationCallN \<Gamma> \<tau> op) thus ?case by auto
next
  case (StaticOperationCallN \<Gamma> params\<^sub>1 params\<^sub>2 \<tau> op)
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> StaticOperationCall \<tau> op params\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
          StaticOperationCall \<tau> op params\<^sub>2 = expr\<^sub>2"
    by (erule StaticOperationCallNE; simp add: StaticOperationCallN.hyps)
  thus ?case by (simp add: StaticOperationCallN.prems)
next
  case (SingleDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> uu call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using SingleDotCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1\<^bold>.call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> src\<^sub>2\<^bold>.call\<^sub>2 = expr\<^sub>2"
    apply (erule DotCallNE)
    apply (simp add: SingleDotCallN.hyps(2) SingleDotCallN.hyps(6) src_type_det)
    using SingleDotCallN.hyps(4) is_iterable_type.intros src_type_det by blast
  thus ?case by (simp add: SingleDotCallN.prems)
next
  case (SingleSafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using SingleSafeDotCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
      if src\<^sub>2 <> null
      then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)\<^bold>.call\<^sub>2
      else null endif = expr\<^sub>2"
    apply (erule SafeDotCallNE)
    apply (simp add: SingleSafeDotCallN.hyps(2) SingleSafeDotCallN.hyps(6) src_type_det)
    using SingleSafeDotCallN.hyps(4) is_iterable_type.intros src_type_det by blast+
  thus ?case by (simp add: SingleSafeDotCallN.prems)
next
  case (SingleArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> uv src\<^sub>3 \<sigma> call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using SingleArrowCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1->call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> src\<^sub>3->call\<^sub>2 = expr\<^sub>2"
    apply (erule ArrowCallNE)
    apply (metis SingleArrowCallN.hyps(2) SingleArrowCallN.hyps(5)
          SingleArrowCallN.hyps(6) SingleArrowCallN.hyps(8) comp_apply typing_det)
    using SingleArrowCallN.hyps(4) is_iterable_type.intros src_type_det by blast
  thus ?case by (simp add: SingleArrowCallN.prems)
next
  case (CollectionDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> call\<^sub>1 call\<^sub>2 it)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using CollectionDotCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1\<^bold>.call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        src\<^sub>2->collect(it : \<sigma> | (Var it)\<^bold>.call\<^sub>2) = expr\<^sub>2"
    apply (erule DotCallNE)
    using CollectionDotCallN.hyps(4) is_iterable_type.intros
          src_type_det apply blast
    using CollectionDotCallN.hyps(2) CollectionDotCallN.hyps(4)
          CollectionDotCallN.hyps(6) CollectionDotCallN.hyps(7)
          iterable_type_det src_type_det by fastforce
  thus ?case by (simp add: CollectionDotCallN.prems)
next
  case (CollectionSafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> \<rho> call\<^sub>1 call\<^sub>2 it)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using CollectionSafeDotCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        src\<^sub>2->selectByKind(\<rho>)->collect(it : \<rho> | (Var it)\<^bold>.call\<^sub>2) = expr\<^sub>2"
    apply (erule SafeDotCallNE)
    using CollectionSafeDotCallN.hyps(4) is_iterable_type.intros
          src_type_det apply blast
    using CollectionSafeDotCallN.hyps(2) CollectionSafeDotCallN.hyps(4)
          CollectionSafeDotCallN.hyps(6) CollectionSafeDotCallN.hyps(8)
          CollectionSafeDotCallN.hyps(9) iterable_type_det src_type_det
          apply fastforce
    using CollectionSafeDotCallN.hyps(4) iterable_type_det src_type_det by blast+
  thus ?case by (simp add: CollectionSafeDotCallN.prems)
next
  case (CollectionArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> uu uv call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using CollectionArrowCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1->call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> src\<^sub>2->call\<^sub>2 = expr\<^sub>2"
    apply (erule ArrowCallNE)
    using CollectionArrowCallN.hyps(4) is_iterable_type.intros
          src_type_det apply auto[1]
    using CollectionArrowCallN.hyps(2) CollectionArrowCallN.hyps(4)
          CollectionArrowCallN.hyps(6) is_iterable_type.intros
          src_type_det by auto
  thus ?case by (simp add: CollectionArrowCallN.prems)
next
  case (CollectionSafeArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> src\<^sub>3 \<rho> call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using CollectionSafeArrowCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?->call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> src\<^sub>3->call\<^sub>2 = expr\<^sub>2"
    apply (erule SafeArrowCallNE)
    apply (metis CollectionSafeArrowCallN.hyps(2)
           CollectionSafeArrowCallN.hyps(4) CollectionSafeArrowCallN.hyps(6)
           CollectionSafeArrowCallN.hyps(7) CollectionSafeArrowCallN.hyps(9)
           iterable_type_det src_type_det typing_det)
    using CollectionSafeArrowCallN.hyps(4) iterable_type_det src_type_det by blast+
  thus ?case by (simp add: CollectionSafeArrowCallN.prems)
next
  case (NullableCollectionSafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> call\<^sub>1 call\<^sub>2 it)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using NullableCollectionSafeDotCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        if src\<^sub>2 <> null
        then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->collect(it : \<sigma> | \<lparr>it\<rparr>\<^bold>.call\<^sub>2)
        else null endif = expr\<^sub>2"
    apply (erule SafeDotCallNE)
    using NullableCollectionSafeDotCallN.hyps(4) is_iterable_type.intros
          src_type_det apply blast
    using NullableCollectionSafeDotCallN.hyps(4) iterable_type_det
          src_type_det apply blast
    using NullableCollectionSafeDotCallN.hyps(2)
          NullableCollectionSafeDotCallN.hyps(4)
          NullableCollectionSafeDotCallN.hyps(7)
          NullableCollectionSafeDotCallN.hyps(8)
          iterable_type_det src_type_det apply fastforce
    using NullableCollectionSafeDotCallN.hyps(4)
          NullableCollectionSafeDotCallN.hyps(5)
          iterable_type_det src_type_det by blast
  thus ?case by (simp add: NullableCollectionSafeDotCallN.prems)
next
  case (NullableNullableCollectionSafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> \<rho> call\<^sub>1 call\<^sub>2 it)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using NullableNullableCollectionSafeDotCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?.call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        if src\<^sub>2 <> null
        then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->selectByKind(\<rho>)->
                    collect(it : \<rho> | \<lparr>it\<rparr>\<^bold>.call\<^sub>2)
        else null endif = expr\<^sub>2"
    apply (erule SafeDotCallNE)
    using NullableNullableCollectionSafeDotCallN.hyps(4)
          is_iterable_type.intros src_type_det apply blast
    using NullableNullableCollectionSafeDotCallN.hyps(4)
          iterable_type_det src_type_det apply blast
    using NullableNullableCollectionSafeDotCallN.hyps(4)
          NullableNullableCollectionSafeDotCallN.hyps(5)
          iterable_type_det src_type_det apply blast
    by (metis NullableNullableCollectionSafeDotCallN.hyps(2)
        NullableNullableCollectionSafeDotCallN.hyps(4)
        NullableNullableCollectionSafeDotCallN.hyps(6)
        NullableNullableCollectionSafeDotCallN.hyps(8)
        NullableNullableCollectionSafeDotCallN.hyps(9)
        comp_def iterable_type_det src_type_det)
  thus ?case by (simp add: NullableNullableCollectionSafeDotCallN.prems)
next
  case (NullableCollectionSafeArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using NullableCollectionSafeArrowCallN.hyps typing_det by auto
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?->call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        if src\<^sub>2 <> null
        then src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>)->call\<^sub>2
        else null endif = expr\<^sub>2"
    apply (erule SafeArrowCallNE)
    using NullableCollectionSafeArrowCallN.hyps(4)
          iterable_type_det src_type_det apply blast
    apply (simp add: NullableCollectionSafeArrowCallN.hyps(2)
           NullableCollectionSafeArrowCallN.hyps(7) src_type_det)
    using NullableCollectionSafeArrowCallN.hyps(4)
          NullableCollectionSafeArrowCallN.hyps(5)
          iterable_type_det src_type_det by blast
  thus ?case by (simp add: NullableCollectionSafeArrowCallN.prems)
next
  case (NullableNullableCollectionSafeArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> src\<^sub>3 \<rho>
                                                 call\<^sub>1 call\<^sub>2)
  have src_type_det: "\<And>src\<^sub>2' \<tau>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow> \<tau> = \<tau>'"
    using NullableNullableCollectionSafeArrowCallN.hyps typing_det by auto
  have src_type_det':
    "\<And>src\<^sub>2' \<tau>' \<sigma>' \<rho>'. \<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2' \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>E src\<^sub>2' : \<tau>' \<Longrightarrow>
     optional_iterable_type \<tau>' \<sigma>' \<Longrightarrow>
     optional_type \<sigma>' \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>E src\<^sub>2\<^bold>.oclAsType(to_required_type \<tau>')->
            selectByKind(to_required_type \<sigma>') : \<rho>' \<Longrightarrow> \<rho> = \<rho>'"
    using NullableNullableCollectionSafeArrowCallN.hyps(4)
          NullableNullableCollectionSafeArrowCallN.hyps(6)
          NullableNullableCollectionSafeArrowCallN.hyps(7)
          iterable_type_det src_type_det typing_det by blast
  have "\<And>expr\<^sub>2. \<Gamma> \<turnstile> src\<^sub>1?->call\<^sub>1 \<Rrightarrow> expr\<^sub>2 \<Longrightarrow>
        if src\<^sub>2 <> null
        then src\<^sub>3->call\<^sub>2
        else null endif = expr\<^sub>2"
    apply (erule SafeArrowCallNE)
    using NullableNullableCollectionSafeArrowCallN.hyps(4)
          iterable_type_det src_type_det apply blast
    using NullableNullableCollectionSafeArrowCallN.hyps(4)
          NullableNullableCollectionSafeArrowCallN.hyps(5)
          iterable_type_det src_type_det apply blast
    using NullableNullableCollectionSafeArrowCallN.hyps(2)
          NullableNullableCollectionSafeArrowCallN.hyps(4)
          NullableNullableCollectionSafeArrowCallN.hyps(6)
          NullableNullableCollectionSafeArrowCallN.hyps(9)
          iterable_type_det src_type_det src_type_det' by fastforce
  thus ?case by (simp add: NullableNullableCollectionSafeArrowCallN.prems)
next
  case (TypeOperationN \<Gamma> \<tau> op ty) thus ?case by auto
next
  case (AttributeN \<Gamma> \<tau> attr) thus ?case by auto
next
  case (AssociationEndN \<Gamma> \<tau> role "from") thus ?case by auto
next
  case (AssociationClassN \<Gamma> \<tau> \<A> "from") thus ?case by auto
next
  case (AssociationClassEndN \<Gamma> \<tau> role) thus ?case by auto
next
  case (OperationN \<Gamma> params\<^sub>1 params\<^sub>2 \<tau> op) thus ?case by blast
next
  case (TupleElementN \<Gamma> \<tau> elem) thus ?case by auto
next
  case (IterateN \<Gamma> res_init\<^sub>1 res_init\<^sub>2 \<tau> its its_ty\<^sub>1 res res_t\<^sub>1 body\<^sub>1
                 its_ty\<^sub>2 res_t\<^sub>2 body\<^sub>2 k)
  have
    "\<And>call\<^sub>2. (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Iterate its its_ty\<^sub>1 res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
     Iterate its its_ty\<^sub>2 res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2 = call\<^sub>2"
    apply (erule IterateCallNE)
    using IterateN.hyps(4) by blast
  thus ?case by (simp add: IterateN.prems)
next
  case (ClosureIterationN iter \<Gamma> \<tau> its its_ty\<^sub>1 body\<^sub>1 its_ty\<^sub>2 body\<^sub>2 \<sigma> k body\<^sub>3)
  have "\<And>call\<^sub>2. (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Iterator iter its its_ty\<^sub>1 body\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
       Iterator iter its its_ty\<^sub>2 body\<^sub>3 = call\<^sub>2"
    apply (erule IterationCallNE)
    using ClosureIterationN.hyps normalize_closure_body_det by fastforce+
  thus ?case by (simp add: ClosureIterationN.prems)
next
  case (IterationN iter \<Gamma> \<tau> its its_ty\<^sub>1 body\<^sub>1 its_ty\<^sub>2 body\<^sub>2 k)
  have "\<And>call\<^sub>2. (\<Gamma>, \<tau>, k) \<turnstile>\<^sub>C Iterator iter its its_ty\<^sub>1 body\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
       Iterator iter its its_ty\<^sub>2 body\<^sub>2 = call\<^sub>2"
    apply (erule IterationCallNE)
    apply (simp add: IterationN.hyps(1))
    using IterationN.hyps(3) by blast
  thus ?case by (simp add: IterationN.prems)
next
  case (ExplicitlyTypedCollectionLoopN \<tau> uy uz \<Gamma> its \<sigma> body\<^sub>1 body\<^sub>2)
  have "\<And>ns. (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<sigma>, None), body\<^sub>1) \<Rrightarrow> ns \<Longrightarrow>
        (its, (Some \<sigma>, None), body\<^sub>2) = ns"
    apply (erule LoopNE)
    using ExplicitlyTypedCollectionLoopN.hyps(1)
          ExplicitlyTypedCollectionLoopN.hyps(3)
          any_collection_type_and_map_type_distinct by blast+
  thus ?case by (simp add: ExplicitlyTypedCollectionLoopN.prems)
next
  case (ImplicitlyTypedCollectionLoopN \<tau> \<sigma> va \<Gamma> its body\<^sub>1 body\<^sub>2)
  have "\<And>ns. (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, None), body\<^sub>1) \<Rrightarrow> ns \<Longrightarrow>
        (its, (Some \<sigma>, None), body\<^sub>2) = ns"
    apply (erule LoopNE)
    using ImplicitlyTypedCollectionLoopN.hyps(1)
          ImplicitlyTypedCollectionLoopN.hyps(3)
          any_collection_type_and_map_type_distinct
          any_collection_type_det by blast+
  thus ?case by (simp add: ImplicitlyTypedCollectionLoopN.prems)
next
  case (ExplicitlyTypedMapLoopN \<tau> va vb vc \<Gamma> its \<sigma> \<rho> body\<^sub>1 body\<^sub>2)
  have "\<And>ns. (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<sigma>, Some \<rho>), body\<^sub>1) \<Rrightarrow> ns \<Longrightarrow>
        (its, (Some \<sigma>, Some \<rho>), body\<^sub>2) = ns"
    using ExplicitlyTypedMapLoopN.hyps(3) by auto
  thus ?case by (simp add: ExplicitlyTypedMapLoopN.prems)
next
  case (ImplicitlyTypedMapKeyLoopN \<tau> \<sigma> vd ve \<Gamma> its \<rho> body\<^sub>1 body\<^sub>2)
  have "\<And>ns. (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, Some \<rho>), body\<^sub>1) \<Rrightarrow> ns \<Longrightarrow>
        (its, (Some \<sigma>, Some \<rho>), body\<^sub>2) = ns"
    using ImplicitlyTypedMapKeyLoopN.hyps(1)
          ImplicitlyTypedMapKeyLoopN.hyps(3) map_type_det(1) by blast
  thus ?case by (simp add: ImplicitlyTypedMapKeyLoopN.prems)
next
  case (ImplicitlyTypedMapValueLoopN \<tau> vf \<rho> vg \<Gamma> its \<sigma> body\<^sub>1 body\<^sub>2)
  have "\<And>ns. (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (Some \<sigma>, None), body\<^sub>1) \<Rrightarrow> ns \<Longrightarrow>
        (its, (Some \<sigma>, Some \<rho>), body\<^sub>2) = ns"
    apply (erule LoopNE)
    using ImplicitlyTypedMapValueLoopN.hyps(1)
          ImplicitlyTypedMapValueLoopN.hyps(3) map_type_det(1)
          any_collection_type_and_map_type_distinct by blast+
  thus ?case by (simp add: ImplicitlyTypedMapValueLoopN.prems)
next
  case (ImplicitlyTypedMapLoopN \<tau> \<sigma> \<rho> vh \<Gamma> its body\<^sub>1 body\<^sub>2)
  have "\<And>ns. (\<Gamma>, \<tau>) \<turnstile>\<^sub>I (its, (None, None), body\<^sub>1) \<Rrightarrow> ns \<Longrightarrow>
        (its, (Some \<sigma>, Some \<rho>), body\<^sub>2) = ns"
    apply (erule LoopNE)
    using ImplicitlyTypedMapLoopN.hyps(1)
          ImplicitlyTypedMapLoopN.hyps(3) map_type_det(1)
          any_collection_type_and_map_type_distinct by blast+
  thus ?case by (simp add: ImplicitlyTypedMapLoopN.prems)
next
  case (ExprListNilN \<Gamma>) thus ?case by auto
next
  case (ExprListConsN \<Gamma> x y xs ys) thus ?case by blast
qed

(*** Normalized Expressions Typing ******************************************)

section \<open>Normalized Expressions Typing\<close>

text \<open>
  Here is the final typing rules.\<close>

inductive nf_typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50) where
  "\<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>N \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E expr\<^sub>N : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> expr : \<tau>"

lemma nf_typing_det:
  "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  by (metis nf_typing.cases normalize_det typing_det)

lemmas ocl_normalization_simps =
  normalize_closure_body_alt_simps
  normalize_alt_simps
  nf_typing.simps

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool,
    i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] normalize_closure_body .

code_pred (modes:
    normalize: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
    normalize_loop: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
    normalize_expr_list: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
    normalize_call: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_modes] normalize .

code_pred nf_typing .

end

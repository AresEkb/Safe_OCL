(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Expressions Normal Form\<close>
theory OCL_Normal_Form
  imports OCL_Typing
begin

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition "new_vname \<equiv> String.implode \<circ> string_of_nat \<circ> fcard \<circ> fmdom"


definition "is_required \<tau> \<equiv> \<tau> \<le> OclAny[1]"
definition "is_optional \<tau> \<equiv> OclVoid \<le> \<tau> \<and> \<tau> \<le> OclAny[?]"
definition "is_collection_of_non_optional \<tau> \<equiv>
  \<exists>\<sigma>. element_type \<tau> \<sigma> \<and> \<not> OclVoid \<le> \<sigma>"
definition "is_collection_of_optional \<tau> \<equiv>
  \<exists>\<sigma>. element_type \<tau> \<sigma> \<and> OclVoid \<le> \<sigma> \<and> \<sigma> \<le> OclAny[?]"
(*
inductive is_collection_of_required where
  "element_type \<tau> \<sigma> \<Longrightarrow> \<sigma> \<le> OclAny[1] \<Longrightarrow>
   is_collection_of_required \<tau> \<sigma>"
*)

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
   \<Gamma> \<turnstile> If a1 b1 c1 \<Rrightarrow> If a1 b1 c1"

|MetaOperationCallN:
  "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> MetaOperationCall \<tau> op"
|StaticOperationCallN:
  "\<Gamma> \<turnstile>\<^sub>L as \<Rrightarrow> bs \<Longrightarrow>
   \<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow>
       StaticOperationCall \<tau> op bs"

|OclAnyDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[1] \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 DotCall call1 \<Rrightarrow> Call src2 DotCall call2"
|OclAnySafeDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   OclVoid \<le> \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[?] \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 SafeDotCall call1 \<Rrightarrow>
       If (OperationCall src2 DotCall NotEqualOp [NullLiteral])
          (Call src2 DotCall call2)
          NullLiteral"
|OclAnyArrowDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[?] \<Longrightarrow>
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
   OclVoid \<le> \<sigma> \<Longrightarrow>
   \<sigma> \<le> OclAny[?] \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 SafeArrowCall call1 \<Rrightarrow>
       Call (OperationCall src2 ArrowCall ExcludingOp [NullLiteral]) ArrowCall call2"
|CollectionDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   \<not> OclVoid \<le> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 DotCall call1 \<Rrightarrow> CollectIteratorCall src2 [it]
          (Call (Var it) DotCall call2)"
|CollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src1 \<Rrightarrow> src2 \<Longrightarrow>
   \<Gamma> \<turnstile> src2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid \<le> \<sigma> \<Longrightarrow>
   \<sigma> \<le> OclAny[?] \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call1 \<Rrightarrow> call2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src1 SafeDotCall call1 \<Rrightarrow>
      CollectIteratorCall (OperationCall src2 ArrowCall ExcludingOp [NullLiteral])
        [it] (Call (Var it) DotCall call2)"

|TypeOperationN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C TypeOperation op ty \<Rrightarrow> TypeOperation op ty"
|IterateN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> res_init1 \<Rrightarrow> res_init2 \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile>
      Let res res_t res_init1 body1 \<Rrightarrow> Let res res_t res_init2 body2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its res res_t res_init1 body1 \<Rrightarrow> Iterate its res res_t res_init2 body2"
|IteratorN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   fmadd \<Gamma> (fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its)) \<turnstile> body1 \<Rrightarrow> body2  \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its body1 \<Rrightarrow> Iterator iter its body2"
|AttributeN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Attribute attr \<Rrightarrow> Attribute attr"
|AssociationEndN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C AssociationEnd role \<Rrightarrow> AssociationEnd role"
|OperationN:
  "\<Gamma> \<turnstile>\<^sub>L as \<Rrightarrow> bs \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> Operation op bs"
|TupleElementN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C TupleElement elem \<Rrightarrow> TupleElement elem"

|ExprListNilN:
  "\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> []"
|ExprListConsN:
  "\<Gamma> \<turnstile> x \<Rrightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> y # ys"

code_pred [show_modes] normalize .

inductive_cases Literal_normalize [elim]: "\<Gamma> \<turnstile> Literal a \<Rrightarrow> b"
inductive_cases Let_normalize [elim]: "\<Gamma> \<turnstile> Let v t init body \<Rrightarrow> b"
inductive_cases Var_normalize [elim]: "\<Gamma> \<turnstile> Var v \<Rrightarrow> b"
inductive_cases If_normalize [elim]: "\<Gamma> \<turnstile> If a b c \<Rrightarrow> d"
inductive_cases MetaOperationCall_normalize [elim]: "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> b"
inductive_cases StaticOperationCall_normalize [elim]: "\<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> b"
inductive_cases DotCall_normalize [elim]: "\<Gamma> \<turnstile> Call src DotCall call \<Rrightarrow> b"
inductive_cases SafeDotCall_normalize [elim]: "\<Gamma> \<turnstile> Call src SafeDotCall call \<Rrightarrow> b"
inductive_cases ArrowCall_normalize [elim]: "\<Gamma> \<turnstile> Call src ArrowCall call \<Rrightarrow> b"
inductive_cases SafeArrowCall_normalize [elim]: "\<Gamma> \<turnstile> Call src SafeArrowCall call \<Rrightarrow> b"

inductive_cases normalize_call_elim [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C call \<Rrightarrow> b"
(*inductive_cases BinaryOperation_normalize_call [elim]:
  "(\<Gamma>, \<tau>) \<turnstile> BinaryOperation op a1 \<Rrightarrow>\<^sub>C call2"
inductive_cases TernaryOperation_normalize_call [elim]:
  "(\<Gamma>, \<tau>) \<turnstile> TernaryOperation op a1 b1 \<Rrightarrow>\<^sub>C call2"*)
inductive_cases Operation_normalize_call [elim]:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call2"
inductive_cases Iterate_normalize_call [elim]:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its res res_t res_init1 body1 \<Rrightarrow> call2"
inductive_cases Iterator_normalize_call [elim]:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its body1 \<Rrightarrow> call2"

inductive_cases normalize_expr_list_elim [elim]:
  "\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> zs"

lemma any_has_not_element_type:
  "\<tau> \<le> OclAny[?] \<Longrightarrow> element_type \<tau> \<sigma> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma
  normalize_det: "\<Gamma> \<turnstile> expr \<Rrightarrow> expr1 \<Longrightarrow> \<Gamma> \<turnstile> expr \<Rrightarrow> expr2 \<Longrightarrow> expr1 = expr2" and
  normalize_call_det: "\<Gamma>1 \<turnstile>\<^sub>C call \<Rrightarrow> call1 \<Longrightarrow> \<Gamma>1 \<turnstile>\<^sub>C call \<Rrightarrow> call2 \<Longrightarrow> call1 = call2" and
  normalize_expr_list_det:
    "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> zs \<Longrightarrow> ys = zs"
  for \<Gamma> :: "('a :: ocl_object_model) type env"
  and \<Gamma>1 :: "('a :: ocl_object_model) type env \<times> 'a type"
proof (induct \<Gamma> expr expr1 and \<Gamma>1 call call1
       arbitrary: expr2 and call2 and zs
       rule: normalize_normalize_call_normalize_expr_list.inducts)
  case (LiteralN \<Gamma> a) thus ?case by auto
next
  case (LetN \<Gamma> init1 init2 v \<tau> body1 body2) thus ?case by blast
next
  case (VarN \<Gamma> v) thus ?case by auto
next
  case (IfN \<Gamma> a1 a2 b1 b2 c1 c2) thus ?case by auto
next
  case (MetaOperationCallN \<Gamma> \<tau> op) thus ?case by auto
next
  case (StaticOperationCallN \<Gamma> as bs \<tau> op) thus ?case by blast
next
  case (OclAnyDotCallN \<Gamma> src1 src2 \<tau> call1 call2) show ?case
    apply (insert OclAnyDotCallN.prems)
    apply (erule DotCall_normalize)
    apply (metis OclAnyDotCallN.hyps(2) OclAnyDotCallN.hyps(3) OclAnyDotCallN.hyps(6) typing_det)
    by (metis OclAnyDotCallN.hyps(2) OclAnyDotCallN.hyps(3) OclAnyDotCallN.hyps(4) any_has_not_element_type type_less_eq_x_Optional_intro(2) typing_det)
next
  case (OclAnySafeDotCallN \<Gamma> src1 src2 \<tau> call1 call2) show ?case
    apply (insert OclAnySafeDotCallN.prems)
    apply (erule SafeDotCall_normalize)
    apply (metis (no_types, lifting) OclAnySafeDotCallN.hyps(2) OclAnySafeDotCallN.hyps(3) OclAnySafeDotCallN.hyps(7) comp_apply list.simps(8) list.simps(9) typing_det)
(*    apply (metis OclAnySafeDotCallN.hyps(2) OclAnySafeDotCallN.hyps(3) OclAnySafeDotCallN.hyps(7) typing_det)*)
    by (metis OclAnySafeDotCallN.hyps(2) OclAnySafeDotCallN.hyps(3) OclAnySafeDotCallN.hyps(5) any_has_not_element_type typing_det)
next
  case (OclAnyArrowDotCallN \<Gamma> src1 src2 \<tau> call1 call2) show ?case
    apply (insert OclAnyArrowDotCallN.prems)
    apply (erule ArrowCall_normalize)
    apply (metis OclAnyArrowDotCallN.hyps(2) OclAnyArrowDotCallN.hyps(3) OclAnyArrowDotCallN.hyps(6) comp_apply typing_det)
(*    apply (metis OclAnyArrowDotCallN.hyps(2) OclAnyArrowDotCallN.hyps(3) OclAnyArrowDotCallN.hyps(6) typing_det)*)
    by (metis OclAnyArrowDotCallN.hyps(2) OclAnyArrowDotCallN.hyps(3) OclAnyArrowDotCallN.hyps(4) any_has_not_element_type typing_det)
next
  case (CollectionArrowCallN \<Gamma> src1 src2 \<tau> call1 call2 uu) show ?case
    apply (insert CollectionArrowCallN.prems)
    apply (erule ArrowCall_normalize)
    apply (metis CollectionArrowCallN.hyps(2) CollectionArrowCallN.hyps(3) CollectionArrowCallN.hyps(4) any_has_not_element_type typing_det)
    using CollectionArrowCallN.hyps(2) CollectionArrowCallN.hyps(3) CollectionArrowCallN.hyps(6) typing_det by fastforce
next
  case (CollectionSafeArrowCallN \<Gamma> src1 src2 \<tau> call1 call2 \<sigma>) show ?case
    apply (insert CollectionSafeArrowCallN.prems)
    apply (erule SafeArrowCall_normalize)
    by (smt CollectionSafeArrowCallN.hyps(2) CollectionSafeArrowCallN.hyps(3) CollectionSafeArrowCallN.hyps(8) comp_assoc comp_eq_dest_lhs list.simps(8) list.simps(9) typing_det)
(*    by (metis CollectionSafeArrowCallN.hyps(2) CollectionSafeArrowCallN.hyps(3) CollectionSafeArrowCallN.hyps(8) comp_eq_dest_lhs typing_det)*)
next
  case (CollectionDotCallN \<Gamma> src1 src2 \<tau> call1 call2 \<sigma> it) show ?case
    apply (insert CollectionDotCallN.prems)
    apply (erule DotCall_normalize)
    apply (metis CollectionDotCallN.hyps(2) CollectionDotCallN.hyps(3) CollectionDotCallN.hyps(4) any_has_not_element_type type_less_eq_x_Optional_intro(2) typing_det)
    using CollectionDotCallN.hyps(2) CollectionDotCallN.hyps(3) CollectionDotCallN.hyps(7) CollectionDotCallN.hyps(8) typing_det by fastforce
next
  case (CollectionSafeDotCallN \<Gamma> src1 src2 \<tau> call1 call2 \<sigma> it) show ?case
    apply (insert CollectionSafeDotCallN.prems)
    apply (erule SafeDotCall_normalize)
    apply (metis CollectionSafeDotCallN.hyps(2) CollectionSafeDotCallN.hyps(3) CollectionSafeDotCallN.hyps(4) any_has_not_element_type typing_det)
    by (metis (no_types, lifting) CollectionSafeDotCallN.hyps(2) CollectionSafeDotCallN.hyps(3) CollectionSafeDotCallN.hyps(8) CollectionSafeDotCallN.hyps(9) comp_apply list.simps(8) list.simps(9) typing_det)
(*    by (metis CollectionSafeDotCallN.hyps(2) CollectionSafeDotCallN.hyps(3) CollectionSafeDotCallN.hyps(8) CollectionSafeDotCallN.hyps(9) comp_eq_dest_lhs typing_det)*)
(*next
  case (OclTypeN \<Gamma> \<tau>) thus ?case by auto*)
next
  case (TypeOperationN \<Gamma> \<tau> op ty) thus ?case by auto
(*next
  case (UnaryOperationN \<Gamma> \<tau> op) thus ?case by auto
next
  case (BinaryOperationN \<Gamma> a1 a2 \<tau> op) show ?case
    apply (insert BinaryOperationN.prems)
    apply (erule BinaryOperation_normalize_call)
    by (simp add: BinaryOperationN.hyps(2))
next
  case (TernaryOperationN \<Gamma> a1 a2 b1 b2 \<tau> op) show ?case
    apply (insert TernaryOperationN.prems)
    apply (erule TernaryOperation_normalize_call)
    by (simp add: TernaryOperationN.hyps(2) TernaryOperationN.hyps(4))*)
next
  case (IterateN \<tau> \<sigma> \<Gamma> res_init1 res_init2 its res res_t body1 body2)
  show ?case
    apply (insert IterateN.prems)
    apply (erule Iterate_normalize_call)
    using IterateN.hyps(1) IterateN.hyps(5) element_type_det by blast
next
  case (IteratorN \<tau> \<sigma> \<Gamma> its body1 body2 iter)
  show ?case
    apply (insert IteratorN.prems)
    apply (erule Iterator_normalize_call)
    using IteratorN.hyps(1) IteratorN.hyps(3) element_type_det by auto
next
  case (AttributeN \<Gamma> \<tau> attr) thus ?case by auto
next
  case (AssociationEndN \<Gamma> \<tau> role) thus ?case by auto
next
  (*case (OperationN \<Gamma> \<tau> op as) thus ?case by auto*)
  case (OperationN \<Gamma> as bs \<tau> op) show ?case
    apply (insert OperationN.prems)
    apply (erule Operation_normalize_call)
    by (simp add: OperationN.hyps(2))
next
  case (TupleElementN \<Gamma> \<tau> elem) thus ?case by auto
next
  case (ExprListNilN \<Gamma>) thus ?case
    using normalize_expr_list.cases by auto
next
  case (ExprListConsN \<Gamma> x y xs ys) thus ?case by blast
qed

end

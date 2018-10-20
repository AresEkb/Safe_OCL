theory OCLtoXPath
  imports Main OCL XPath
    "~~/src/HOL/Library/Product_Order"
begin

no_notation (ASCII) Set.member  ("(_/ : _)" [51, 51] 50)

notation ProgLang.typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
notation ProgLang.big_step (infix "\<Rightarrow>" 55)
notation ProgLang.etyping (infix "\<turnstile>" 50)
(*notation ProgLang.cast (infix "as!" 55)
notation ProgLang.cast_eq (infix "as" 55)
notation ProgLang.cast_either (infix "as*" 55)*)


(*
  Можно пока не рассматривать свойства, потому что их можно заменить
  на переменные, которые могут иметь пустое или ошибочное значение.
*)


(* OCL Stuff *)

inductive ocl_is_supported :: "OCL.exp \<Rightarrow> bool" where
"ocl_is_supported (OCL.BooleanLiteral _)" |
"ocl_is_supported (OCL.IntegerLiteral _)" |
"ocl_is_supported (OCL.RealLiteral _)" |
"ocl_is_supported init \<Longrightarrow>
 ocl_is_supported body \<Longrightarrow>
 ocl_is_supported (OCL.Let var init body)" |
"ocl_is_supported (OCL.Var var)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported b \<Longrightarrow>
 ocl_is_supported (OCL.And a b)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported b \<Longrightarrow>
 ocl_is_supported (OCL.Or a b)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported b \<Longrightarrow>
 ocl_is_supported (OCL.Implies a b)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported (OCL.Not a)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported b \<Longrightarrow>
 ocl_is_supported (OCL.Plus a b)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported b \<Longrightarrow>
 ocl_is_supported (OCL.Divide a b)" |
"ocl_is_supported a \<Longrightarrow>
 ocl_is_supported b \<Longrightarrow>
 ocl_is_supported (OCL.Less a b)"

inductive_cases BooleanLiteralSupported[elim!]: "ocl_is_supported (OCL.BooleanLiteral c)"
inductive_cases IntegerLiteralSupported[elim!]: "ocl_is_supported (OCL.IntegerLiteral c)"
inductive_cases LetSupported[elim!]: "ocl_is_supported (OCL.Let var init body)"
inductive_cases VarSupported[elim!]: "ocl_is_supported (OCL.Var var)"
inductive_cases AndSupported[elim!]: "ocl_is_supported (OCL.And a b)"
inductive_cases OrSupported[elim!]: "ocl_is_supported (OCL.Or a b)"
inductive_cases ImpliesSupported[elim!]: "ocl_is_supported (OCL.Implies a b)"
inductive_cases NotSupported[elim!]: "ocl_is_supported (OCL.Not a)"
inductive_cases PlusSupported[elim!]: "ocl_is_supported (OCL.Plus a b)"
inductive_cases DivideSupported[elim!]: "ocl_is_supported (OCL.Divide a b)"
inductive_cases LessSupported[elim!]: "ocl_is_supported (OCL.Less a b)"

(*** OCL and XPath Stuff ****************************************************************)

inductive ocl_eq :: "OCLType.val \<Rightarrow> OCLType.val \<Rightarrow> bool" where
  "ocl_eq NullVal NullVal"
| "ocl_eq (BooleanVal x) (BooleanVal y)"
| "ocl_eq (RealVal x) (RealVal y)"
| "ocl_eq (IntegerVal x) (IntegerVal y)"
| "ocl_eq (UnlimNatVal x) (UnlimNatVal y)"
| "ocl_eq (StringVal x) (StringVal y)"

inductive xpath_eq :: "XPathType.val \<Rightarrow> XPathType.val \<Rightarrow> bool" where
  "xpath_eq (BValue x) (BValue y)"
| "xpath_eq (IValue x) (IValue y)"
| "xpath_eq (DValue x) (DValue y)"
| "xpath_eq (NNIValue x) (NNIValue y)"

inductive ocl_has_safe_div :: "OCLType.val env \<Rightarrow> OCL.exp \<Rightarrow> bool" where
  "ocl_has_safe_div e (OCL.NullLiteral)"
| "ocl_has_safe_div e (OCL.BooleanLiteral _)"
| "ocl_has_safe_div e (OCL.RealLiteral _)"
| "ocl_has_safe_div e (OCL.IntegerLiteral _)"
| "ocl_has_safe_div e (OCL.UnlimNatLiteral _)"
| "ocl_has_safe_div e (OCL.StringLiteral _)"
| "(init, e) \<Rightarrow> x \<Longrightarrow>
   ocl_has_safe_div e init \<Longrightarrow>
   ocl_has_safe_div (e(var\<mapsto>x)) body \<Longrightarrow>
   ocl_has_safe_div e (OCL.Let var init body)"
| "ocl_has_safe_div e (OCL.Var var)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   ocl_has_safe_div e (OCL.And a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   ocl_has_safe_div e (OCL.Or a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   ocl_has_safe_div e (OCL.Xor a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   ocl_has_safe_div e (OCL.Implies a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e (OCL.Not a)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   ocl_has_safe_div e (OCL.Plus a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   (a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   yn \<noteq> Just 0 \<Longrightarrow>
   ocl_has_safe_div e (OCL.Divide a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   (a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (IntegerVal xn, IntegerVal yn) \<Longrightarrow>
   yn \<noteq> Just 0 \<Longrightarrow>
   ocl_has_safe_div e (OCL.Divide a b)"
| "ocl_has_safe_div e a \<Longrightarrow>
   ocl_has_safe_div e b \<Longrightarrow>
   ocl_has_safe_div e (OCL.Less a b)"

inductive_cases ocl_has_safe_div_NullLiteralE[elim!]: "ocl_has_safe_div e (OCL.NullLiteral)"
inductive_cases ocl_has_safe_div_BooleanLiteralE[elim!]: "ocl_has_safe_div e (OCL.BooleanLiteral c)"
inductive_cases ocl_has_safe_div_RealLiteralE[elim!]: "ocl_has_safe_div e (OCL.RealLiteral c)"
inductive_cases ocl_has_safe_div_IntegerLiteralE[elim!]: "ocl_has_safe_div e (OCL.IntegerLiteral c)"
inductive_cases ocl_has_safe_div_UnlimNatLiteralE[elim!]: "ocl_has_safe_div e (OCL.UnlimNatLiteral c)"
inductive_cases ocl_has_safe_div_StringLiteralE[elim!]: "ocl_has_safe_div e (OCL.StringLiteral c)"
inductive_cases ocl_has_safe_div_LetE[elim!]: "ocl_has_safe_div e (OCL.Let var init body)"
inductive_cases ocl_has_safe_div_VarE[elim!]: "ocl_has_safe_div e (OCL.Var var)"
inductive_cases ocl_has_safe_div_AndE[elim!]: "ocl_has_safe_div e (OCL.And a b)"
inductive_cases ocl_has_safe_div_OrE[elim!]: "ocl_has_safe_div e (OCL.Or a b)"
inductive_cases ocl_has_safe_div_XorE[elim!]: "ocl_has_safe_div e (OCL.Xor a b)"
inductive_cases ocl_has_safe_div_ImpliesE[elim!]: "ocl_has_safe_div e (OCL.Implies a b)"
inductive_cases ocl_has_safe_div_NotE[elim!]: "ocl_has_safe_div e (OCL.Not a)"
inductive_cases ocl_has_safe_div_PlusE[elim!]: "ocl_has_safe_div e (OCL.Plus a b)"
inductive_cases ocl_has_safe_div_DivideE[elim!]: "ocl_has_safe_div e (OCL.Divide a b)"
inductive_cases ocl_has_safe_div_LessE[elim!]: "ocl_has_safe_div e (OCL.Less a b)"
(*
inductive xpath_has_safe_div :: "XPathType.val env \<Rightarrow> XPath.exp \<Rightarrow> bool" where
  "xpath_has_safe_div e (XPath.BConst _)"
| "xpath_has_safe_div e (XPath.IConst _)"
| "xpath_has_safe_div e (XPath.DConst _)"
| "(init, e) \<Rightarrow> x \<Longrightarrow>
   xpath_has_safe_div e init \<Longrightarrow>
   xpath_has_safe_div (e(var\<mapsto>x)) body \<Longrightarrow>
   xpath_has_safe_div e (XPath.Let var init body)"
| "xpath_has_safe_div e (XPath.Var var)"
| "xpath_has_safe_div e a \<Longrightarrow>
   xpath_has_safe_div e b \<Longrightarrow>
   xpath_has_safe_div e (XPath.And a b)"
| "xpath_has_safe_div e a \<Longrightarrow>
   xpath_has_safe_div e b \<Longrightarrow>
   xpath_has_safe_div e (XPath.Or a b)"
| "xpath_has_safe_div e a \<Longrightarrow>
   xpath_has_safe_div e (XPath.Not a)"
| "xpath_has_safe_div e a \<Longrightarrow>
   xpath_has_safe_div e b \<Longrightarrow>
   xpath_has_safe_div e (XPath.Plus a b)"
| "xpath_has_safe_div e a \<Longrightarrow>
   xpath_has_safe_div e b \<Longrightarrow>
   (b, e) \<Rightarrow> DValue (Some v) \<Longrightarrow>
   v \<noteq> 0 \<Longrightarrow>
   xpath_has_safe_div e (XPath.Divide a b)"
| "xpath_has_safe_div e a \<Longrightarrow>
   xpath_has_safe_div e b \<Longrightarrow>
   xpath_has_safe_div e (XPath.Less a b)"

inductive_cases xpath_has_safe_div_BConstE[elim!]: "xpath_has_safe_div e (XPath.BConst c)"
inductive_cases xpath_has_safe_div_IConstE[elim!]: "xpath_has_safe_div e (XPath.IConst c)"
inductive_cases xpath_has_safe_div_DConstE[elim!]: "xpath_has_safe_div e (XPath.DConst c)"
inductive_cases xpath_has_safe_div_LetE[elim!]: "xpath_has_safe_div e (XPath.Let var init body)"
inductive_cases xpath_has_safe_div_VarE[elim!]: "xpath_has_safe_div e (XPath.Var var)"
inductive_cases xpath_has_safe_div_AndE[elim!]: "xpath_has_safe_div e (XPath.And a b)"
inductive_cases xpath_has_safe_div_OrE[elim!]: "xpath_has_safe_div e (XPath.Or a b)"
inductive_cases xpath_has_safe_div_NotE[elim!]: "xpath_has_safe_div e (XPath.Not a)"
inductive_cases xpath_has_safe_div_PlusE[elim!]: "xpath_has_safe_div e (XPath.Plus a b)"
inductive_cases xpath_has_safe_div_DivideE[elim!]: "xpath_has_safe_div e (XPath.Divide a b)"
inductive_cases xpath_has_safe_div_LessE[elim!]: "xpath_has_safe_div e (XPath.Less a b)"
*)
(******************* Type Env Translator *********************************************************)

inductive type_equiv :: "OCLType.type \<Rightarrow> XPathType.type \<Rightarrow> bool" (infix "\<sim>" 50) where
XS_booleanEquiv: "OCLType.BooleanType \<sim> XPathType.XS_boolean" |
XS_integerEquiv: "OCLType.IntegerType \<sim> XPathType.XS_integer" |
XS_decimalEquiv: "OCLType.RealType \<sim> XPathType.XS_decimal"

fun ocl_to_xpath_type :: "OCLType.type \<Rightarrow> XPathType.type option" where
  "ocl_to_xpath_type OCLType.BooleanType = Some XPathType.XS_boolean" |
  "ocl_to_xpath_type OCLType.IntegerType = Some XPathType.XS_integer" |
  "ocl_to_xpath_type OCLType.RealType = Some XPathType.XS_decimal" |
  "ocl_to_xpath_type _ = None"

fun xpath_to_ocl_type :: "XPathType.type \<Rightarrow> OCLType.type option" where
  "xpath_to_ocl_type XPathType.XS_boolean = Some OCLType.BooleanType" |
  "xpath_to_ocl_type XPathType.XS_integer = Some OCLType.IntegerType" |
  "xpath_to_ocl_type XPathType.XS_decimal = Some OCLType.RealType" |
  "xpath_to_ocl_type _ = None"

lemma ocl_to_xpath_type_eq_type_equiv:
  "(ocl_to_xpath_type \<tau>\<^sub>F = Some \<tau>\<^sub>B) = (\<tau>\<^sub>F \<sim> \<tau>\<^sub>B)"
  using ocl_to_xpath_type.elims type_equiv.simps by auto

definition ocl_to_xpath_tenv :: "OCLType.type env \<Rightarrow> XPathType.type env" where
  "ocl_to_xpath_tenv env \<equiv> ocl_to_xpath_type \<circ>\<^sub>m env"

definition ocl_tenv_is_safe :: "OCLType.type env \<Rightarrow> bool" where
  "ocl_tenv_is_safe env \<equiv> \<forall>x. \<exists>y z. env x = Some y \<and> y \<sim> z"

definition xpath_tenv_is_safe :: "XPathType.type env \<Rightarrow> bool" where
  "xpath_tenv_is_safe env \<equiv> \<forall>x. \<exists>y z. env x = Some z \<and> y \<sim> z"

inductive ocl_to_xpath_tenv_ind :: "OCLType.type env \<Rightarrow> XPathType.type env \<Rightarrow> bool"
  ("_ \<sim>/ _" [50,50] 50) where
  "\<forall>x. \<exists>y z. env1 x = Some y \<and> y \<sim> z \<Longrightarrow>
   env2 = ocl_to_xpath_type \<circ>\<^sub>m env1 \<Longrightarrow>
   env1 \<sim> env2"

inductive_cases ocl_to_xpath_tenv_indE[elim!]: "ocl_to_xpath_tenv_ind env1 env2"

code_pred [show_modes] ocl_to_xpath_tenv_ind .

lemma ocl_to_xpath_tenv_distr:
  "ocl_to_xpath_type \<tau> = Some \<sigma> \<Longrightarrow>
   (ocl_to_xpath_tenv \<Gamma>)(var \<mapsto> \<sigma>) =
   ocl_to_xpath_tenv (\<Gamma>(var \<mapsto> \<tau>))"
  by (auto simp: map_comp_def ocl_to_xpath_tenv_def)
(*
lemma ocl_to_xpath_tenv_each:
  "\<Gamma>\<^sub>B = ocl_to_xpath_tenv \<Gamma>\<^sub>F \<Longrightarrow>
   \<Gamma>\<^sub>F x = Some \<tau> \<Longrightarrow>
   \<Gamma>\<^sub>B x = ocl_to_xpath_type \<tau>"
  by (simp add: ocl_to_xpath_tenv_def)
*)
lemma q42:
  "\<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1) \<sim> \<Gamma>\<^sub>B(var \<mapsto> \<tau>\<^sub>2) \<Longrightarrow>
   \<tau>\<^sub>1 \<sim> \<tau>\<^sub>2"
  by (metis (no_types, hide_lams) fun_upd_same map_comp_def ocl_to_xpath_tenv_indE ocl_to_xpath_type_eq_type_equiv option.simps(5))

lemma q421:
  "\<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<tau>\<^sub>1 \<sim> \<tau>\<^sub>2 \<Longrightarrow>
   \<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1) \<sim> \<Gamma>\<^sub>B(var \<mapsto> \<tau>\<^sub>2)"
  by (smt fun_upd_apply ocl_to_xpath_tenv_def ocl_to_xpath_tenv_distr ocl_to_xpath_tenv_ind.intros ocl_to_xpath_tenv_indE ocl_to_xpath_type_eq_type_equiv)

lemma xpath_to_ocl_type_eq_type_equiv:
  "(xpath_to_ocl_type v\<^sub>B = Some v\<^sub>F) = (v\<^sub>F \<sim> v\<^sub>B)"
  apply (induct v\<^sub>B; auto simp add: type_equiv.simps)
  done

inductive xpath_to_ocl_tenv_ind :: "OCLType.type env \<Rightarrow> XPathType.type env \<Rightarrow> bool"
  ("_ \<sim>2/ _" [50,50] 50) where
  "\<forall>x. \<exists>y z. env2 x = Some z \<and> y \<sim> z \<Longrightarrow>
   env1 = xpath_to_ocl_type \<circ>\<^sub>m env2 \<Longrightarrow>
   env1 \<sim>2 env2"

inductive_cases xpath_to_ocl_tenv_indE[elim!]: "xpath_to_ocl_tenv_ind env1 env2"

lemma type_sup_equiv:
  "a \<sim> x \<Longrightarrow>
   b \<sim> y \<Longrightarrow>
   a \<squnion> b = t \<Longrightarrow>
   x \<squnion> y = s \<Longrightarrow>
   t < AnyType \<Longrightarrow>
   t \<sim> s"
  apply (induct rule: type_equiv.induct; induct rule: type_equiv.induct)
  apply (simp add: XS_booleanEquiv)
  using OCLType.sup_type_def le_neq_trans apply fastforce
  using OCLType.sup_type_def le_neq_trans apply fastforce
  using OCLType.sup_type_def le_neq_trans apply fastforce
  apply (simp add: XS_integerEquiv)
  apply (simp add: XS_decimalEquiv less_imp_le sup.absorb2)
  using OCLType.sup_type_def le_neq_trans apply fastforce
  apply (metis OCLType.less_type.simps(19) XPathType.less_type.simps(10) sup.strict_order_iff type_equiv.simps)
  apply (simp add: XS_decimalEquiv)
  done

lemma type_sup_equivE:
  "t \<sim> s \<Longrightarrow>
   (a \<sim> x \<Longrightarrow> P) \<Longrightarrow>
   (b \<sim> y \<Longrightarrow> P) \<Longrightarrow>
   (a \<squnion> b = t \<Longrightarrow> P) \<Longrightarrow>
   (x \<squnion> y = s \<Longrightarrow> P) \<Longrightarrow>
   (t < AnyType \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis OCLType.less_type.simps(14) OCLType.less_type.simps(15) OCLType.less_type.simps(16) type_equiv.simps)

lemma preserve_type_b2:
  "\<tau>\<^sub>F \<sim> \<tau>\<^sub>B \<Longrightarrow>
   \<tau>\<^sub>F \<le> BooleanType \<Longrightarrow>
   \<tau>\<^sub>B = XS_boolean"
  apply (induct rule: type_equiv.induct; simp add: order.order_iff_strict)
  done

lemma preserve_type_r2:
  "\<tau>\<^sub>F \<sim> \<tau>\<^sub>B \<Longrightarrow>
   \<tau>\<^sub>F \<le> RealType \<Longrightarrow>
   \<tau>\<^sub>B \<le> XS_decimal"
  apply (induct rule: type_equiv.induct; simp add: order.order_iff_strict)
  done

lemma preserve_type_i2:
  "\<tau>\<^sub>F \<sim> \<tau>\<^sub>B \<Longrightarrow>
   \<tau>\<^sub>F \<le> IntegerType \<Longrightarrow>
   \<tau>\<^sub>B \<le> XS_integer"
  apply (induct rule: type_equiv.induct; simp add: order.order_iff_strict)
  done

lemma preserve_type_u2:
  "\<tau>\<^sub>F \<sim> \<tau>\<^sub>B \<Longrightarrow>
   \<tau>\<^sub>F \<le> UnlimNatType \<Longrightarrow>
   \<tau>\<^sub>B \<le> XS_integer"
  apply (induct rule: type_equiv.induct; simp add: order.order_iff_strict)
  done

lemma xpath_to_ocl_type_simp:
  "\<exists>y. x \<sim> y \<Longrightarrow>
   (xpath_to_ocl_type \<circ>\<^sub>m ocl_to_xpath_type) x = Some x"
  using map_comp_simps(2) type_equiv.simps by auto

lemma ocl_to_xpath_type_simp:
  "\<exists>y. y \<sim> x \<Longrightarrow>
   (ocl_to_xpath_type \<circ>\<^sub>m xpath_to_ocl_type) x = Some x"
  using map_comp_simps(2) type_equiv.simps by auto

lemma xpath_to_ocl_tenv_simp:
  "\<forall>x. \<exists>y z. env\<^sub>F x = Some y \<and> y \<sim> z \<Longrightarrow>
   env\<^sub>F = (xpath_to_ocl_type \<circ>\<^sub>m ocl_to_xpath_type) \<circ>\<^sub>m env\<^sub>F"
  apply (simp add: fun_eq_iff)
  by (metis map_comp_simps(2) xpath_to_ocl_type_simp)

lemma ocl_to_xpath_tenv_simp:
  "\<forall>x. \<exists>y z. env\<^sub>F x = Some z \<and> y \<sim> z \<Longrightarrow>
   env\<^sub>F = (ocl_to_xpath_type \<circ>\<^sub>m xpath_to_ocl_type) \<circ>\<^sub>m env\<^sub>F"
  apply (simp add: fun_eq_iff)
  by (metis map_comp_simps(2) ocl_to_xpath_type_simp)

lemma xpath_to_ocl_tenv_assoc:
  "\<forall>x. \<exists>y. \<Gamma>\<^sub>F x = Some y \<Longrightarrow>
   xpath_to_ocl_type \<circ>\<^sub>m (ocl_to_xpath_type \<circ>\<^sub>m \<Gamma>\<^sub>F) =
   (xpath_to_ocl_type \<circ>\<^sub>m ocl_to_xpath_type) \<circ>\<^sub>m \<Gamma>\<^sub>F"
  apply (simp add: map_comp_def)
  by (metis option.simps(5))

lemma ocl_to_xpath_tenv_assoc:
  "\<forall>x. \<exists>y. \<Gamma>\<^sub>F x = Some y \<Longrightarrow>
   ocl_to_xpath_type \<circ>\<^sub>m (xpath_to_ocl_type \<circ>\<^sub>m \<Gamma>\<^sub>F) =
   (ocl_to_xpath_type \<circ>\<^sub>m xpath_to_ocl_type) \<circ>\<^sub>m \<Gamma>\<^sub>F"
  apply (simp add: map_comp_def)
  by (metis option.simps(5))

lemma ocl_to_xpath_tenv_ind_then:
  "\<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow> \<Gamma>\<^sub>F \<sim>2 \<Gamma>\<^sub>B"
  apply (rule xpath_to_ocl_tenv_ind.intros; auto)
  apply (metis map_comp_simps(2) ocl_to_xpath_type_eq_type_equiv)
  by (metis xpath_to_ocl_tenv_assoc xpath_to_ocl_tenv_simp)

lemma xpath_to_ocl_tenv_ind_then:
  "\<Gamma>\<^sub>F \<sim>2 \<Gamma>\<^sub>B \<Longrightarrow> \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B"
  apply (rule ocl_to_xpath_tenv_ind.intros; auto)
  apply (metis map_comp_simps(2) xpath_to_ocl_type_eq_type_equiv)
  by (metis ocl_to_xpath_tenv_assoc ocl_to_xpath_tenv_simp)

lemma ocl_to_xpath_tenv_safe:
  "\<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   ocl_tenv_is_safe \<Gamma>\<^sub>F \<and> xpath_tenv_is_safe \<Gamma>\<^sub>B"
  using ocl_tenv_is_safe_def ocl_to_xpath_tenv_ind_then xpath_tenv_is_safe_def xpath_to_ocl_tenv_ind.simps by auto


(******************* Val Env Translator **********************************************************)

inductive val_equiv :: "OCLType.val \<Rightarrow> XPathType.val \<Rightarrow> bool" (infix "\<approx>" 50) where
  "OCLType.BooleanVal (Just v) \<approx> BValue (Only v)"
| "OCLType.IntegerVal (Just v) \<approx> IValue (Some v)"
| "OCLType.RealVal (Just v) \<approx> DValue (Some v)"

lemma val_equiv_is_fun:
  "v\<^sub>F \<approx> v\<^sub>B\<^sub>1 \<Longrightarrow> v\<^sub>F \<approx> v\<^sub>B\<^sub>2 \<Longrightarrow> v\<^sub>B\<^sub>1 = v\<^sub>B\<^sub>2"
  using val_equiv.simps by auto

fun ocl_to_xpath_val :: "OCLType.val \<Rightarrow> XPathType.val option" where
  "ocl_to_xpath_val (OCLType.BooleanVal v) =
    (case v of Just v1 \<Rightarrow> Some (BValue (Only v1)) | _ \<Rightarrow> None)" |
  "ocl_to_xpath_val (OCLType.IntegerVal v) =
    (case v of Just v1 \<Rightarrow> Some (IValue (Some v1)) | _ \<Rightarrow> None)" |
  "ocl_to_xpath_val (OCLType.RealVal v) =
    (case v of Just v1 \<Rightarrow> Some (DValue (Some v1)) | _ \<Rightarrow> None)" |
  "ocl_to_xpath_val (OCLType.StringVal v) = None" |
  "ocl_to_xpath_val _ = None"

fun xpath_to_ocl_val :: "XPathType.val \<Rightarrow> OCLType.val option" where
  "xpath_to_ocl_val (BValue v) =
    (case v of Only v1 \<Rightarrow> Some (OCLType.BooleanVal (Just v1)) | _ \<Rightarrow> None)" |
  "xpath_to_ocl_val (IValue v) =
    (case v of Some v1 \<Rightarrow> Some (OCLType.IntegerVal (Just v1)) | _ \<Rightarrow> None)" |
  "xpath_to_ocl_val (DValue v) =
    (case v of Some v1 \<Rightarrow> Some (OCLType.RealVal (Just v1)) | _ \<Rightarrow> None)" |
  "xpath_to_ocl_val _ = None"

definition xpath_to_ocl_env :: "XPathType.val env \<Rightarrow> OCLType.val env" where
  "xpath_to_ocl_env env \<equiv> xpath_to_ocl_val \<circ>\<^sub>m env"

lemma xpath_to_ocl_env_assoc:
  "\<forall>x. \<exists>y. env\<^sub>F x = Some y \<Longrightarrow>
   xpath_to_ocl_val \<circ>\<^sub>m (ocl_to_xpath_val \<circ>\<^sub>m env\<^sub>F) =
   (xpath_to_ocl_val \<circ>\<^sub>m ocl_to_xpath_val) \<circ>\<^sub>m env\<^sub>F"
  apply (simp add: map_comp_def)
  by (metis option.simps(5))

lemma ocl_to_xpath_env_assoc:
  "\<forall>x. \<exists>y. env\<^sub>F x = Some y \<Longrightarrow>
   ocl_to_xpath_val \<circ>\<^sub>m (xpath_to_ocl_val \<circ>\<^sub>m env\<^sub>F) =
   (ocl_to_xpath_val \<circ>\<^sub>m xpath_to_ocl_val) \<circ>\<^sub>m env\<^sub>F"
  apply (simp add: map_comp_def)
  by (metis option.simps(5))

lemma errorable_case_simp [simp]:
  "((case x of Just y \<Rightarrow> Some (P y) | _ \<Rightarrow> None) = Some z) =
   (\<exists>y. x = Just y \<and> z = P y)"
  by (cases x; auto)

lemma nondet_case_simp [simp]:
  "((case x of Only y \<Rightarrow> Some (P y) | _ \<Rightarrow> None) = Some z) =
   (\<exists>y. x = Only y \<and> z = P y)"
  by (cases x; auto)

lemma ocl_to_xpath_val_eq_value_equiv:
  "(ocl_to_xpath_val v\<^sub>F = Some v\<^sub>B) = (v\<^sub>F \<approx> v\<^sub>B)"
  by (induct v\<^sub>F; simp add: val_equiv.simps)

definition ocl_to_xpath_env :: "OCLType.val env \<Rightarrow> XPathType.val env" where
  "ocl_to_xpath_env env \<equiv> ocl_to_xpath_val \<circ>\<^sub>m env"

inductive ocl_to_xpath_env_ind :: "OCLType.val env \<Rightarrow> XPathType.val env \<Rightarrow> bool"
  ("_ \<approx>/ _" [50,50] 50) where
  "\<forall>x. \<exists>y z. env1 x = Some y \<and> y \<approx> z \<Longrightarrow>
   env2 = ocl_to_xpath_val \<circ>\<^sub>m env1 \<Longrightarrow>
   ocl_to_xpath_env_ind env1 env2"

inductive_cases ocl_to_xpath_env_indE[elim!]: "ocl_to_xpath_env_ind env1 env2"

code_pred [show_modes] ocl_to_xpath_env_ind .

lemma ocl_to_xpath_val_distr:
  "v\<^sub>F \<approx> v\<^sub>B \<Longrightarrow>
   ocl_to_xpath_env (env\<^sub>F(var\<mapsto>v\<^sub>F)) = (ocl_to_xpath_env env\<^sub>F)(var\<mapsto>v\<^sub>B)"
  by (auto simp: map_comp_def ocl_to_xpath_val_eq_value_equiv ocl_to_xpath_env_def)

definition ocl_env_is_safe :: "OCLType.val env \<Rightarrow> bool" where
  "ocl_env_is_safe env \<equiv> \<forall>x. \<exists>y z. env x = Some y \<and> y \<approx> z"

lemma i11:
  "ocl_to_xpath_env_ind env\<^sub>F env\<^sub>B \<Longrightarrow>
   (ocl_env_is_safe env\<^sub>F \<Longrightarrow>
   env\<^sub>B = ocl_to_xpath_env env\<^sub>F \<Longrightarrow> P) \<Longrightarrow> P"
  using ocl_env_is_safe_def ocl_to_xpath_env_def by auto

lemma xpath_to_ocl_val_eq_value_equiv:
  "(xpath_to_ocl_val v\<^sub>B = Some v\<^sub>F) = (v\<^sub>F \<approx> v\<^sub>B)"
  apply (induct v\<^sub>B; auto simp add: val_equiv.simps)
  apply (metis option.case_eq_if option.collapse option.inject option.simps(3))
  apply (metis option.case_eq_if option.collapse option.inject option.simps(3))
  done

lemma xpath_to_ocl_val_distr:
  "v\<^sub>F \<approx> v\<^sub>B \<Longrightarrow>
   xpath_to_ocl_env (env\<^sub>B(var\<mapsto>v\<^sub>B)) = (xpath_to_ocl_env env\<^sub>B)(var\<mapsto>v\<^sub>F)"
  by (auto simp: map_comp_def xpath_to_ocl_val_eq_value_equiv xpath_to_ocl_env_def)

inductive xpath_to_ocl_env_ind :: "OCLType.val env \<Rightarrow> XPathType.val env \<Rightarrow> bool"
  ("_ \<approx>2/ _" [50,50] 50) where
  "\<forall>x. \<exists>y z. env2 x = Some z \<and> y \<approx> z \<Longrightarrow>
   env1 = xpath_to_ocl_val \<circ>\<^sub>m env2 \<Longrightarrow>
   xpath_to_ocl_env_ind env1 env2"

definition xpath_env_is_safe :: "XPathType.val env \<Rightarrow> bool" where
  "xpath_env_is_safe env \<equiv> \<forall>x. \<exists>y z. env x = Some z \<and> y \<approx> z"

inductive_cases xpath_to_ocl_env_indE[elim!]: "xpath_to_ocl_env_ind env1 env2"

code_pred [show_modes] xpath_to_ocl_env_ind .

lemma ocl_env_is_safe_then_xpath_env_is_safe:
  "\<forall>x. \<exists>y z. env\<^sub>F x = Some y \<and> y \<approx> z \<Longrightarrow>
   env\<^sub>B = ocl_to_xpath_val \<circ>\<^sub>m env\<^sub>F \<Longrightarrow>
   \<forall>x. \<exists>y z. env\<^sub>B x = Some z \<and> y \<approx> z"
  by (metis map_comp_simps(2) ocl_to_xpath_val_eq_value_equiv)

lemma xpath_to_ocl_val_simp:
  "\<exists>y. x \<approx> y \<Longrightarrow>
   (xpath_to_ocl_val \<circ>\<^sub>m ocl_to_xpath_val) x = Some x"
  by (simp add: map_comp_Some_iff ocl_to_xpath_val_eq_value_equiv xpath_to_ocl_val_eq_value_equiv)

lemma ocl_to_xpath_val_simp:
  "\<exists>y. y \<approx> x \<Longrightarrow>
   (ocl_to_xpath_val \<circ>\<^sub>m xpath_to_ocl_val) x = Some x"
  by (simp add: map_comp_Some_iff ocl_to_xpath_val_eq_value_equiv xpath_to_ocl_val_eq_value_equiv)

lemma xpath_to_ocl_env_simp:
  "\<forall>x. \<exists>y z. env\<^sub>F x = Some y \<and> y \<approx> z \<Longrightarrow>
   env\<^sub>F = (xpath_to_ocl_val \<circ>\<^sub>m ocl_to_xpath_val) \<circ>\<^sub>m env\<^sub>F"
  apply (simp add: fun_eq_iff)
  by (metis map_comp_simps(2) xpath_to_ocl_val_simp)

lemma ocl_to_xpath_env_simp:
  "\<forall>x. \<exists>y z. env\<^sub>F x = Some z \<and> y \<approx> z \<Longrightarrow>
   env\<^sub>F = (ocl_to_xpath_val \<circ>\<^sub>m xpath_to_ocl_val) \<circ>\<^sub>m env\<^sub>F"
  apply (simp add: fun_eq_iff)
  by (metis map_comp_simps(2) ocl_to_xpath_val_simp)

lemma ocl_to_xpath_env_ind_then:
  "env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow> env\<^sub>F \<approx>2 env\<^sub>B"
  apply (rule xpath_to_ocl_env_ind.intros; auto)
  apply (metis map_comp_simps(2) ocl_to_xpath_val_eq_value_equiv)
  by (metis xpath_to_ocl_env_assoc xpath_to_ocl_env_simp)

lemma xpath_to_ocl_env_ind_then:
  "env\<^sub>F \<approx>2 env\<^sub>B \<Longrightarrow> env\<^sub>F \<approx> env\<^sub>B"
  apply (rule ocl_to_xpath_env_ind.intros; auto)
  apply (metis map_comp_simps(2) xpath_to_ocl_val_eq_value_equiv)
  by (metis ocl_to_xpath_env_assoc ocl_to_xpath_env_simp)

lemma ocl_to_xpath_env_safe:
  "env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   ocl_env_is_safe env\<^sub>F \<and> xpath_env_is_safe env\<^sub>B"
  by (meson i11 ocl_to_xpath_env_ind_then xpath_env_is_safe_def xpath_to_ocl_env_ind.simps)

lemma e41:
  "xpath_env_is_safe env\<^sub>B \<Longrightarrow>
   env\<^sub>F = xpath_to_ocl_env env\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx>2 env\<^sub>B"
  using xpath_env_is_safe_def xpath_to_ocl_env_def xpath_to_ocl_env_ind.simps by auto

lemma s10:
  "env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   x \<approx> y \<Longrightarrow>
   env\<^sub>F(var\<mapsto>x) \<approx> env\<^sub>B(var\<mapsto>y)"
  by (smt fun_upd_apply i11 ocl_to_xpath_env_ind.intros ocl_to_xpath_env_indE ocl_to_xpath_val_distr)


(********************* Env and TEnv Relations ***************************************************)

lemma e15:
  "c \<sim> d \<Longrightarrow>
   a \<approx> b \<Longrightarrow>
   OCLType.type_of_val a = c \<Longrightarrow>
   XPathType.type_of_val b = d"
  apply (cases c; cases d; simp add: type_equiv.simps;
         cases a; cases b; simp add: val_equiv.simps)
  done

lemma preserve_good_env2:
  "\<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> env\<^sub>F \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B"
  apply (simp add: OCL.etyping_def XPath.etyping_def)
  apply (erule ocl_to_xpath_tenv_indE)
  apply (erule ocl_to_xpath_env_indE)
  by (smt e15 map_comp_def ocl_to_xpath_type_eq_type_equiv ocl_to_xpath_val_eq_value_equiv option.simps(5))

definition ocl_env_to_tenv :: "OCLType.val env \<Rightarrow> OCLType.type env" where
  "ocl_env_to_tenv env \<equiv> (map_option OCLType.type_of_val) \<circ> env"

lemma e21:
  "ocl_env_to_tenv env\<^sub>F \<turnstile> env\<^sub>F"
  using OCL.default_tenv_def OCL.default_tenv_exists ocl_env_to_tenv_def by auto

lemma e22:
  "a \<approx> b \<Longrightarrow>
   OCLType.type_of_val a \<sim> XPathType.type_of_val b"
  apply (induct rule: val_equiv.induct; simp add: type_equiv.simps)
  done

lemma e23:
  "a \<approx> b \<Longrightarrow>
   \<exists>d. OCLType.type_of_val a \<sim> d"
  using e22 by auto

lemma e24:
  "ocl_env_is_safe env\<^sub>F \<Longrightarrow>
   ocl_tenv_is_safe (ocl_env_to_tenv env\<^sub>F)"
  apply (simp add: ocl_env_is_safe_def ocl_env_to_tenv_def ocl_tenv_is_safe_def)
  using e23 by blast

lemma preserve_good_env3:
  "\<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> env\<^sub>F"
  apply (simp add: OCL.etyping_def XPath.etyping_def)
  apply (erule ocl_to_xpath_tenv_indE)
  apply (erule ocl_to_xpath_env_indE)
  by (smt e15 e23 map_comp_simps(2) ocl_to_xpath_type_eq_type_equiv ocl_to_xpath_val_eq_value_equiv option.simps(5) xpath_to_ocl_type_eq_type_equiv)

lemma ocl_env_is_safe_then_tenv_is_safe:
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   ocl_env_is_safe env \<Longrightarrow>
   ocl_tenv_is_safe \<Gamma>"
  apply (simp add: OCL.etyping_def ocl_tenv_is_safe_def ocl_env_is_safe_def)
  by (smt e22 option.case_eq_if option.collapse option.distinct(1) option.sel)

lemma xpath_env_is_safe_then_tenv_is_safe:
  "\<Gamma> \<turnstile> env \<Longrightarrow>
   xpath_env_is_safe env \<Longrightarrow>
   xpath_tenv_is_safe \<Gamma>"
  apply (simp add: XPath.etyping_def xpath_tenv_is_safe_def xpath_env_is_safe_def)
  by (smt e22 option.case_eq_if option.collapse option.distinct(1) option.sel)

(*********************** Exp Translator **********************************************************)

inductive ocl_to_xpath :: "OCL.exp \<Rightarrow> XPath.exp \<Rightarrow> bool"
  ("_ \<leadsto>/ _" [50,50] 50) where
ocl_to_xpath_bool:
"OCL.BooleanLiteral c \<leadsto> BConst c" |
ocl_to_xpath_int:
"OCL.IntegerLiteral c \<leadsto> IConst c" |
ocl_to_xpath_real:
"OCL.RealLiteral c \<leadsto> DConst c" |
ocl_to_xpath_let:
"init\<^sub>F \<leadsto> init\<^sub>B \<Longrightarrow>
 body\<^sub>F \<leadsto> body\<^sub>B \<Longrightarrow>
 OCL.Let var init\<^sub>F body\<^sub>F \<leadsto> XPath.Let var init\<^sub>B body\<^sub>B" |
ocl_to_xpath_var:
"OCL.Var var \<leadsto> XPath.Var var" |
ocl_to_xpath_and:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 b\<^sub>F \<leadsto> b\<^sub>B \<Longrightarrow>
 OCL.And a\<^sub>F b\<^sub>F \<leadsto> XPath.And a\<^sub>B b\<^sub>B" |
ocl_to_xpath_or:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 b\<^sub>F \<leadsto> b\<^sub>B \<Longrightarrow>
 OCL.Or a\<^sub>F b\<^sub>F \<leadsto> XPath.Or a\<^sub>B b\<^sub>B" |
ocl_to_xpath_implies:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 b\<^sub>F \<leadsto> b\<^sub>B \<Longrightarrow>
 OCL.Implies a\<^sub>F b\<^sub>F \<leadsto> XPath.Or (XPath.Not a\<^sub>B) b\<^sub>B" |
ocl_to_xpath_not:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 OCL.Not a\<^sub>F \<leadsto> XPath.Not a\<^sub>B" |
ocl_to_xpath_plus:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 b\<^sub>F \<leadsto> b\<^sub>B \<Longrightarrow>
 OCL.Plus a\<^sub>F b\<^sub>F \<leadsto> XPath.Plus a\<^sub>B b\<^sub>B" |
ocl_to_xpath_divide:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 b\<^sub>F \<leadsto> b\<^sub>B \<Longrightarrow>
 OCL.Divide a\<^sub>F b\<^sub>F \<leadsto> XPath.Divide a\<^sub>B b\<^sub>B" |
ocl_to_xpath_less:
"a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
 b\<^sub>F \<leadsto> b\<^sub>B \<Longrightarrow>
 OCL.Less a\<^sub>F b\<^sub>F \<leadsto> XPath.Less a\<^sub>B b\<^sub>B"

code_pred [show_modes] ocl_to_xpath .

inductive_cases FooBConstToBarE[elim!]: "OCL.BooleanLiteral c \<leadsto> exp\<^sub>B"
inductive_cases FooIConstToBarE[elim!]: "OCL.IntegerLiteral c \<leadsto> exp\<^sub>B"
inductive_cases FooDConstToBarE[elim!]: "OCL.RealLiteral c \<leadsto> exp\<^sub>B"
inductive_cases FooLetToBarE[elim!]: "OCL.Let var init\<^sub>F body\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooVarToBarE[elim!]: "OCL.Var var \<leadsto> exp\<^sub>B"
inductive_cases FooAndToBarE[elim!]: "OCL.And a\<^sub>F b\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooAndToBarE2[elim!]: "OCL.And a\<^sub>F b\<^sub>F \<leadsto> XPath.And a\<^sub>B b\<^sub>B"
inductive_cases FooOrToBarE[elim!]: "OCL.Or a\<^sub>F b\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooImpliesToBarE[elim!]: "OCL.Implies a\<^sub>F b\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooNotToBarE[elim!]: "OCL.Not a\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooPlusToBarE[elim!]: "OCL.Plus a\<^sub>F b\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooDivideToBarE[elim!]: "OCL.Divide a\<^sub>F b\<^sub>F \<leadsto> exp\<^sub>B"
inductive_cases FooLessToBarE[elim!]: "OCL.Less a\<^sub>F b\<^sub>F \<leadsto> exp\<^sub>B"

lemma ocl_to_xpath_is_fun:
  "exp\<^sub>F \<leadsto> exp\<^sub>B\<^sub>1 \<Longrightarrow>
   exp\<^sub>F \<leadsto> exp\<^sub>B\<^sub>2 \<Longrightarrow>
   exp\<^sub>B\<^sub>1 = exp\<^sub>B\<^sub>2"
  apply (induct exp\<^sub>F exp\<^sub>B\<^sub>1 arbitrary: exp\<^sub>B\<^sub>2 rule: ocl_to_xpath.induct)
  apply (erule FooBConstToBarE; simp)
  apply (erule FooIConstToBarE; simp)
  apply (erule FooDConstToBarE; simp)
  apply (erule FooLetToBarE; simp)
  apply (erule FooVarToBarE; simp)
  apply (erule FooAndToBarE; simp)
  apply (erule FooOrToBarE; simp)
  apply (erule FooImpliesToBarE; simp)
  apply (erule FooNotToBarE; simp)
  apply (erule FooPlusToBarE; simp)
  apply (erule FooDivideToBarE; simp)
  apply (erule FooLessToBarE; simp)
  done

(****************************************** Lemma 1 **********************************************)

lemma ocl_to_xpath_is_full2:
  "ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<exists>exp\<^sub>B. exp\<^sub>F \<leadsto> exp\<^sub>B"
  apply (induct rule: ocl_is_supported.induct)
  using ocl_to_xpath_bool apply auto[1]
  using ocl_to_xpath_int apply auto[1]
  using ocl_to_xpath_real apply auto[1]
  using ocl_to_xpath_let apply blast
  using ocl_to_xpath_var apply auto[1]
  using ocl_to_xpath_and apply blast
  using ocl_to_xpath_or apply blast
  using ocl_to_xpath_implies apply blast
  using ocl_to_xpath_not apply auto[1]
  using ocl_to_xpath_plus apply blast
  using ocl_to_xpath_divide apply blast
  using ocl_to_xpath_less apply blast
  done

(****************************************** Lemma 2 **********************************************)

lemma preserve_type2:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> exp\<^sub>B : \<tau>\<^sub>B \<Longrightarrow>
   \<tau>\<^sub>F \<sim> \<tau>\<^sub>B"
  apply (induct arbitrary: \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<tau>\<^sub>F \<tau>\<^sub>B rule: ocl_to_xpath.induct)
  using type_equiv.simps apply auto[1]
  using type_equiv.simps apply auto[1]
  using type_equiv.simps apply auto[1]
  apply (erule OCL.LetTE; erule XPath.LetTE; meson q421)
  using ocl_to_xpath_type_eq_type_equiv apply auto[1]
  using type_equiv.simps apply auto[1]
  using type_equiv.simps apply auto[1]
  using type_equiv.simps apply auto[1]
  using type_equiv.simps apply auto[1]
  apply (erule OCL.PlusTE; erule XPath.PlusTE)
  apply (metis OCLType.less_type.simps(15) type_sup_equiv)
  apply (metis OCLType.less_type.simps(15) type_sup_equiv)
  using XS_integerEquiv apply blast
  apply (metis OCLType.less_type.simps(16) type_sup_equiv)
  apply (metis OCLType.less_type.simps(17) type_sup_equiv)
  apply (metis OCLType.less_type.simps(17) type_sup_equiv)
  apply (erule OCL.DivideTE; erule XPath.DivideTE)
  using XS_decimalEquiv apply blast
  apply (erule OCL.LessTE; erule XPath.LessTE)
  using XS_booleanEquiv apply blast
  done

lemma q222:
  "    (*\<Gamma>\<^sub>F \<turnstile> init\<^sub>F \<leadsto> \<Gamma>\<^sub>B \<turnstile> init\<^sub>B \<Longrightarrow>*)
       init\<^sub>F \<leadsto> init\<^sub>B \<Longrightarrow>
       (
           \<Gamma>\<^sub>F \<turnstile> init\<^sub>F : \<tau>\<^sub>1 \<Longrightarrow>
           ocl_to_xpath_tenv_ind \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<Longrightarrow>
           (ProgLang.typing (ocl_to_xpath_tenv \<Gamma>\<^sub>F) init\<^sub>B) \<tau>\<^sub>2) \<Longrightarrow>
       (*\<Gamma>\<^sub>F \<turnstile> body\<^sub>F \<leadsto> \<Gamma>\<^sub>B \<turnstile> body\<^sub>B \<Longrightarrow>*)
       body\<^sub>F \<leadsto> body\<^sub>B \<Longrightarrow>
       (
           \<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1) \<turnstile> body\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
           ocl_to_xpath_tenv_ind (\<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1)) (\<Gamma>\<^sub>B(var \<mapsto> \<tau>\<^sub>2)) \<Longrightarrow>
           (ProgLang.typing (ocl_to_xpath_tenv (\<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1))) body\<^sub>B) \<tau>\<^sub>B) \<Longrightarrow>
       \<Gamma>\<^sub>F \<turnstile> init\<^sub>F : \<tau>\<^sub>1 \<Longrightarrow>
       (*Some \<tau>\<^sub>2 = ocl_to_xpath_type \<tau>\<^sub>1 \<Longrightarrow>*)
       (*Some \<tau>\<^sub>B = ocl_to_xpath_type \<tau>\<^sub>F \<Longrightarrow>*)
       ocl_to_xpath_tenv_ind \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<Longrightarrow>
       (*\<Gamma>\<^sub>B(var \<mapsto> \<tau>\<^sub>2) = ocl_to_xpath_tenv (\<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1)) \<Longrightarrow>*)
       \<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1) \<turnstile> body\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
       (ProgLang.typing (ocl_to_xpath_tenv \<Gamma>\<^sub>F)
            (XPath.exp.Let var init\<^sub>B body\<^sub>B) \<tau>\<^sub>B)"
  apply auto
  by (metis ocl_to_xpath_tenv_def ocl_to_xpath_tenv_ind.simps preserve_type2 q421 XPath.typing.intros(4))

lemma q253:
  "    (*\<Gamma>\<^sub>F \<turnstile> init\<^sub>F \<leadsto> \<Gamma>\<^sub>B \<turnstile> init\<^sub>B \<Longrightarrow>*)
       init\<^sub>F \<leadsto> init\<^sub>B \<Longrightarrow>
       (\<And>\<Gamma>\<^sub>F \<Gamma>\<^sub>B \<tau>\<^sub>F.
           \<Gamma>\<^sub>F \<turnstile> init\<^sub>F : (\<tau>\<^sub>F :: OCLType.type) \<Longrightarrow>
           ocl_is_supported init\<^sub>F \<Longrightarrow>
           ocl_to_xpath_tenv_ind \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<Longrightarrow>
           Ex (ProgLang.typing \<Gamma>\<^sub>B init\<^sub>B)) \<Longrightarrow>
       (*\<Gamma>\<^sub>F \<turnstile> body\<^sub>F \<leadsto> \<Gamma>\<^sub>B \<turnstile> body\<^sub>B \<Longrightarrow>*)
       body\<^sub>F \<leadsto> body\<^sub>B \<Longrightarrow>
       (\<And>\<Gamma>\<^sub>F \<Gamma>\<^sub>B \<tau>\<^sub>F.
           \<Gamma>\<^sub>F \<turnstile> body\<^sub>F : (\<tau>\<^sub>F :: OCLType.type) \<Longrightarrow>
           ocl_is_supported body\<^sub>F \<Longrightarrow>
           ocl_to_xpath_tenv_ind \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<Longrightarrow>
           Ex (ProgLang.typing \<Gamma>\<^sub>B body\<^sub>B)) \<Longrightarrow>
       \<Gamma>\<^sub>F \<turnstile> OCL.exp.Let var init\<^sub>F body\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
       ocl_is_supported (OCL.exp.Let var init\<^sub>F body\<^sub>F) \<Longrightarrow>
       ocl_to_xpath_tenv_ind \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<Longrightarrow>
       Ex (ProgLang.typing \<Gamma>\<^sub>B (XPath.exp.Let var init\<^sub>B body\<^sub>B))"
  by (metis LetSupported OCL.LetTE preserve_type2 q421 XPath.typing.intros(4))

lemma q322:
  "    a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
       \<Gamma>\<^sub>F \<turnstile> a\<^sub>F : \<tau>\<^sub>1 \<Longrightarrow>
       \<Gamma>\<^sub>B \<turnstile> a\<^sub>B : \<tau>\<^sub>3 \<Longrightarrow>
       \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
       \<tau>\<^sub>1 \<le> BooleanType \<Longrightarrow>
       \<tau>\<^sub>3 = XS_boolean"
  by (meson preserve_type2 preserve_type_b2)

lemma q323:
  "    a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
       \<Gamma>\<^sub>F \<turnstile> a\<^sub>F : \<tau>\<^sub>1 \<Longrightarrow>
       \<Gamma>\<^sub>B \<turnstile> a\<^sub>B : \<tau>\<^sub>3 \<Longrightarrow>
       \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
       \<tau>\<^sub>1 \<le> RealType \<Longrightarrow>
       \<tau>\<^sub>3 \<le> XS_decimal"
  by (meson preserve_type2 preserve_type_r2)

lemma q324:
  "    a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
       \<Gamma>\<^sub>F \<turnstile> a\<^sub>F : \<tau>\<^sub>1 \<Longrightarrow>
       \<Gamma>\<^sub>B \<turnstile> a\<^sub>B : \<tau>\<^sub>3 \<Longrightarrow>
       \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
       \<tau>\<^sub>1 \<le> IntegerType \<Longrightarrow>
       \<tau>\<^sub>3 \<le> XS_integer"
  by (meson preserve_type2 preserve_type_i2)

lemma q325:
  "    a\<^sub>F \<leadsto> a\<^sub>B \<Longrightarrow>
       \<Gamma>\<^sub>F \<turnstile> a\<^sub>F : \<tau>\<^sub>1 \<Longrightarrow>
       \<Gamma>\<^sub>B \<turnstile> a\<^sub>B : \<tau>\<^sub>3 \<Longrightarrow>
       \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
       \<tau>\<^sub>1 \<le> UnlimNatType \<Longrightarrow>
       \<tau>\<^sub>3 \<le> XS_integer"
  by (meson preserve_type2 preserve_type_u2)
(*
The lemma can't be proven.
Some of well-typed expressions are not supported yet.
Some of supported expressions are not well-typed, because this function doesn't check types.

lemma ocl_is_supported_then_has_type:
  "ocl_is_supported_fun \<Gamma>\<^sub>F exp\<^sub>F \<Longrightarrow>
   (*ocl_env_is_safe \<Gamma>\<^sub>F \<Longrightarrow>*)
   \<exists>\<tau>\<^sub>F. \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F"
  apply (induct exp\<^sub>F arbitrary: \<Gamma>\<^sub>F)
  apply simp
  using typing.intros(2) apply auto[1]
  apply simp
  using typing.intros(4) apply auto[1]
  apply simp
  apply simp
  apply (smt ocl_is_supported_fun.simps(7) q5 typing.intros(7))
  using typing.intros(8) apply auto[1]
*)

(****************************************** Lemma 3 **********************************************)

thm OrT2
thm OCL.OrTE
thm OCL.ImpliesTE
thm sup.cobounded2 sup_ge2

lemma preserve_has_type:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<exists>\<tau>\<^sub>B. \<Gamma>\<^sub>B \<turnstile> exp\<^sub>B : \<tau>\<^sub>B"
  apply (induct arbitrary: \<Gamma>\<^sub>F \<Gamma>\<^sub>B \<tau>\<^sub>F rule: ocl_to_xpath.induct)
  using XPath.typing.intros(1) apply auto[1]
  using XPath.typing.intros(2) apply auto[1]
  using XPath.typing.intros(3) apply auto[1]
  apply (simp add: q253)
  apply (auto simp add: map_comp_def)[1]
  apply (metis ocl_to_xpath_type_eq_type_equiv option.case_eq_if option.distinct(1) option.sel XPath.typing.intros(5))
  apply (erule AndSupported; erule OCL.AndTE;
         metis AndT2 q322 sup_ge1 sup_ge2)
  apply (erule OrSupported; erule OCL.OrTE;
         metis OrT2 q322 sup_ge1 sup_ge2)
  apply (erule ImpliesSupported; erule OCL.ImpliesTE;
         metis OrNotT2 q322 sup_ge1 sup_ge2)
  apply (erule NotSupported; erule OCL.NotTE;
         metis NotT2 q322 sup.idem sup.orderI)
  apply (erule PlusSupported; erule OCL.PlusTE)
  apply (smt le_sup_iff num_type_cases2 q323 sup_ge1 sup_ge2 XPath.typing.intros(10) XPath.typing.intros(9))
  apply (smt le_sup_iff num_type_cases3 q324 sup_ge1 sup_ge2 XPath.typing.intros(10) XPath.typing.intros(9))
  apply (smt le_sup_iff num_type_cases3 q325 sup_ge1 sup_ge2 XPath.typing.intros(10) XPath.typing.intros(9))
  apply (erule DivideSupported; erule OCL.DivideTE;
         metis le_sup_iff q323 XPath.typing.intros(11))
  apply (erule LessSupported; erule OCL.LessTE;
         metis le_sup_iff q323 XPath.typing.intros(12))
  done

lemma preserve_has_type2:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<exists>\<tau>\<^sub>B. \<Gamma>\<^sub>B \<turnstile> exp\<^sub>B : \<tau>\<^sub>B \<and> \<tau>\<^sub>F \<sim> \<tau>\<^sub>B"
  by (meson preserve_has_type preserve_type2)

lemma and_val_eq_nondet_and_val:
  "BooleanVal a\<^sub>F \<approx> BValue a\<^sub>B \<Longrightarrow>
   BooleanVal b\<^sub>F \<approx> BValue b\<^sub>B \<Longrightarrow>
   BooleanVal (and_val a\<^sub>F b\<^sub>F) \<approx> BValue (nondet_and_val a\<^sub>B b\<^sub>B)"
  using val_equiv.simps by auto

lemma or_val_eq_nondet_or_val:
  "BooleanVal a\<^sub>F \<approx> BValue a\<^sub>B \<Longrightarrow>
   BooleanVal b\<^sub>F \<approx> BValue b\<^sub>B \<Longrightarrow>
   BooleanVal (or_val a\<^sub>F b\<^sub>F) \<approx> BValue (nondet_or_val a\<^sub>B b\<^sub>B)"
  using val_equiv.simps by auto

lemma implies_val_eq_nondet_or_not_val:
  "BooleanVal a\<^sub>F \<approx> BValue a\<^sub>B \<Longrightarrow>
   BooleanVal b\<^sub>F \<approx> BValue b\<^sub>B \<Longrightarrow>
   BooleanVal (implies_val a\<^sub>F b\<^sub>F) \<approx> BValue (nondet_or_val (nondet_not_val a\<^sub>B) b\<^sub>B)"
  using val_equiv.simps implies_eq_not_or by auto

lemma not_val_eq_nondet_not_val:
  "BooleanVal a\<^sub>F \<approx> BValue a\<^sub>B \<Longrightarrow>
   BooleanVal (not_val a\<^sub>F) \<approx> BValue (nondet_not_val a\<^sub>B)"
  using val_equiv.simps by auto

lemma and_val_eq_nondet_and_val2:
  "x as BooleanVal xb \<Longrightarrow>
   y as BooleanVal yb \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   y \<approx> BValue ya \<Longrightarrow>
   BooleanVal (and_val xb yb) \<approx> BValue (nondet_and_val xa ya)"
  apply (simp add: OCLType.cast_eq_def OCLType.cast.simps)
  using and_val_eq_nondet_and_val val_equiv.simps by blast

lemma and_val_eq_nondet_and_val3:
  "(x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   y \<approx> BValue ya \<Longrightarrow>
   BooleanVal (and_val xb yb) \<approx> BValue (nondet_and_val xa ya)"
  apply (simp add: OCLType.cast_either.simps OCLType.cast_eq_def OCLType.cast.simps)
  using and_val_eq_nondet_and_val val_equiv.simps by blast

lemma or_val_eq_nondet_or_val2:
  "x as BooleanVal xb \<Longrightarrow>
   y as BooleanVal yb \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   y \<approx> BValue ya \<Longrightarrow>
   BooleanVal (or_val xb yb) \<approx> BValue (nondet_or_val xa ya)"
  apply (simp add: OCLType.cast_eq_def OCLType.cast.simps)
  using or_val_eq_nondet_or_val val_equiv.simps by blast

lemma or_val_eq_nondet_or_val3:
  "(x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   y \<approx> BValue ya \<Longrightarrow>
   BooleanVal (or_val xb yb) \<approx> BValue (nondet_or_val xa ya)"
  apply (simp add: OCLType.cast_either.simps OCLType.cast_eq_def OCLType.cast.simps)
  using or_val_eq_nondet_or_val val_equiv.simps by blast

lemma implies_val_eq_nondet_or_not_val2:
  "x as BooleanVal xb \<Longrightarrow>
   y as BooleanVal yb \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   y \<approx> BValue ya \<Longrightarrow>
   BooleanVal (implies_val xb yb) \<approx> BValue (nondet_or_val (nondet_not_val xa) ya)"
  apply (simp add: OCLType.cast_eq_def OCLType.cast.simps)
  using implies_val_eq_nondet_or_not_val val_equiv.simps by blast

lemma implies_val_eq_nondet_or_not_val3:
  "(x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   y \<approx> BValue ya \<Longrightarrow>
   BooleanVal (implies_val xb yb) \<approx> BValue (nondet_or_val (nondet_not_val xa) ya)"
  apply (simp add: OCLType.cast_either.simps OCLType.cast_eq_def OCLType.cast.simps)
  using implies_val_eq_nondet_or_not_val val_equiv.simps by blast

lemma not_val_eq_nondet_not_val2:
  "x as BooleanVal xb \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   BooleanVal (not_val xb) \<approx> BValue (nondet_not_val xa)"
  apply (simp add: OCLType.cast_eq_def OCLType.cast.simps)
  using not_val_eq_nondet_not_val val_equiv.simps by blast

lemma not_val_eq_nondet_not_val3:
  "x = BooleanVal xb \<Longrightarrow>
   x \<approx> BValue xa \<Longrightarrow>
   BooleanVal (not_val xb) \<approx> BValue (nondet_not_val xa)"
  apply (simp add: OCLType.cast_eq_def OCLType.cast.simps)
  using not_val_eq_nondet_not_val val_equiv.simps by blast

lemma ocl_cast_either_elim:
  "(a :: OCLType.val, b) as* (x, y) \<Longrightarrow>
   (a = x \<Longrightarrow> b as y \<Longrightarrow> P) \<Longrightarrow>
   (a as x \<Longrightarrow> b = y \<Longrightarrow> P) \<Longrightarrow> P"
  using OCLType.cast_either.simps OCLType.cast_eq_def by auto

lemma xpath_cast_either_elim:
  "(a :: XPathType.val, b) as* (x, y) \<Longrightarrow>
   (a = x \<Longrightarrow> b as y \<Longrightarrow> P) \<Longrightarrow>
   (a as x \<Longrightarrow> b = y \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma cast_equiv_vals:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (an, bn) \<Longrightarrow>
   (x, y) as* (xn, yn) \<Longrightarrow>
   ocl_eq an bn \<Longrightarrow>
   xpath_eq xn yn \<Longrightarrow>
   an \<approx> xn \<and> bn \<approx> yn"
  apply (erule ocl_cast_either_elim; erule xpath_cast_either_elim;
         auto simp add: OCLType.cast_eq_def XPathType.cast_eq_def XPathType.cast.simps;
         erule val_equiv.cases;
         auto simp add: XPathType.cast.simps;
         erule val_equiv.cases;
         auto simp add: OCLType.cast.simps val_equiv.simps;
         erule ocl_eq.cases;
         auto simp add: xpath_eq.simps)
  done

lemma cast_real_decimal:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (RealVal an, RealVal bn) \<Longrightarrow>
   (x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   RealVal an \<approx> DValue xn \<and> RealVal bn \<approx> DValue yn"
  by (meson cast_equiv_vals ocl_eq.intros(3) xpath_eq.intros(3))

thm OCLType.type_of_pair_less_eq

lemma ocl_type_of_pair_less_eq_elim:
  "(x :: OCLType.val, y) as* (a, b) \<Longrightarrow> (\<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b \<Longrightarrow> P) \<Longrightarrow> P"
  using OCLType.type_of_pair_less_eq by auto

lemma ocl_type_of_pair_eq_elim:
  "(x :: OCLType.val, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   (\<T> x \<squnion> \<T> y = \<tau> \<Longrightarrow> P) \<Longrightarrow>
   P"
  using OCLType.type_of_pair_eq by auto

lemma xpath_type_of_pair_less_eq_elim:
  "(x :: XPathType.val, y) as* (a, b) \<Longrightarrow> (\<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b \<Longrightarrow> P) \<Longrightarrow> P"
  using XPathType.type_of_pair_less_eq by auto

lemma xpath_type_of_pair_eq_elim:
  "(x :: XPathType.val, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   (\<T> x \<squnion> \<T> y = \<tau> \<Longrightarrow> P) \<Longrightarrow>
   P"
  using XPathType.type_of_pair_eq by auto

lemma val_equiv_to_type_equiv_elim:
  "x \<approx> y \<Longrightarrow> (\<T> x \<sim> \<T> y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: e22)
(*
lemma q:
  "t \<sim> s \<Longrightarrow>
   t \<le> RealType \<Longrightarrow>
   s \<le> XS_integer \<Longrightarrow> False"
*)
(*
lemma q:
  "a \<sim> x \<Longrightarrow>
   b \<sim> y \<Longrightarrow>
   a \<squnion> b = t \<Longrightarrow>
   x \<squnion> y = s \<Longrightarrow>
   t < AnyType \<Longrightarrow>
   s < XS_anyType \<Longrightarrow>
   t \<sim> s"
  apply (induct rule: type_equiv.induct; induct rule: type_equiv.induct; auto)
  apply (simp add: type_equiv.simps)
(*  apply (cases a; cases b; cases x; cases y; auto)*)
*)

lemma type_sup_equiv_elim:
  "a \<squnion> b = t \<Longrightarrow> x \<squnion> y = s \<Longrightarrow> a \<sim> x \<Longrightarrow> b \<sim> y \<Longrightarrow> t < AnyType \<Longrightarrow>
   (t \<sim> s \<Longrightarrow> P) \<Longrightarrow> P"
  using type_sup_equiv by blast

lemma type_sup_equiv_elim2:
  "a \<squnion> b = t \<and>
   x \<squnion> y = s \<and>
   a \<sim> x \<and> b \<sim> y \<Longrightarrow> t < AnyType \<Longrightarrow> (t \<sim> s \<Longrightarrow> P) \<Longrightarrow> P"
  using type_sup_equiv by blast
(*
lemma q:
  "A1 \<Longrightarrow> A2 \<Longrightarrow> (A1 \<and> A2 \<Longrightarrow> P) \<Longrightarrow> P"
  by simp
*)
thm type_sup_equivE

lemma cast_real_integer:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   (x, y) as* (IValue xna, IValue yna) \<Longrightarrow>
   False"
  apply (erule ocl_type_of_pair_eq_elim)
  apply (simp)
  apply (simp)
  apply (erule xpath_type_of_pair_eq_elim)
  apply (simp)
  apply (simp)
  apply (erule val_equiv_to_type_equiv_elim)
  apply (erule val_equiv_to_type_equiv_elim)
  (*apply (erule_tac a="\<T> a" and x="\<T> x" and b="\<T> b" and y="\<T> y" in type_sup_equivE)
  apply (erule type_sup_equivE)
  apply (erule type_sup_equiv_elim2)*)
  by (metis OCLType.type.distinct(31) XPathType.sup_ge1_type num_type_cases3 option.sel
            sup.idem sup_ge2 xpath_to_ocl_type.simps(2) xpath_to_ocl_type_eq_type_equiv)
(*  by (meson cast_equiv_vals val_equiv.simps ocl_eq.intros(3) xpath_eq.intros(2)
            OCLType.val.distinct(19) XPathType.val.distinct(2) XPathType.val.distinct(7))*)

thm ocl_cast_either_elim ocl_to_xpath_val.simps(2)
            ocl_to_xpath_val_eq_value_equiv option.simps(3)

lemma cast_integer_decimal:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (IntegerVal an, IntegerVal bn) \<Longrightarrow>
   (x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   False"
  apply (erule ocl_type_of_pair_eq_elim)
  apply (simp)
  apply (simp)
  apply (erule xpath_type_of_pair_eq_elim)
  apply (simp)
  apply (simp)
  apply (erule val_equiv_to_type_equiv_elim)
  apply (erule val_equiv_to_type_equiv_elim)
  by (metis OCLType.less_type.simps(19) OCLType.less_type.simps(27)
            OCLType.less_type.simps(28) XPathType.type.distinct(61)
            sup.idem sup.strict_boundedE type_equiv.simps)
(*  by (metis ocl_cast_either_elim ocl_to_xpath_val.simps(2)
            ocl_to_xpath_val_eq_value_equiv option.simps(3))*)
(*  by (metis OCLType.val.distinct(19) XPathType.val.distinct(7) XPathType.val.simps(8)
            cast_equiv_vals ocl_eq.intros(4) val_equiv.cases xpath_eq.intros(3))*)

lemma cast_integer_integer:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (IntegerVal an, IntegerVal bn) \<Longrightarrow>
   (x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   IntegerVal an \<approx> IValue xn \<and> IntegerVal bn \<approx> IValue yn"
  by (meson cast_equiv_vals ocl_eq.intros(4) xpath_eq.intros(2))

lemma cast_unlim_nat_decimal:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   (x, y) as* (DValue xna, DValue yna) \<Longrightarrow>
   False"
  by (metis ocl_cast_either_elim ocl_to_xpath_val.simps(6)
            ocl_to_xpath_val_eq_value_equiv option.simps(3))

lemma cast_unlim_nat_integer:
  "a \<approx> x \<Longrightarrow>
   b \<approx> y \<Longrightarrow>
   (a, b) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   (x, y) as* (IValue xna, IValue yna) \<Longrightarrow>
   False"
  by (metis ocl_cast_either_elim ocl_to_xpath_val.simps(6)
            ocl_to_xpath_val_eq_value_equiv option.simps(3))

lemma real_plus_val_is_strict:
  "\<exists>z. real_plus_val (Just xn) (Just yn) = Just z"
  by simp

lemma integer_plus_val_is_strict:
  "\<exists>z. integer_plus_val (Just xn) (Just yn) = Just z"
  by simp

lemma unlim_nat_plus_val_is_strict:
  "xn \<noteq> \<infinity> \<Longrightarrow> yn \<noteq> \<infinity> \<Longrightarrow>
   \<exists>z. unlim_nat_plus_val (Just xn) (Just yn) = Just z"
  using unlim_nat_plus_val.simps(3) by blast

lemma decimal_add_val_is_strict:
  "\<exists>z. decimal_add_val (Some xn) (Some yn) = Some z"
  by simp

lemma integer_add_val_is_strict:
  "\<exists>z. integer_add_val (Some xn) (Some yn) = Some z"
  by simp

lemma plus_real_decimal:
  "RealVal an \<approx> DValue xn \<Longrightarrow>
   RealVal bn \<approx> DValue yn \<Longrightarrow>
   RealVal (real_plus_val an bn) \<approx> DValue (decimal_add_val xn yn)"
  by (erule val_equiv.cases; erule val_equiv.cases; simp add: val_equiv.intros(3))

lemma plus_integer_integer:
  "IntegerVal an \<approx> IValue xn \<Longrightarrow>
   IntegerVal bn \<approx> IValue yn \<Longrightarrow>
   IntegerVal (integer_plus_val an bn) \<approx> IValue (integer_add_val xn yn)"
  by (erule val_equiv.cases; erule val_equiv.cases; simp add: val_equiv.intros(2))

lemma divide_real_decimal:
  "RealVal an \<approx> DValue xn \<Longrightarrow>
   RealVal bn \<approx> DValue yn \<Longrightarrow>
   bn \<noteq> Just 0 \<or> yn \<noteq> Some 0 \<Longrightarrow>
   RealVal (real_divide_val an bn) \<approx> DValue (decimal_divide_val xn yn)"
  by (erule val_equiv.cases; erule val_equiv.cases; simp add: val_equiv.intros(3))

lemma divide_integer_integer:
  "IntegerVal an \<approx> IValue xn \<Longrightarrow>
   IntegerVal bn \<approx> IValue yn \<Longrightarrow>
   bn \<noteq> Just 0 \<or> yn \<noteq> Some 0 \<Longrightarrow>
   RealVal (OCL.integer_divide_val an bn) \<approx> DValue (XPath.integer_divide_val xn yn)"
  by (erule val_equiv.cases; erule val_equiv.cases; simp add: val_equiv.intros(3))

lemma less_real_decimal:
  "RealVal an \<approx> DValue xn \<Longrightarrow>
   RealVal bn \<approx> DValue yn \<Longrightarrow>
   BooleanVal (real_less_val an bn) \<approx> BValue (decimal_less_than xn yn)"
  by (erule val_equiv.cases; erule val_equiv.cases; simp add: val_equiv.intros(1))

lemma less_integer_integer:
  "IntegerVal an \<approx> IValue xn \<Longrightarrow>
   IntegerVal bn \<approx> IValue yn \<Longrightarrow>
   BooleanVal (integer_less_val an bn) \<approx> BValue (integer_less_than xn yn)"
  by (erule val_equiv.cases; erule val_equiv.cases; simp add: val_equiv.intros(1))
(*
lemma t11 [iff]:
  "(OCLType.type_of_val v = BooleanType) =
   (\<exists>x. v = BooleanVal x)"
  using type_of_boolean_val_eq by fastforce

lemma t12 [iff]:
  "(XPathType.type_of_val v = XS_boolean) =
   (\<exists>x. v = BValue x)"
  using BooleanVal_exists by fastforce
*)

(****************************************** Lemma 4 **********************************************)

lemma s11:
  "ocl_has_safe_div env\<^sub>F (OCL.exp.Let var init\<^sub>F body\<^sub>F) \<Longrightarrow>
   \<exists>v. ocl_has_safe_div env\<^sub>F init\<^sub>F \<and> ocl_has_safe_div (env\<^sub>F(var\<mapsto>v)) body\<^sub>F"
  by auto
(*
lemma s12:
  "xpath_has_safe_div env\<^sub>F (XPath.exp.Let var init\<^sub>F body\<^sub>F) \<Longrightarrow>
   \<exists>v. xpath_has_safe_div env\<^sub>F init\<^sub>F \<and> xpath_has_safe_div (env\<^sub>F(var\<mapsto>v)) body\<^sub>F"
  by auto
*)
(* TODO Доказывать это как-то через типы.
        Тип выражения определяет возможные значения.
        Но для пустых значений это не выполняется, типа недостаточно.
        Посмотреть почему так просто доказано для логических операций *)
lemma ocl_to_xpath_preserve_semantics2:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<Longrightarrow>
   (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B \<Longrightarrow>
   ocl_has_safe_div env\<^sub>F exp\<^sub>F \<Longrightarrow>
   v\<^sub>F \<approx> v\<^sub>B"
  apply (induct exp\<^sub>F exp\<^sub>B arbitrary: env\<^sub>F env\<^sub>B v\<^sub>F v\<^sub>B rule: ocl_to_xpath.induct)
  apply (erule OCL.BooleanLiteralE; erule BConstE; simp add: val_equiv.simps)
  apply (erule OCL.IntegerLiteralE; erule IConstE; simp add: val_equiv.simps)
  apply (erule OCL.RealLiteralE; erule DConstE; simp add: val_equiv.simps)
  apply (erule OCL.LetE; erule XPath.LetE)
  apply (metis OCL.big_step_is_fun ocl_has_safe_div_LetE s10)
  (*apply (smt fun_upd_def ocl_to_xpath_env_def ocl_to_xpath_env_ind.intros ocl_to_xpath_env_indE ocl_to_xpath_val_distr)*)
  apply (erule OCL.VarE; erule XPath.VarE)
  using ocl_to_xpath_val_eq_value_equiv apply auto[1]
  apply (erule OCL.AndE; erule XPath.AndE)
  apply (erule ocl_has_safe_div_AndE)
  apply (simp add: and_val_eq_nondet_and_val3)
  apply (erule OCL.OrE; erule XPath.OrE)
  apply (erule ocl_has_safe_div_OrE)
  apply (simp add: or_val_eq_nondet_or_val3)
  apply (erule OCL.ImpliesE; erule XPath.OrE; erule XPath.NotE)
  apply (erule ocl_has_safe_div_ImpliesE)
  apply (simp add: implies_val_eq_nondet_or_not_val3)
  apply (erule OCL.NotE; erule XPath.NotE)
  apply (erule ocl_has_safe_div_NotE)
  apply (simp add: not_val_eq_nondet_not_val3)
  apply (erule OCL.PlusE; erule XPath.PlusE; erule ocl_has_safe_div_PlusE)
  apply (meson cast_real_integer)
  apply (meson cast_real_decimal plus_real_decimal)
  apply (meson cast_integer_integer plus_integer_integer)
  apply (meson cast_integer_decimal)
  apply (meson cast_unlim_nat_integer)
  apply (meson cast_unlim_nat_decimal)
  apply (erule OCL.DivideE; erule XPath.DivideE; erule ocl_has_safe_div_DivideE)
  apply (meson cast_real_integer)
  apply (meson cast_real_integer)
  apply (smt RealDivideVal OCL.big_step_is_fun cast_real_decimal divide_real_decimal)
  apply (meson cast_real_integer)
  apply (meson cast_integer_decimal)
  apply (meson cast_real_integer)
  apply (metis (mono_tags, lifting) IntegerDivideVal OCL.big_step_is_fun cast_integer_integer divide_integer_integer)
  apply (meson cast_integer_decimal)
  apply (meson cast_integer_decimal)
  apply (meson cast_unlim_nat_integer)
  apply (meson cast_unlim_nat_integer)
  apply (meson cast_unlim_nat_decimal)
  apply (meson cast_unlim_nat_decimal)
  apply (erule OCL.LessE; erule XPath.LessE; erule ocl_has_safe_div_LessE)
  apply (meson cast_real_integer)
  apply (meson cast_real_decimal less_real_decimal)
  apply (meson cast_integer_integer less_integer_integer)
  apply (meson cast_integer_decimal)
  apply (meson cast_unlim_nat_integer)
  apply (meson cast_unlim_nat_decimal)
  done

(****************************************** Lemma 5 **********************************************)

lemma preserve_has_value2:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F = ocl_env_to_tenv env\<^sub>F \<Longrightarrow>
   (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> exp\<^sub>B : \<tau> \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<exists>v\<^sub>B. (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B"
  using XPath.type_system_is_sound e21 preserve_good_env2 by auto

lemma preserve_has_value22:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F = ocl_env_to_tenv env\<^sub>F \<Longrightarrow>
   (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<exists>v\<^sub>B. (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B"
  by (meson OCL.type_system_is_complete e21 preserve_has_type2 preserve_has_value2)

lemma preserve_has_value:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<exists>v\<^sub>B. (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B"
  by (smt e24 i11 ocl_tenv_is_safe_def ocl_to_xpath_tenv_ind.intros preserve_has_value22)

(*
values "{t. (OCL.And (OCL.Var ''x'') (OCL.BooleanLiteral True)) \<leadsto> t}"
values "{t. (OCL.And (OCL.Var ''x'') (OCL.BooleanLiteral True), [''x''\<mapsto>OCLType.BooleanVal Void]) \<Rightarrow> t}"
*)
lemma preserve_has_value3:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B \<Longrightarrow>
   \<exists>v\<^sub>B. (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B"
  by (meson XPath.type_system_is_sound preserve_has_type)

lemma preserve_has_value4:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   ocl_has_safe_div env\<^sub>F exp\<^sub>F \<Longrightarrow>
   env\<^sub>F \<approx>2 env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B \<Longrightarrow>
   \<exists>v\<^sub>F v\<^sub>B. (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<and> (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B \<and> v\<^sub>F \<approx> v\<^sub>B"
  by (meson OCL.type_system_is_sound ocl_to_xpath_preserve_semantics2 preserve_good_env3 preserve_has_value3 xpath_to_ocl_env_ind_then)

lemma preserve_has_value5:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   xpath_env_is_safe env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B \<Longrightarrow>
   \<exists>env\<^sub>F v\<^sub>F v\<^sub>B.
      \<Gamma>\<^sub>F \<turnstile> env\<^sub>F \<and>
      env\<^sub>F \<approx> env\<^sub>B \<and>
      (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<and>
      (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B \<and>
      (ocl_has_safe_div env\<^sub>F exp\<^sub>F \<longrightarrow> v\<^sub>F \<approx> v\<^sub>B)"
  by (metis OCL.type_system_is_sound e41 preserve_good_env3 preserve_has_value3 preserve_has_value4 xpath_to_ocl_env_ind_then)


values "{t. OCL.And (OCL.Var ''x'') (OCL.BooleanLiteral True) \<leadsto> t}"
values "{t. (OCL.And (OCL.Var ''x'') (OCL.BooleanLiteral True), [''x''\<mapsto>NullVal]) \<Rightarrow> t}"

values "{t. (OCL.Or
              (OCL.Less (OCL.Divide (OCL.IntegerLiteral 1) (OCL.IntegerLiteral 0))
                        (OCL.IntegerLiteral 1))
              (OCL.BooleanLiteral True), Map.empty) \<Rightarrow> t}"

values "{t. (XPath.Or
              (XPath.Less (XPath.Divide (XPath.IConst 1) (XPath.IConst 0))
                          (XPath.IConst 1))
              (XPath.BConst True), Map.empty) \<Rightarrow> t}"

code_pred ocl_has_safe_div .

value "ocl_has_safe_div Map.empty (OCL.Or
              (OCL.Less (OCL.Divide (OCL.IntegerLiteral 1) (OCL.IntegerLiteral 0))
                        (OCL.IntegerLiteral 1))
              (OCL.BooleanLiteral True))"

(*values "{t. (XPath.And (XPath.Var ''x'') (BConst True), [''x''\<mapsto>NullVal]) \<Rightarrow> t}"*)




































(*
lemma preserve_has_value5:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   xpath_env_is_safe env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B \<Longrightarrow>
   \<exists>env\<^sub>F v\<^sub>F v\<^sub>B. \<Gamma>\<^sub>F \<turnstile> env\<^sub>F \<and> env\<^sub>F \<approx> env\<^sub>B \<and>
    (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<and> (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B \<and>
    v\<^sub>F \<approx> v\<^sub>B"
  by (meson e41 preserve_good_env3 preserve_has_value4 xpath_to_ocl_env_ind_then)

lemma s13:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   (exp\<^sub>F, env\<^sub>F) \<Rightarrow> RealVal v\<^sub>F \<Longrightarrow>
   (exp\<^sub>B, env\<^sub>B) \<Rightarrow> DValue v\<^sub>B \<Longrightarrow>
   v\<^sub>F \<noteq> Just 0 \<Longrightarrow>
   v\<^sub>B \<noteq> Some 0"
  by (metis (no_types, lifting) OCLType.val.inject(2) ocl_to_xpath_preserve_semantics2 option.inject val_equiv.intros(3) xpath_to_ocl_val_eq_value_equiv)

lemma s14:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   (exp\<^sub>F, env\<^sub>F) \<Rightarrow> RealVal (Just v\<^sub>F) \<Longrightarrow>
   (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B \<Longrightarrow>
   v\<^sub>F \<noteq> 0 \<Longrightarrow>
   \<exists>v\<^sub>B2. v\<^sub>B = DValue (Some v\<^sub>B2) \<and> v\<^sub>B2 \<noteq> 0"
  by (meson ocl_to_xpath_preserve_semantics2 val_equiv.intros(3) val_equiv_is_fun)

lemma ocl_has_safe_div_then_xpath:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   env\<^sub>F \<approx> env\<^sub>B \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   ocl_has_safe_div env\<^sub>F exp\<^sub>F \<Longrightarrow>
   xpath_has_safe_div env\<^sub>B exp\<^sub>B"
  apply (induct arbitrary: env\<^sub>F env\<^sub>B rule: ocl_to_xpath.induct)
  apply (simp add: xpath_has_safe_div.intros(1))
  apply (simp add: xpath_has_safe_div.intros(2))
  apply (simp add: xpath_has_safe_div.intros(3))
  apply (meson ocl_has_safe_div_LetE LetSupported ocl_to_xpath_preserve_semantics2 preserve_has_value s10 xpath_has_safe_div.intros(4))
  apply (simp add: xpath_has_safe_div.intros(5))
  apply (meson AndSupported ocl_has_safe_div_AndE xpath_has_safe_div.intros(6))
  apply (meson OrSupported ocl_has_safe_div_OrE xpath_has_safe_div.intros(7))
  apply (meson ImpliesSupported ocl_has_safe_div_ImpliesE xpath_has_safe_div.intros(7) xpath_has_safe_div.intros(8))
  apply (meson NotSupported ocl_has_safe_div_NotE xpath_has_safe_div.intros(8))
  apply (meson PlusSupported ocl_has_safe_div_PlusE xpath_has_safe_div.intros(9))
  apply (erule ocl_has_safe_div_DivideE)
  (*apply (metis DivideSupported ocl_has_safe_div_DivideE preserve_has_value s14 xpath_has_safe_div.intros(10))*)
  apply (meson LessSupported ocl_has_safe_div_LessE xpath_has_safe_div.intros(11))
  done

lemma preserve_has_value6:
  "exp\<^sub>F \<leadsto> exp\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<sim> \<Gamma>\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>F \<turnstile> exp\<^sub>F : \<tau>\<^sub>F \<Longrightarrow>
   ocl_is_supported exp\<^sub>F \<Longrightarrow>
   xpath_env_is_safe env\<^sub>B \<Longrightarrow>
   \<Gamma>\<^sub>B \<turnstile> env\<^sub>B \<Longrightarrow>
   \<exists>env\<^sub>F v\<^sub>F v\<^sub>B. \<Gamma>\<^sub>F \<turnstile> env\<^sub>F \<and> env\<^sub>F \<approx> env\<^sub>B \<and>
    (exp\<^sub>F, env\<^sub>F) \<Rightarrow> v\<^sub>F \<and> (exp\<^sub>B, env\<^sub>B) \<Rightarrow> v\<^sub>B \<and>
    v\<^sub>F \<approx> v\<^sub>B \<and> (ocl_has_safe_div env\<^sub>F exp\<^sub>F \<longrightarrow> xpath_has_safe_div env\<^sub>B exp\<^sub>B)"
  by (metis ocl_has_safe_div_then_xpath preserve_has_value5)
*)

inductive has_boolean_val :: "OCLType.type env \<Rightarrow> OCL.exp \<Rightarrow> bool" where
"has_boolean_val \<Gamma> (OCL.BooleanLiteral _)" |
"\<Gamma> \<turnstile> init : \<tau> \<Longrightarrow>
 has_boolean_val (\<Gamma>(var\<mapsto>\<tau>)) body \<Longrightarrow>
 has_boolean_val \<Gamma> (OCL.Let var init body)" |
"(* TODO: Check var *)
 has_boolean_val \<Gamma> (OCL.Var var)" |
"has_boolean_val \<Gamma> a \<Longrightarrow>
 has_boolean_val \<Gamma> b \<Longrightarrow>
 has_boolean_val \<Gamma> (OCL.And a b)" |
"has_boolean_val \<Gamma> a \<Longrightarrow>
 has_boolean_val \<Gamma> b \<Longrightarrow>
 has_boolean_val \<Gamma> (OCL.Or a b)" |
"has_boolean_val \<Gamma> a \<Longrightarrow>
 has_boolean_val \<Gamma> b \<Longrightarrow>
 has_boolean_val \<Gamma> (OCL.Xor a b)" |
"has_boolean_val \<Gamma> a \<Longrightarrow>
 has_boolean_val \<Gamma> b \<Longrightarrow>
 has_boolean_val \<Gamma> (OCL.Implies a b)" |
"has_boolean_val \<Gamma> a \<Longrightarrow>
 has_boolean_val \<Gamma> (OCL.Not a)"

inductive ocl_is_safe :: "OCLType.type env \<Rightarrow> OCL.exp \<Rightarrow> bool" where
(*"ocl_is_safe \<Gamma> (OCL.NullLiteral)" |
"ocl_is_safe \<Gamma> (OCL.BooleanLiteral _)" |
"ocl_is_safe \<Gamma> (OCL.IntegerLiteral _)" |
"ocl_is_safe \<Gamma> init \<Longrightarrow>
 ocl_is_safe \<Gamma> body \<Longrightarrow>
 ocl_is_safe \<Gamma> (OCL.Let var init body)" |
"ocl_is_safe \<Gamma> (OCL.Var var)" |*)
"has_boolean_val \<Gamma> (OCL.And a b) \<Longrightarrow>
(* \<exists>env. \<Gamma> \<turnstile> env \<Longrightarrow>*)
 (OCL.And a b, env) \<Rightarrow> v \<Longrightarrow>
(* v \<noteq> OCLType.BooleanVal OCL.Void \<Longrightarrow>
 v \<noteq> OCLType.BooleanVal OCL.Error \<Longrightarrow>*)
 ocl_is_safe \<Gamma> (OCL.And a b)" |
(*"has_boolean_val \<Gamma> (OCL.Or a b) \<Longrightarrow>
 ocl_is_safe \<Gamma> (OCL.Or a b)" |
"has_boolean_val \<Gamma> (OCL.Xor a b) \<Longrightarrow>
 ocl_is_safe \<Gamma> (OCL.Xor a b)" |
"has_boolean_val \<Gamma> (OCL.Implies a b) \<Longrightarrow>
 ocl_is_safe \<Gamma> (OCL.Implies a b)" |*)
"has_boolean_val \<Gamma> (OCL.Not a) \<Longrightarrow>
 ocl_is_safe \<Gamma> (OCL.Not a)"

code_pred [show_modes] ocl_is_safe .

value "ocl_is_safe Map.empty (OCL.And (OCL.BooleanLiteral True) (OCL.BooleanLiteral False))"




(* Safe typing *)

type_synonym stype = "OCLType.type \<times> bool"

value "False < True"
value "(OCLType.IntegerType, False) < (OCLType.IntegerType, True)"
value "(OCLType.IntegerType, True) < (OCLType.IntegerType, True)"
value "(OCLType.IntegerType, True) < (OCLType.RealType, True)"
value "(OCLType.IntegerType, True) < (OCLType.RealType, False)"
value "(OCLType.IntegerType, False) < (OCLType.RealType, True)"
value "(OCLType.IntegerType, False) \<squnion> (OCLType.RealType, True)"
value "(OCLType.IntegerType, True) \<squnion> (OCLType.RealType, False)"
value "(BooleanType, False) \<squnion> (BooleanType, True)"
value "(VoidType, False) \<squnion> (BooleanType, False)"
value "(VoidType, True) \<squnion> (BooleanType, False)"

definition stenv_to_tenv :: "stype env \<Rightarrow> OCLType.type env" where
  "stenv_to_tenv \<Gamma> \<equiv> (map_option fst) \<circ> \<Gamma>"

definition stenv_to_senv :: "stype env \<Rightarrow> bool env" where
  "stenv_to_senv \<Gamma> \<equiv> (map_option snd) \<circ> \<Gamma>"
(*
inductive ocl_styping :: "stype env \<Rightarrow> OCL.exp \<Rightarrow> stype \<Rightarrow> bool"
(*("(1_/ \<turnstile>s/ (_ :/ _))" [51,51,51] 50)*) where
  "(stenv_to_tenv \<Gamma>) \<turnstile> exp1 : (fst \<tau>) \<Longrightarrow>
   ocl_is_strict_fun (stenv_to_senv \<Gamma>) exp1 \<Longrightarrow>
   ocl_styping \<Gamma> exp1 \<tau>"

definition ocl_styping_fun :: "stype env \<Rightarrow> OCL.exp \<Rightarrow> stype \<Rightarrow> bool"
("(1_/ \<turnstile>s/ (_ :/ _))" [51,51,51] 50) where
  "ocl_styping_fun \<Gamma> exp1 \<tau> \<equiv>
   (stenv_to_tenv \<Gamma>) \<turnstile> exp1 : (fst \<tau>) \<and>
   ocl_is_strict_fun (stenv_to_senv \<Gamma>) exp1"

lemma ocl_styping_eq:
  "ocl_styping_fun \<Gamma> exp1 \<tau> = ocl_styping \<Gamma> exp1 \<tau>"
  by (simp add: ocl_styping.simps ocl_styping_fun_def)
*)

inductive styping2 :: "stype env \<Rightarrow> OCL.exp \<Rightarrow> stype \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50) where
"\<Gamma> \<turnstile> NullLiteral : (VoidType, True)" |
"\<Gamma> \<turnstile> BooleanLiteral c : (BooleanType, False)" |
"\<Gamma> \<turnstile> RealLiteral c : (RealType, False)" |
"\<Gamma> \<turnstile> IntegerLiteral c : (IntegerType, False)" |
"\<Gamma> \<turnstile> UnlimNatLiteral c : (UnlimNatType, c = \<infinity>)" |
"\<Gamma> \<turnstile> StringLiteral c : (StringType, False)" |
"(\<Gamma> :: stype env) \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma>(var\<mapsto>\<tau>\<^sub>1) \<turnstile> body : \<tau> \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.Let var init body : \<tau>" |
"(\<Gamma> :: stype env) var = Some \<tau> \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.Var var : \<tau>" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = \<tau> \<Longrightarrow>
 \<tau> \<le> (BooleanType, True) \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.And a b : \<tau> \<squnion> (BooleanType, False)" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 fst \<tau>\<^sub>1 \<squnion> fst \<tau>\<^sub>2 \<le> BooleanType \<Longrightarrow>
 snd \<tau>\<^sub>1 \<and> snd \<tau>\<^sub>2 = s \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.Or a b : (BooleanType, s)" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 fst \<tau>\<^sub>1 \<squnion> fst \<tau>\<^sub>2 \<le> BooleanType \<Longrightarrow>
 snd \<tau>\<^sub>1 \<and> snd \<tau>\<^sub>2 = s \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.Xor a b : (BooleanType, s)" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 fst \<tau>\<^sub>1 \<squnion> fst \<tau>\<^sub>2 \<le> BooleanType \<Longrightarrow>
 snd \<tau>\<^sub>1 \<and> snd \<tau>\<^sub>2 = s \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.Implies a b : (BooleanType, s)" |
"\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow>
 fst \<tau> \<le> BooleanType \<Longrightarrow>
 snd \<tau> = s \<Longrightarrow>
 \<Gamma> \<turnstile> OCL.Not a : (BooleanType, s)" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = \<tau> \<Longrightarrow>
 \<tau> = (RealType, s) \<Longrightarrow>
 \<Gamma> \<turnstile> Plus a b : \<tau>" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = \<tau> \<Longrightarrow>
 \<tau> = (IntegerType, s) \<Longrightarrow>
 \<Gamma> \<turnstile> Plus a b : \<tau>" |
"\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
 \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
 \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = \<tau> \<Longrightarrow>
 \<tau> = (UnlimNatType, s) \<Longrightarrow>
 \<Gamma> \<turnstile> Plus a b : \<tau>"

inductive_cases NullLiteralTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> NullLiteral : \<tau>"
inductive_cases BooleanLiteralTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> BooleanLiteral c : \<tau>"
inductive_cases RealLiteralTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> RealLiteral c : \<tau>"
inductive_cases IntegerLiteralTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> IntegerLiteral c : \<tau>"
inductive_cases UnlimNatLiteralTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> UnlimNatLiteral c : \<tau>"
inductive_cases StringLiteralTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> StringLiteral c : \<tau>"
inductive_cases LetTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Let var init body : \<tau>"
inductive_cases VarTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Var var : \<tau>"
inductive_cases AndTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.And a b : \<tau>"
inductive_cases OrTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Or a b : \<tau>"
inductive_cases XorTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Xor a b : \<tau>"
inductive_cases ImpliesTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Implies a b : \<tau>"
inductive_cases NotTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Not a : \<tau>"
inductive_cases PlusTE2[elim!]: "(\<Gamma> :: stype env) \<turnstile> OCL.Plus a b : \<tau>"

thm styping2.induct
(*
lemma t11:
  "ocl_is_supported_fun (OCL.Let var init body) \<Longrightarrow>
   ocl_is_supported_fun init \<and>
   ocl_is_supported_fun body"
  by simp

lemma t12:
  "ocl_is_strict_fun (stenv_to_senv \<Gamma>\<^sub>F) (OCL.Let var init body) \<Longrightarrow>
   ocl_is_strict_fun (stenv_to_senv \<Gamma>\<^sub>F) init = s \<Longrightarrow>
   s \<and> ocl_is_strict_fun ((stenv_to_senv \<Gamma>\<^sub>F)(var\<mapsto>s)) body"
  by auto

lemma t13:
  "(\<Gamma>\<^sub>F :: stype env) \<turnstile> OCL.Let var init body : \<tau> \<Longrightarrow>
   \<exists>\<tau>\<^sub>1. \<Gamma>\<^sub>F \<turnstile> init : \<tau>\<^sub>1 \<and>
   \<Gamma>\<^sub>F(var \<mapsto> \<tau>\<^sub>1) \<turnstile> body : \<tau>"
  by auto

lemma t14:
  "\<Gamma>\<^sub>F \<turnstile> exp1 : \<tau> \<Longrightarrow>
   \<exists>a b. \<Gamma>\<^sub>F \<turnstile> exp1 : (a, b)"
  by (metis prod.collapse)

lemma t15:
  "\<Gamma>\<^sub>F \<turnstile> OCL.Let var init body : \<tau> \<Longrightarrow>
   \<exists>c d. \<Gamma>\<^sub>F \<turnstile> init : (c, d) \<and>
   \<Gamma>\<^sub>F(var \<mapsto> (c, d)) \<turnstile> body : \<tau>"
  by auto
*)
lemma t16:
  "\<Gamma>\<^sub>F \<turnstile> OCL.Let var init body : (a, b) \<Longrightarrow>
   \<exists>c d. \<Gamma>\<^sub>F \<turnstile> init : (c, d) \<and>
   \<Gamma>\<^sub>F(var \<mapsto> (c, d)) \<turnstile> body : (a, b)"
  by auto

lemma styping2_is_fun:
  "(\<Gamma> :: stype env) \<turnstile> exp1 : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> exp1 : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (induct \<Gamma> exp1 \<tau>\<^sub>1 arbitrary: \<tau>\<^sub>2 rule: styping2.induct)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply auto[1]
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  done

lemma stenv_to_tenv_distr:
  "(stenv_to_tenv \<Gamma>)(var \<mapsto> fst \<tau>) =
   stenv_to_tenv (\<Gamma>(var \<mapsto> \<tau>))"
  by (simp add: stenv_to_tenv_def)

lemma styping2_eq_typing:
  "\<Gamma>2 = stenv_to_tenv \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> exp1 : (\<tau>\<^sub>1, s) \<Longrightarrow>
   \<Gamma>2 \<turnstile> exp1 : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (induct exp1 arbitrary: \<Gamma> \<Gamma>2 \<tau>\<^sub>1 \<tau>\<^sub>2 s)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply (erule OCL.LetTE; erule LetTE2;
         metis prod.collapse stenv_to_tenv_distr)
  apply (erule OCL.VarTE; erule VarTE2;
         metis fst_conv fun_upd_same fun_upd_triv option.inject stenv_to_tenv_distr)
  apply (auto simp: le_iff_sup)[1]
  apply (auto simp: le_iff_sup)[1]
  apply (auto simp: le_iff_sup)[1]
  apply auto[1]
  apply auto[1]
  apply fastforce
  done


values "{t. (OCL.Or (OCL.Less
          (OCL.Divide (OCL.IntegerLiteral 1) (OCL.IntegerLiteral 0))
          (OCL.IntegerLiteral 1)) (OCL.BooleanLiteral True), Map.empty) \<Rightarrow> t}"

values "{t. (OCL.Or (OCL.Less
          (OCL.Divide (OCL.IntegerLiteral 1) (OCL.IntegerLiteral 0))
          (OCL.IntegerLiteral 1)) (OCL.BooleanLiteral True)) \<leadsto> t}"

values "{t. (OCL.Or (OCL.Var ''x'') (OCL.BooleanLiteral True)) \<leadsto> t}"

code_pred [show_modes] XPath.big_step .

values "{t. (OCL.Or (OCL.Var ''x'') (OCL.BooleanLiteral True), [''x''\<mapsto>BooleanVal OCL.Error]) \<Rightarrow> t}"
values "{t. (XPath.Or (XPath.exp.Var ''x'') (BConst True), [''x''\<mapsto>BValue XPath.Error]) \<Rightarrow> t}"

values "{t. (OCL.Divide (OCL.IntegerLiteral 1) (OCL.IntegerLiteral 0), Map.empty) \<Rightarrow> t}"
values "{t. (XPath.exp.Divide (IConst 1) (IConst 0), Map.empty) \<Rightarrow> t}"

values "{t. (OCL.Or (OCL.Less
          (OCL.Divide (OCL.IntegerLiteral 1) (OCL.IntegerLiteral 0))
          (OCL.IntegerLiteral 1)) (OCL.BooleanLiteral True), Map.empty) \<Rightarrow> t}"
values "{t. (XPath.exp.Or (XPath.exp.Less (XPath.exp.Divide (IConst 1) (IConst 0)) (IConst 1)) (BConst True), Map.empty) \<Rightarrow> t}"

value "BooleanVal (Just True) \<approx> BValue (Maybe True)"

end

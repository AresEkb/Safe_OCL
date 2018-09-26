theory XPath
  imports Complex_Main ProgLang XPathType
begin
(*
no_notation ProgLang.big_step (infix "\<Rightarrow>" 55)
no_notation ProgLang.typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
no_notation ProgLang.etyping (infix "\<turnstile>" 50)
*)

(*** Syntax *****************************************************************************)

(* Описываем абстрактный синтаксис XPath (допустимые выражения) *)

datatype exp =
  BConst bool
| IConst int
| DConst real
| Let vname exp exp
| Var vname
| And exp exp
| Or exp exp
| Not exp
| Plus exp exp
| Divide exp exp
| Less exp exp

(*** Typing *****************************************************************************)

(* Определяем для выражений типы *)

inductive typing :: "type env \<Rightarrow> exp \<Rightarrow> type \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50) where
 BConstT:
  "\<Gamma> \<turnstile> BConst c : XS_boolean"
|IConstT:
  "\<Gamma> \<turnstile> IConst c : XS_integer"
|DConstT:
  "\<Gamma> \<turnstile> DConst c : XS_decimal"
|LetT:
  "\<Gamma> \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma>(var\<mapsto>\<tau>\<^sub>1) \<turnstile> body : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> Let var init body : \<tau>"
|VarT:
  "\<Gamma> var = Some \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> Var var : \<tau>"
|AndT:
  (* TODO: Operands must be normalized to fn:boolean(...) *)
  "\<Gamma> \<turnstile> a : XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> b : XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> And a b : XS_boolean"
|OrT:
  "\<Gamma> \<turnstile> a : XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> b : XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> Or a b : XS_boolean"
|NotT:
  "\<Gamma> \<turnstile> a : XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> Not a : XS_boolean"
|IntegerPlusT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_integer \<Longrightarrow>
   \<Gamma> \<turnstile> Plus a b : XS_integer"
|DecimalPlusT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_decimal \<Longrightarrow>
   \<Gamma> \<turnstile> Plus a b : XS_decimal"
|DivideT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> XS_decimal \<Longrightarrow>
   \<Gamma> \<turnstile> Divide a b : XS_decimal"
|LessT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> XS_decimal \<Longrightarrow>
   \<Gamma> \<turnstile> Less a b : XS_boolean"

inductive_cases BConstTE[elim!]: "\<Gamma> \<turnstile> BConst c : \<tau>"
inductive_cases IConstTE[elim!]: "\<Gamma> \<turnstile> IConst c : \<tau>"
inductive_cases DConstTE[elim!]: "\<Gamma> \<turnstile> DConst c : \<tau>"
inductive_cases LetTE[elim!]: "\<Gamma> \<turnstile> Let var init body : \<tau>"
inductive_cases VarTE[elim!]: "\<Gamma> \<turnstile> Var var : \<tau>"
inductive_cases AndTE[elim!]: "\<Gamma> \<turnstile> And a b : \<tau>"
inductive_cases AndTE2[elim!]: "\<Gamma> \<turnstile> And a b : XS_boolean"
inductive_cases OrTE[elim!]: "\<Gamma> \<turnstile> Or a b : \<tau>"
inductive_cases NotTE[elim!]: "\<Gamma> \<turnstile> Not a : \<tau>"
inductive_cases PlusTE[elim!]: "\<Gamma> \<turnstile> Plus a b : \<tau>"
inductive_cases DivideTE[elim!]: "\<Gamma> \<turnstile> Divide a b : \<tau>"
inductive_cases LessTE[elim!]: "\<Gamma> \<turnstile> Less a b : \<tau>"

(* Доказываем, что если выражение имеет тип, то он детерминирован *)

lemma typing_is_fun:
  "\<Gamma> \<turnstile> exp1 : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> exp1 : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (induct \<Gamma> exp1 \<tau>\<^sub>1 arbitrary: \<tau>\<^sub>2 rule: typing.induct)
  apply blast
  apply blast
  apply blast
  apply blast
  apply fastforce
  apply force
  apply force
  apply force
  apply fastforce
  apply fastforce
  apply force
  apply force
  done

(*** Semantics **************************************************************************)

(* Описываем семантику XPath выражений: какое значение они возвращают.
   Для индуктивных определений проще доказывать теоремы.
   Но видимо тут всё-таки удобней функции *)

fun nondet_and_val :: "nbool \<Rightarrow> nbool \<Rightarrow> nbool" where
  "nondet_and_val (Maybe False) _ = Maybe False"
| "nondet_and_val _ (Maybe False) = Maybe False"
| "nondet_and_val Error (Only False) = Maybe False"
| "nondet_and_val (Only False) Error = Maybe False"
| "nondet_and_val Error _ = Error"
| "nondet_and_val _ Error = Error"
| "nondet_and_val (Maybe True) _ = Maybe True"
| "nondet_and_val _ (Maybe True) = Maybe True"
| "nondet_and_val (Only a) (Only b) = Only (a \<and> b)"

fun nondet_or_val :: "nbool \<Rightarrow> nbool \<Rightarrow> nbool" where
  "nondet_or_val (Maybe True) _ = Maybe True"
| "nondet_or_val _ (Maybe True) = Maybe True"
| "nondet_or_val Error (Only True) = Maybe True"
| "nondet_or_val (Only True) Error = Maybe True"
| "nondet_or_val Error _ = Error"
| "nondet_or_val _ Error = Error"
| "nondet_or_val (Maybe False) _ = Maybe False"
| "nondet_or_val _ (Maybe False) = Maybe False"
| "nondet_or_val (Only a) (Only b) = Only (a \<or> b)"

fun nondet_not_val :: "nbool \<Rightarrow> nbool" where
  "nondet_not_val (Maybe a) = Maybe (\<not>a)"
| "nondet_not_val (Only a) = Only (\<not>a)"
| "nondet_not_val Error = Error"

fun integer_add_val :: "oint \<Rightarrow> oint \<Rightarrow> oint" where
  "integer_add_val (Some a) (Some b) = Some (a + b)"
| "integer_add_val _ _ = None"

fun decimal_add_val :: "oreal \<Rightarrow> oreal \<Rightarrow> oreal" where
  "decimal_add_val (Some a) (Some b) = Some (a + b)"
| "decimal_add_val _ _ = None"

fun integer_divide_val :: "oint \<Rightarrow> oint \<Rightarrow> oreal" where
  "integer_divide_val (Some a) (Some b) = (if b = 0 then None else Some (a / b))"
| "integer_divide_val _ _ = None"

fun decimal_divide_val :: "oreal \<Rightarrow> oreal \<Rightarrow> oreal" where
  "decimal_divide_val (Some a) (Some b) = (if b = 0 then None else Some (a / b))"
| "decimal_divide_val _ _ = None"

fun integer_less_than :: "oint \<Rightarrow> oint \<Rightarrow> nbool" where
  "integer_less_than (Some a) (Some b) = Only (a < b)"
| "integer_less_than _ _ = Error"

fun decimal_less_than :: "oreal \<Rightarrow> oreal \<Rightarrow> nbool" where
  "decimal_less_than (Some a) (Some b) = Only (a < b)"
| "decimal_less_than _ _ = Error"

(* Тут уже точно без индукции было бы проблематично.
   TODO: Вспомнить чем big-step отличается от small-step.
   Вроде в small-step идет постепенное упрощение выражения,
   а тут мы сразу определяем результат *)

inductive big_step :: "exp \<times> val env \<Rightarrow> val \<Rightarrow> bool"
  (infix "\<Rightarrow>" 55) where
  "(BConst c, e) \<Rightarrow> BValue (Only c)"
|
  "(IConst c, e) \<Rightarrow> IValue (Some c)"
|
  "(DConst c, e) \<Rightarrow> DValue (Some c)"
|
  "(init, e) \<Rightarrow> x \<Longrightarrow>
   (body, e(var\<mapsto>x)) \<Rightarrow> v \<Longrightarrow>
   (Let var init body, e) \<Rightarrow> v"
|
  "e var = Some v \<Longrightarrow>
   (Var var, e) \<Rightarrow> v"
|
  "(a, e) \<Rightarrow> BValue x \<Longrightarrow>
   (b, e) \<Rightarrow> BValue y \<Longrightarrow>
   (And a b, e) \<Rightarrow> BValue (nondet_and_val x y)"
|
  "(a, e) \<Rightarrow> BValue x \<Longrightarrow>
   (b, e) \<Rightarrow> BValue y \<Longrightarrow>
   (Or a b, e) \<Rightarrow> BValue (nondet_or_val x y)"
|
  "(a, e) \<Rightarrow> BValue x \<Longrightarrow>
   (Not a, e) \<Rightarrow> BValue (nondet_not_val x)"
|
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
(* x as IValue xn \<Longrightarrow>
 y as IValue yn \<Longrightarrow>*)
   (x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   (Plus a b, e) \<Rightarrow> IValue (integer_add_val xn yn)"
|
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   (Plus a b, e) \<Rightarrow> DValue (decimal_add_val xn yn)"
|
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   (Divide a b, e) \<Rightarrow> DValue (integer_divide_val xn yn)"
|
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   (Divide a b, e) \<Rightarrow> DValue (decimal_divide_val xn yn)"
|
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
(* x as IValue xn \<Longrightarrow>
 y as IValue yn \<Longrightarrow>*)
   (x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   (Less a b, e) \<Rightarrow> BValue (integer_less_than xn yn)"
|
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   (Less a b, e) \<Rightarrow> BValue (decimal_less_than xn yn)"

inductive_cases BConstE[elim!]: "(BConst c, e) \<Rightarrow> v"
inductive_cases IConstE[elim!]: "(IConst c, e) \<Rightarrow> v"
inductive_cases DConstE[elim!]: "(DConst c, e) \<Rightarrow> v"
inductive_cases LetE[elim!]: "(Let var init body, e) \<Rightarrow> v"
inductive_cases VarE[elim!]: "(Var var, e) \<Rightarrow> v"
inductive_cases AndE[elim!]: "(And a b, e) \<Rightarrow> v"
inductive_cases OrE[elim!]: "(Or a b, e) \<Rightarrow> v"
inductive_cases NotE[elim!]: "(Not a, e) \<Rightarrow> v"
inductive_cases PlusE[elim!]: "(Plus a b, e) \<Rightarrow> v"
inductive_cases DivideE[elim!]: "(Divide a b, e) \<Rightarrow> v"
inductive_cases LessE[elim!]: "(Less a b, e) \<Rightarrow> v"

(* Доказываем, что семантика детерминирована. На самом деле нет,
   но недетерминированность мы описали с помощью типа nondet *)

lemma big_step_is_fun:
  "(exp1, env) \<Rightarrow> v\<^sub>1 \<Longrightarrow>
   (exp1, env) \<Rightarrow> v\<^sub>2 \<Longrightarrow>
   v\<^sub>1 = v\<^sub>2"
  apply (induct arbitrary: v\<^sub>2 rule: big_step.induct)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply blast
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (erule PlusE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule PlusE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule DivideE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule DivideE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule LessE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule LessE; auto simp: cast.simps cast_eq_def cast_either.simps)
  done


(* Environment Typing *)
(*
fun type_of_val :: "val \<Rightarrow> type" where
  "type_of_val (BValue _) = XS_boolean"
| "type_of_val (IValue _) = XS_integer"
| "type_of_val (DValue _) = XS_decimal"
| "type_of_val (NNIValue _) = XS_nonNegativeInteger"

fun val_of_type :: "type \<Rightarrow> val" where
  "val_of_type XS_anyType = BValue (Only False)"
| "val_of_type XS_boolean = BValue (Only False)"
| "val_of_type XS_integer = IValue (Some 0)"
| "val_of_type XS_decimal = DValue (Some 0)"
| "val_of_type XS_nonNegativeInteger = NNIValue (Some 0)"
*)
definition default_tenv :: "val env \<Rightarrow> type env" where
  "default_tenv env \<equiv> (map_option type_of_val) \<circ> env"
(*
definition default_env :: "type env \<Rightarrow> val env" where
  "default_env \<Gamma> \<equiv> (map_option val_of_type) \<circ> \<Gamma>"
*)
definition etyping :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> env \<equiv> \<forall>x. (case (env x, \<Gamma> x) of
    (Some v, Some t) \<Rightarrow> type_of_val v = t |
    (None, None) \<Rightarrow> True |
    _ \<Rightarrow> False)"

definition etyping1 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>1" 50)  where
  "\<Gamma> \<turnstile>1 env \<equiv> \<forall>x. the ((map_option type_of_val) (env x)) = the (\<Gamma> x)"

(* Если переменная имеет тип в окружении \<Gamma>, то она имеет значение в любом env,
   которое соответствует \<Gamma> *)

lemma var_has_type_impies_has_value:
  "\<Gamma> var = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>v. env var = Some v"
  by (smt etyping_def old.prod.case option.case_eq_if option.collapse option.distinct(1))

(* Обратная теорема *)

lemma var_has_value_impies_has_type:
  "env var = Some v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>\<tau>. \<Gamma> var = Some \<tau>"
  by (smt etyping_def old.prod.case option.case_eq_if option.distinct(1) option.expand option.sel)

lemma etyping2_eq1:
  "etyping \<Gamma> env \<Longrightarrow> etyping1 \<Gamma> env"
  by (smt etyping1_def etyping_def less_eq_type_def old.prod.case option.case_eq_if option.map_disc_iff option.map_sel)

lemma default_tenv_exists:
  "default_tenv env \<turnstile> env"
  by (simp add: default_tenv_def etyping_def option.case_eq_if option.map_sel)
(*
lemma default_env_exists:
  "\<Gamma> \<turnstile> default_env \<Gamma>"
  by (smt comp_apply default_env_def eq_iff etyping_def less_type.simps(2) map_option_is_None old.prod.case option.case_eq_if option.map_sel subtype_strict_eq_subtype type.exhaust type_of_val.simps(1) type_of_val.simps(2) val_of_type.simps(1) val_of_type.simps(2) val_of_type.simps(3))
*)
(*
definition etyping0 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>0" 50) where
  "\<Gamma> \<turnstile>0 env \<equiv> \<forall>x. \<exists>v t. env x = Some v \<and> \<Gamma> x = Some t \<and> type_of_val v <: t"

definition etyping2 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>2" 50) where
  "\<Gamma> \<turnstile>2 env \<equiv> \<forall>x. \<exists>v t. env x = Some v \<and> \<Gamma> x = Some t \<longleftrightarrow> type_of_val v <: t"

definition etyping3 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>3" 50) where
  "\<Gamma> \<turnstile>3 env \<equiv> \<forall>x. (case (env x, \<Gamma> x) of (Some v, Some t) \<Rightarrow> type_of_val v <: t | _ \<Rightarrow> False)"

definition etyping4 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>4" 50) where
  "\<Gamma> \<turnstile>4 env \<equiv> \<forall>x. (case (env x, \<Gamma> x) of (Some v, Some t) \<Rightarrow> type_of_val v <: t | _ \<Rightarrow> True)"

definition etyping5 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>5" 50) where
  "\<Gamma> \<turnstile>5 env \<equiv> \<forall>x. \<exists>v t. env x = Some v \<and> \<Gamma> x = Some t \<longrightarrow> type_of_val v <: t"

lemma var_has_type_impies_has_value0:
  "\<Gamma> var = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile>0 env \<Longrightarrow> \<exists>v. env var = Some v"
  using etyping0_def by blast

lemma var_has_value_impies_has_type0:
  "env var = Some v \<Longrightarrow> \<Gamma> \<turnstile>0 env \<Longrightarrow> \<exists>\<tau>. \<Gamma> var = Some \<tau>"
  using etyping0_def by blast

lemma etyping2_eq2:
  "etyping0 \<Gamma> env \<Longrightarrow> etyping2 \<Gamma> env"
  by (meson etyping2_def etyping0_def)

lemma etyping3_eq1:
  "etyping0 \<Gamma> env = etyping3 \<Gamma> env"
  by (smt etyping3_def etyping0_def option.case_eq_if option.exhaust_sel option.simps(5) prod.simps(2))

lemma etyping4_eq1:
  "etyping0 \<Gamma> env \<Longrightarrow> etyping4 \<Gamma> env"
  by (smt etyping1_def etyping2_eq1 etyping4_def old.prod.case option.case_eq_if option.map_sel)

lemma etyping7_eq1:
  "etyping0 \<Gamma> env \<Longrightarrow> etyping \<Gamma> env"
  by (smt etyping3_def etyping3_eq1 etyping_def old.prod.case option.case_eq_if)

lemma default_tenv_exists4:
  "default_tenv env \<turnstile>4 env"
  by (simp add: default_tenv_def etyping4_def option.case_eq_if option.map_sel xpath_subtype.intros(2))

lemma default_env_exists4:
  "\<Gamma> \<turnstile>4 default_env \<Gamma>"
  by (smt comp_apply default_env_def etyping4_def old.prod.case option.case_eq_if option.map_sel type.exhaust type_eq_then_subtype type_of_val.simps(1) type_of_val.simps(2) val_of_type.simps(1) val_of_type.simps(2) val_of_type.simps(3) xpath_subtype.intros(1))
*)

(*** Lemma 1 ****************************************************************************)

(* Вычисление выражения не изменяет его тип *)

lemma type_preservation:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> (exp1, env) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow>
   type_of_val v = \<tau>"
  apply (induct arbitrary: env v rule: typing.induct)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  using etyping_def apply auto[1]
  apply (metis VarE etyping1_def etyping2_eq1 is_none_code(2) option.sel the_map_option)
  apply fastforce
  apply fastforce
  apply fastforce
  apply (erule XPath.PlusE)
  apply auto[1]
  apply (metis type_of_pair_eq type_of_val.simps(4))
  apply (erule XPath.PlusE)
  apply (metis type_of_pair_eq type_of_val.simps(3))
  apply auto[1]
  apply (erule XPath.DivideE; fastforce)
  apply fastforce
  done

(* Well-typed expression has value *)

lemma let_simp22:
  "\<Gamma> \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   type_of_val v\<^sub>1 = \<tau>\<^sub>1 \<Longrightarrow>
   (\<Gamma> \<turnstile> env \<Longrightarrow> (init, env) \<Rightarrow> v\<^sub>1) \<Longrightarrow>
   \<Gamma>(var\<mapsto>\<tau>\<^sub>1) \<turnstile> body : \<tau> \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>\<^sub>1) \<turnstile> env(var\<mapsto>v\<^sub>1) \<Longrightarrow> (body, env(var\<mapsto>v\<^sub>1)) \<Rightarrow> v) \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow> (Let var init body, env) \<Rightarrow> v"
  by (simp add: big_step.intros(4) etyping_def)
(*
lemma max_type_ebtype_simp:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = \<tau> \<Longrightarrow>
   \<tau> \<le> XS_boolean \<Longrightarrow>
   \<tau>\<^sub>1 \<le> XS_boolean \<and> \<tau>\<^sub>2 \<le> XS_boolean"
  using le_sup_iff by blast
*)
lemma and_exists:
  "(a, env) \<Rightarrow> (BValue v\<^sub>1) \<Longrightarrow>
   (b, env) \<Rightarrow> (BValue v\<^sub>2) \<Longrightarrow>
   \<exists>v. (And a b, env) \<Rightarrow> v"
  using big_step.intros(6) by blast

lemma or_exists:
  "(a, env) \<Rightarrow> (BValue v\<^sub>1) \<Longrightarrow>
   (b, env) \<Rightarrow> (BValue v\<^sub>2) \<Longrightarrow>
   \<exists>v. (Or a b, env) \<Rightarrow> v"
  using big_step.intros(7) by blast

lemma not_exists:
  "(a, env) \<Rightarrow> (BValue v) \<Longrightarrow>
   \<exists>v. (Not a, env) \<Rightarrow> v"
  using big_step.intros(8) by blast

lemma integer_divide_exists:
  "(a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   \<exists>v. (Divide a b, env) \<Rightarrow> v"
  by (meson big_step.intros(11))

lemma decimal_divide_exists:
  "(a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   \<exists>v. (Divide a b, env) \<Rightarrow> v"
  by (meson big_step.intros(12))
(*
lemma subtype_trans:
  "\<tau>\<^sub>1 <: \<tau>\<^sub>2 \<Longrightarrow> \<tau>\<^sub>2 <: \<tau>\<^sub>3 \<Longrightarrow> \<tau>\<^sub>1 <: \<tau>\<^sub>3"
  by (metis xpath_subtype.cases)
*)
(*
lemma BooleanVal_exists:
  "type_of_val v \<le> XS_boolean \<Longrightarrow>
   \<exists>x. v = BValue x"
  by (cases v; simp add: order.order_iff_strict)
*)
(*
lemma BooleanVal_exists2:
  "v = BooleanVal x \<Longrightarrow>
   type_of_val v <: EBooleanType"
  by (simp add: subtype.simps)

lemma BooleanVal_exists3:
  "(\<exists>x. v = BooleanVal x) =
   (type_of_val v <: EBooleanType)"
  using BooleanVal_exists subtype.simps by auto
*)

lemma num_type_cases:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> XS_decimal \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_decimal \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_integer \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_nonNegativeInteger \<Longrightarrow> P) \<Longrightarrow> P"
  using less_type.elims(2) order.order_iff_strict by blast

lemma num_type_cases2:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> XS_decimal \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_decimal \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_integer \<Longrightarrow> P) \<Longrightarrow> P"
  using less_type.elims(2) order.order_iff_strict by blast

lemma num_type_cases3:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> XS_integer \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = XS_integer \<Longrightarrow> P) \<Longrightarrow> P"
  using less_type.elims(2) order.order_iff_strict by blast

lemma cast_either_ex_intros:
  "\<exists>x y. a = P x \<and> b = P y \<or>
         a = P x \<and> b as! P y \<or>
         a as! P x \<and> b = P y \<Longrightarrow>
   \<exists>x y. (a, b) as* (P x, P y)"
  using cast_either.intros by blast
(*
lemma type_max_simp:
  "x \<squnion> y = (t :: type) \<Longrightarrow> t \<noteq> XS_anyType \<Longrightarrow> (x = t \<and> y \<le> t) \<or> (x \<le> t \<and> y = t)"
  using sup_type_def by auto

lemma type_max_simp_elim:
  "x \<squnion> y = (t :: type) \<Longrightarrow>
   (t \<noteq> XS_anyType) \<Longrightarrow>
   (x = t \<and> y \<le> t \<Longrightarrow> P) \<Longrightarrow>
   (x \<le> t \<and> y = t \<Longrightarrow> P) \<Longrightarrow> P"
  using type_max_simp by blast

lemma decimal_val_pair_type_rev:
  "type_of_val x \<squnion> type_of_val y = XS_decimal \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (DValue xn, DValue yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
(*  apply (metis cast.simps less_type.simps(20) less_type.simps(9) option.collapse order.order_iff_strict type.distinct(10) type.distinct(15) type.distinct(3) type_of_val.elims)
  apply (metis cast.simps less_type.simps(20) less_type.simps(9) option.collapse order.order_iff_strict type.distinct(10) type.distinct(15) type.distinct(3) type_of_val.elims)*)
  done

lemma integer_val_pair_type_rev:
  "type_of_val x \<squnion> type_of_val y = XS_integer \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (IValue xn, IValue yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  (*apply (metis less_type.simps(15) less_type.simps(19) less_type.simps(8) sup.orderE sup.strict_order_iff type.distinct(1) type.distinct(10) type.distinct(11) type_of_val.elims)
  apply (metis less_type.simps(15) less_type.simps(19) less_type.simps(8) sup.orderE sup.strict_order_iff type.distinct(1) type.distinct(10) type.distinct(11) type_of_val.elims)*)
  done
*)
lemma decimal_val_pair_exists2:
  "\<Gamma> \<turnstile> a : \<tau>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>2 \<Longrightarrow>
   (a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow>
   \<tau>1 \<squnion> \<tau>2 = XS_decimal \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (DValue xn, DValue yn)"
  by (simp add: decimal_val_pair_exists type_preservation)

lemma integer_val_pair_exists2:
  "\<Gamma> \<turnstile> a : \<tau>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>2 \<Longrightarrow>
   (a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow>
   \<tau>1 \<squnion> \<tau>2 = XS_integer \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (IValue xn, IValue yn)"
  by (simp add: integer_val_pair_exists type_preservation)

(*** Lemma 2 ****************************************************************************)

(* Если выражение имеет тип, то оно имеет значение *)

(* Эта и предыдущая теорема доказывают, что описанная система является безопасной:
   https://en.wikipedia.org/wiki/Type_safety
   1) (Type-) preservation or subject reduction
   2) Progress *)

lemma type_system_is_sound:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>v. (exp1, env) \<Rightarrow> v"
  apply (induct arbitrary: env rule: typing.induct)
  using big_step.intros(1) apply auto[1]
  using big_step.intros(2) apply auto[1]
  using big_step.intros(3) apply auto[1]
  apply (metis (no_types, lifting) let_simp22 type_preservation)
  apply (meson big_step.intros(5) var_has_type_impies_has_value)
  apply (metis and_exists boolean_val_exists type_preservation)
  apply (metis or_exists boolean_val_exists type_preservation)
  apply (metis not_exists boolean_val_exists type_preservation)
  apply (meson big_step.intros(9) integer_val_pair_exists2)
  apply (meson big_step.intros(10) decimal_val_pair_exists2)
  apply (erule num_type_cases2)
  apply (meson big_step.intros(12) decimal_val_pair_exists2)
  apply (meson big_step.intros(11) integer_val_pair_exists2)
  apply (erule num_type_cases2)
  apply (meson big_step.intros(14) decimal_val_pair_exists2)
  apply (meson big_step.intros(13) integer_val_pair_exists2)
  done

(* If has value then has type *)

lemma let_simp31:
  "(exp1, env) \<Rightarrow> v1 \<Longrightarrow>
   (\<Gamma> \<turnstile> env \<Longrightarrow> \<Gamma> \<turnstile> exp1 : \<tau>1) \<Longrightarrow>
   (exp2, env(var\<mapsto>v1)) \<Rightarrow> v2 \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>1) \<turnstile> env(var\<mapsto>v1) \<Longrightarrow> \<Gamma>(var\<mapsto>\<tau>1) \<turnstile> exp2 : \<tau>) \<Longrightarrow>
   (Let var exp1 exp2, env) \<Rightarrow> v2 \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow> \<Gamma> \<turnstile> (Let var exp1 exp2) : \<tau>"
  by (simp add: etyping_def type_preservation typing.intros(4))

lemma AndT2:
  "\<Gamma> \<turnstile> exp1 : t1 \<Longrightarrow> t1 = XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> exp2 : t2 \<Longrightarrow> t2 = XS_boolean \<Longrightarrow>
   \<exists>t. \<Gamma> \<turnstile> And exp1 exp2 : t"
  by (meson le_sup_iff typing.intros(6))

lemma OrT2:
  "\<Gamma> \<turnstile> exp1 : t1 \<Longrightarrow> t1 = XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> exp2 : t2 \<Longrightarrow> t2 = XS_boolean \<Longrightarrow>
   \<exists>t. \<Gamma> \<turnstile> Or exp1 exp2 : t"
  by (meson le_sup_iff typing.intros(7))

lemma OrNotT2:
  "\<Gamma> \<turnstile> exp1 : t1 \<Longrightarrow> t1 = XS_boolean \<Longrightarrow>
   \<Gamma> \<turnstile> exp2 : t2 \<Longrightarrow> t2 = XS_boolean \<Longrightarrow>
   \<exists>t. \<Gamma> \<turnstile> Or (Not exp1) exp2 : t"
  by (meson le_sup_iff typing.intros(7) typing.intros(8))

lemma NotT2:
  "\<Gamma> \<turnstile> exp1 : t1 \<Longrightarrow> t1 = XS_boolean \<Longrightarrow>
   \<exists>t. \<Gamma> \<turnstile> Not exp1 : t"
  using typing.intros(8) by blast

inductive_cases cast_either_integer: "(x, y) as* (IValue xn, IValue yn)"
inductive_cases cast_either_decimal: "(x, y) as* (DValue xn, DValue yn)"

lemma decimal_pair_type:
  "(x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y = XS_decimal"
  by (simp add: type_of_pair_eq)

lemma integer_pair_type:
  "(x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y = XS_integer"
  by (simp add: type_of_pair_eq)

lemma decimal_val_pair_type:
  "(x, y) as* (DValue xn, DValue yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y \<le> XS_decimal"
  by (simp add: decimal_pair_type)

lemma integer_val_pair_type:
  "(x, y) as* (IValue xn, IValue yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y \<le> XS_decimal"
  by (simp add: integer_pair_type order.order_iff_strict)

(*** Lemma 3 ****************************************************************************)

(* Любое осмысленное выражение (которое имеет значение) имеет тип
   TODO: Найти определение полноты системы типов *)

lemma type_system_is_complete:
  "(exp1, env) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>"
  apply (induct exp1 arbitrary: env v \<Gamma>)
  using typing.intros(1) apply auto[1]
  using typing.intros(2) apply auto[1]
  using typing.intros(3) apply auto[1]
  apply (smt LetE let_simp31)
  apply (meson VarE var_has_value_impies_has_type typing.intros(5))
  using typing.intros(6) apply auto[1]
  apply (metis type_of_val.simps(2) type_preservation)
  apply (metis OrE OrT2 type_of_val.simps(2) type_preservation)
  apply (metis NotE type_of_val.simps(2) type_preservation typing.intros(8))
  apply (erule PlusE)
  apply (metis integer_pair_type type_preservation typing.intros(9))
  apply (metis decimal_pair_type type_preservation typing.intros(10))
  apply (erule DivideE)
  apply (metis integer_val_pair_type type_preservation typing.intros(11))
  apply (metis decimal_val_pair_type type_preservation typing.intros(11))
  apply (erule LessE)
  apply (metis integer_val_pair_type type_preservation typing.intros(12))
  apply (metis decimal_val_pair_type type_preservation typing.intros(12))
  done

(* TODO: Это свойство как-то называется? *)

lemma has_type_eq_has_value:
  "\<Gamma> \<turnstile> env \<Longrightarrow> (\<exists>v. (exp1, env) \<Rightarrow> v) = (\<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>)"
  using type_system_is_sound type_system_is_complete by auto
(*
lemma well_typed_exp_has_value3:
  "\<exists>env. \<Gamma> \<turnstile> env"
  using default_env_exists by auto

lemma well_typed_exp_has_value4:
  "\<Gamma> \<turnstile> exp : \<tau> \<Longrightarrow> \<exists>env. \<Gamma> \<turnstile> env"
  using default_env_exists by auto
*)
lemma well_typed_exp_has_value7:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> \<exists>env v. \<Gamma> \<turnstile> env \<and> (exp1, env) \<Rightarrow> v"
  using default_env_exists type_system_is_sound by blast

lemma has_value_then_well_typed7:
  "(exp1, env) \<Rightarrow> v \<Longrightarrow> \<exists>\<Gamma> \<tau>. \<Gamma> \<turnstile> env \<and> \<Gamma> \<turnstile> exp1 : \<tau>"
  using default_tenv_exists type_system_is_complete by blast

no_notation big_step (infix "\<Rightarrow>" 55)
no_notation typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
no_notation etyping (infix "\<turnstile>" 50)
(*no_notation cast (infix "as!" 55)
no_notation cast_eq (infix "as" 55)
no_notation cast_either (infix "as*" 55)*)
(*
notation ProgLang.big_step (infix "\<Rightarrow>" 55)
notation ProgLang.typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
notation ProgLang.etyping (infix "\<turnstile>" 50)
*)

code_pred [show_modes] XPath.big_step .
(*
interpretation XPath: prog_lang xpath_typing big_step etyping
  by (simp add: prog_lang.intro typing_is_fun big_step_is_fun has_type_eq_has_value)
*)

(* Определяем XPath как язык программирования, обладающий доказанными выше свойствами *)

interpretation XPath: prog_lang type_of_val typing big_step etyping
  apply (standard)
  apply (simp add: typing_is_fun)
  apply (simp add: big_step_is_fun)
  apply (simp add: type_preservation)
  apply (simp add: type_system_is_sound)
  apply (simp add: type_system_is_complete)
  done

adhoc_overloading ProgLang.big_step big_step
adhoc_overloading ProgLang.typing typing
adhoc_overloading ProgLang.etyping etyping

end

theory XPathType
  imports Complex_Main "~~/src/HOL/Library/Extended_Nat" ProgLang
begin

(*** Types ******************************************************************************)

(* TODO: Добавить остальные типы *)

datatype type =
  XS_anyType
| XS_anySimpleType
| XS_anyAtomicType
| XS_string       
| XS_boolean      
| XS_decimal      
| XS_integer           
| XS_nonNegativeInteger
| FS_numeric

(* Типы XPath образуют верхнюю полурешетку, anyType является верхним элементом *)

instantiation type :: semilattice_sup
begin

fun less_type where
  "XS_anyType < _ = False"
| "_ < XS_anyType = True"
| "XS_integer < XS_decimal = True"
| "(_ :: type) < _ = False"

definition less_eq_type where
  "(\<tau> :: type) \<le> \<sigma> \<equiv> \<tau> = \<sigma> \<or> \<tau> < \<sigma>"

definition sup_type where
  "\<tau> \<squnion> \<sigma> \<equiv> (if \<tau> \<le> \<sigma> then \<sigma> else (if \<sigma> \<le> \<tau> then \<tau> else XS_anyType))"

lemma less_le_not_le_type:
  "(\<tau> :: type) < \<sigma> \<longleftrightarrow> \<tau> \<le> \<sigma> \<and> \<not> \<sigma> \<le> \<tau>"
  by (cases \<tau>; cases \<sigma>; simp add: less_eq_type_def)

lemma order_refl_type [iff]:
  "(\<tau> :: type) \<le> \<tau>"
  by (simp add: less_eq_type_def)

lemma order_trans_type:
  "(\<tau> :: type) \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<le> \<rho>"
  by (cases \<tau>; cases \<sigma>; cases \<rho>; auto simp add: less_eq_type_def)

lemma antisym_type:
  "(\<tau> :: type) \<le> \<sigma> \<Longrightarrow> \<sigma> \<le> \<tau> \<Longrightarrow> \<tau> = \<sigma>"
  by (cases \<tau>; cases \<sigma>; simp add: less_eq_type_def)

lemma sup_ge1_type:
  "(\<tau> :: type) \<le> \<tau> \<squnion> \<sigma>"
  by (cases \<tau>; cases \<sigma>; simp add: less_eq_type_def sup_type_def)

lemma sup_commut_type:
  "(\<tau> :: type) \<squnion> \<sigma> = \<sigma> \<squnion> \<tau>"
  by (simp add: sup_type_def antisym_type)

lemma sup_least_type:
  "(\<tau> :: type) \<le> \<rho> \<Longrightarrow> \<sigma> \<le> \<rho> \<Longrightarrow> \<tau> \<squnion> \<sigma> \<le> \<rho>"
  by (cases \<tau>; cases \<sigma>; cases \<rho>; auto simp add: less_eq_type_def sup_type_def)

instance
  apply intro_classes
  apply (simp add: less_le_not_le_type)
  apply (simp)
  using order_trans_type apply blast
  apply (simp add: antisym_type)
  using less_eq_type_def sup_ge1_type sup_type_def apply auto[1]
  using less_eq_type_def sup_commut_type sup_ge1_type sup_type_def apply auto[1]
  by (simp add: sup_least_type)

end

(*** Values *****************************************************************************)

(* В XPath логические операторы в некоторых ситуациях могут возвращать недетерминированный
   результат (ошибка или значение). Также арифметические операции могут выбрасывать
   динамические исключения. Поэтому для представления значений используем такой тип *)

datatype 'a nondet = Only 'a | Maybe 'a | Error

type_synonym nbool = "bool nondet"

(* Для арифметических операций всё проще. Они могут выбрасывать динамические исключения *)

type_synonym onat = "nat option"
type_synonym oint = "int option"
type_synonym oreal = "real option"

datatype val =
  AValue
| BValue nbool
| IValue oint
| DValue oreal
| NNIValue oint

(* Определяем операцию преобразования типа *)

inductive cast :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "as!" 55) where
  "IValue (Some x) as! DValue (Some x)"
| "IValue None as! DValue None"
| "x \<noteq> AValue \<Longrightarrow> x as! AValue"

code_pred [show_modes] cast .

inductive_cases cast_strict_elim: "x as! y"

(* Значение может быть преобразовано само в себя *)

definition cast_eq :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "as" 55) where
  "x as y \<equiv> x = y \<or> x as! y"

(* Значения XPath с операцией преобразования типов образуют порядок.
   Речь не про сравнение значений одного типа, а про то что, например,
   1 кастуется в 1.0 *)

instantiation val :: order
begin

definition less_eq_val where
  "less_eq_val \<equiv> cast_eq"

definition less_val where
  "less_val \<equiv> cast"

lemma less_le_not_le_val:
  "x as! y \<longleftrightarrow> x as y \<and> \<not> y as x"
  apply (auto simp add: cast_eq_def)
  apply (erule cast.cases; auto)
  apply (erule cast.cases; simp add: cast.simps)
  done

lemma order_refl_val [iff]:
  "x as x"
  by (simp add: cast_eq_def)

lemma order_trans_val:
  "x as y \<Longrightarrow> y as z \<Longrightarrow> x as z"
  apply (auto simp add: cast_eq_def)
  apply (erule cast.cases; auto simp add: cast.simps)
  done

lemma antisym_val:
  "x as y \<Longrightarrow> y as x \<Longrightarrow> x = y"
  using cast_eq_def less_le_not_le_val by blast

instance
  apply (standard)
  apply (simp add: less_eq_val_def less_le_not_le_val less_val_def)
  apply (simp add: less_eq_val_def)
  apply (metis less_eq_val_def order_trans_val)
  by (simp add: antisym_val less_eq_val_def)

end

(* Операция кастования двух значений. Нужна для определения бинарных полиморфных операторов XPath *)

inductive cast_either :: "val \<times> val \<Rightarrow> val \<times> val \<Rightarrow> bool" (infix "as*" 55) where
  "x as* x"
| "a = x \<Longrightarrow> b as! y \<Longrightarrow> (a, b) as* (x, y)"
| "a as! x \<Longrightarrow> b = y \<Longrightarrow> (a, b) as* (x, y)"

inductive_cases cast_eitherE[elim!]: "(a, b) as* (x, y)"

code_pred [show_modes] cast_either .

(*** Type of Val ************************************************************************)

(* Определяем тип для значения *)

fun type_of_val :: "val \<Rightarrow> type" ("\<T> _" [75] 75) where
  "\<T> (AValue) = XS_anyType"
| "\<T> (BValue _) = XS_boolean"
| "\<T> (IValue _) = XS_integer"
| "\<T> (DValue _) = XS_decimal"
| "\<T> (NNIValue _) = XS_nonNegativeInteger"

(* TODO: Вспомнить для чего эта теорема *)

lemma type_of_val_less_any_type:
  "(x \<noteq> AValue) = (\<T> x < XS_anyType)"
  by (cases x; auto)

(* "Порядок кастования" для значений сохраняется для типов этих значений *)

lemma type_of_val_less:
  "x as! y \<Longrightarrow>
   \<T> x < \<T> y"
  by (induct rule: cast.induct; simp add: type_of_val_less_any_type)

lemma type_of_val_less_eq:
  "x as y \<Longrightarrow>
   \<T> x \<le> \<T> y"
  using cast_eq_def less_eq_type_def type_of_val_less by auto

(* TODO: Вспомнить для чего эти теоремы *)

lemma type_of_pair_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> a = \<tau> \<Longrightarrow>
   \<T> b = \<tau> \<Longrightarrow>
   \<T> x \<squnion> \<T> y = \<tau>"
  apply (erule cast_eitherE; simp)
  apply (metis sup.strict_order_iff type_of_val_less)
  by (metis sup.strict_order_iff sup_commut_type type_of_val_less)

lemma type_of_pair_less_eq:
  "(x, y) as* (a, b) \<Longrightarrow>
   \<T> x \<squnion> \<T> y \<le> \<T> a \<squnion> \<T> b"
  apply (erule cast_eitherE; simp)
  apply (simp add: less_eq_type_def less_supI2 type_of_val_less)
  apply (simp add: less_eq_type_def less_supI1 type_of_val_less)
  done  

(*** Val for Type ***********************************************************************)

(* TODO: Вспомнить для чего эти теоремы *)

lemma type_of_val_eq_rev:
  "\<T> x = t \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x = y"
  by auto

lemma type_of_val_less_rev:
  "\<T> x < t \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as! y"
  apply (induct x; induct t; simp)
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  apply (metis cast.intros(1) cast.intros(2) option.exhaust type_of_val.simps(4))
  using cast.intros type_of_val.simps apply blast
  using cast.intros type_of_val.simps apply blast
  done

lemma type_of_val_less_eq_rev:
  "\<T> x \<le> t \<Longrightarrow>
   \<exists>y. \<T> y = t \<and> x as y"
  by (meson cast_eq_def less_eq_type_def type_of_val_less_rev)

(*** Type System ************************************************************************)

(* Типы и значения XPath образуют систему, с определенными свойствами.
   Эти свойства доказаны в теоремах выше *)

interpretation xpath_type_system: type_system
  "(\<squnion>)" "(\<le>)" "(<)" cast_eq cast type_of_val
  apply (standard)
  apply (simp add: less_le_not_le_val)
  apply (simp add: cast_eq_def)
  using order_trans_val apply blast
  apply (simp add: eq_iff less_eq_val_def)
  apply simp
  apply (simp add: type_of_val_less_eq)
  apply (simp add: type_of_val_less)
  apply simp
  apply (simp add: type_of_val_less_eq_rev)
  apply (simp add: type_of_val_less_rev)
  done

(*** Misc *******************************************************************************)

(* TODO: Дальше идут какие-то вспомогательные теоремы.
   Вспомнить зачем они и привести их впорядок *)

lemma type_max_simp:
  "x \<squnion> y = (t :: type) \<Longrightarrow> t \<noteq> XS_anyType \<Longrightarrow> (x = t \<and> y \<le> t) \<or> (x \<le> t \<and> y = t)"
  using sup_type_def by auto

lemma type_max_simp_elim:
  "x \<squnion> y = (t :: type) \<Longrightarrow>
   (t \<noteq> XS_anyType) \<Longrightarrow>
   (x = t \<and> y \<le> t \<Longrightarrow> P) \<Longrightarrow>
   (x \<le> t \<and> y = t \<Longrightarrow> P) \<Longrightarrow> P"
  using type_max_simp by blast

lemma type_of_val_eq_rev_elim:
  "\<T> x = t \<Longrightarrow>
   (\<exists>y. \<T> y = t \<and> x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma type_of_val_less_eq_rev_elim:
  "\<T> x \<le> t \<Longrightarrow>
   (\<exists>y. \<T> y = t \<and> x as y \<Longrightarrow> P) \<Longrightarrow> P"
  using type_of_val_less_eq_rev by blast
    
lemma type_of_pair_eq_rev:
  "\<T> x \<squnion> \<T> y = \<tau> \<Longrightarrow>
   \<tau> \<noteq> XS_anyType \<Longrightarrow>
   \<exists>a b.
      \<T> a = \<tau> \<and> \<T> b = \<tau> \<and>
      (x, y) as* (a, b)"
  apply (erule type_max_simp_elim)
  apply (simp)
  apply (erule conjE)
  apply (erule type_of_val_less_eq_rev_elim)
  apply (erule type_of_val_eq_rev_elim)
  apply (metis cast_either.intros(1) cast_either.intros(2) cast_eq_def)
  apply (erule conjE)
  apply (erule type_of_val_less_eq_rev_elim)
  apply (erule type_of_val_eq_rev_elim)
  apply (metis cast_either.intros(1) cast_either.intros(3) cast_eq_def)
  done

lemma cast_either_ex_intros:
  "\<exists>x y. a = P x \<and> b = P y \<or>
         a = P x \<and> b as! P y \<or>
         a as! P x \<and> b = P y \<Longrightarrow>
   \<exists>x y. (a, b) as* (P x, P y)"
  using cast_either.intros by blast

(*** Specifics **************************************************************************)

lemma boolean_val_exists:
  "\<T> x = XS_boolean \<Longrightarrow> \<exists>y. x = BValue y"
  by (cases x; simp)

lemma decimal_val_exists:
  "\<T> x = XS_decimal \<Longrightarrow> \<exists>y. x = DValue y"
  by (cases x; simp)

lemma integer_val_exists:
  "\<T> x = XS_integer \<Longrightarrow> \<exists>y. x = IValue y"
  by (cases x; simp)

lemma boolean_val_pair_exists:
  "\<T> x \<squnion> \<T> y = XS_boolean \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (BValue xn, BValue yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis boolean_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis boolean_val_exists cast_eq_def type_of_val_less_eq_rev)
  done

lemma decimal_val_pair_exists:
  "\<T> x \<squnion> \<T> y = XS_decimal \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (DValue xn, DValue yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis decimal_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis decimal_val_exists cast_eq_def type_of_val_less_eq_rev)
  done

lemma integer_val_pair_exists:
  "\<T> x \<squnion> \<T> y = XS_integer \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (IValue xn, IValue yn)"
  apply (rule cast_either_ex_intros)
  apply (erule type_max_simp_elim)
  apply simp
  apply (metis integer_val_exists cast_eq_def type_of_val_less_eq_rev)
  apply (metis integer_val_exists cast_eq_def type_of_val_less_eq_rev)
  done
(*
lemma real_type_le_cases:
  "x \<squnion> y \<le> RealType \<Longrightarrow>
   (x \<squnion> y = RealType \<Longrightarrow> P) \<Longrightarrow> 
   (x \<squnion> y = IntegerType \<Longrightarrow> P) \<Longrightarrow>
   (x \<squnion> y = UnlimNatType \<Longrightarrow> P) \<Longrightarrow> 
   (x \<squnion> y = VoidType \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases x; cases y; simp add: less_eq_type_def sup_type_def)

lemma num_type_cases:
  "\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> RealType \<Longrightarrow>
   VoidType < \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = RealType \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = IntegerType \<Longrightarrow> P) \<Longrightarrow>
   (\<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = UnlimNatType \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis dual_order.strict_iff_order real_type_le_cases)
*)
end

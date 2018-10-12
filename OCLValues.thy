theory OCLValues
  imports
    Complex_Main
    "~~/src/HOL/Library/Adhoc_Overloading"
    "~~/src/HOL/Library/Extended_Nat"
    "~~/src/HOL/Library/FSet"
    "Transitive_Closure_Ext"
    "OCLType"
begin

(* errorable *)

notation
  bot ("\<bottom>")

typedef 'a errorable ("_\<^sub>\<bottom>" [21] 21) = "UNIV :: 'a option set" ..

definition errorable :: "'a \<Rightarrow> 'a errorable" ("_\<^sub>\<bottom>" [1000] 1000) where
  "errorable x = Abs_errorable (Some x)"

instantiation errorable :: (type) bot
begin
definition "\<bottom> \<equiv> Abs_errorable None"
instance ..
end

free_constructors case_errorable for
  errorable
| "\<bottom> :: 'a errorable"
  apply (metis Rep_errorable_inverse bot_errorable_def errorable_def not_Some_eq)
  apply (metis Abs_errorable_inverse UNIV_I errorable_def option.inject)
  by (simp add: Abs_errorable_inject bot_errorable_def errorable_def)

copy_bnf 'a errorable

(* nullable *)

(* В этом классе нет смысла, нужно заменить его на optional
   Если для None нужна специальная нотация, то можно её объявить
   Так же как она фактически для bot сейчас объявляется.
   С другой стороны пусть будет.
   Для option конечно могут быть полезные теоремы или свойства.
   Но они могут быть и лишними, как например для enat *)

class opt =
  fixes null :: "'a" ("\<epsilon>")

typedef 'a nullable ("_\<^sub>\<box>" [21] 21) = "UNIV :: 'a option set" ..

definition nullable :: "'a \<Rightarrow> 'a nullable" ("_\<^sub>\<box>" [1000] 1000) where
  "nullable x = Abs_nullable (Some x)"

instantiation nullable :: (type) opt
begin
definition "\<epsilon> \<equiv> Abs_nullable None"
instance ..
end

free_constructors case_nullable for
  nullable
| "\<epsilon> :: 'a nullable"
  apply (metis Rep_nullable_inverse null_nullable_def nullable_def option.collapse)
  apply (simp add: Abs_nullable_inject nullable_def)
  by (metis Abs_nullable_inverse UNIV_I null_nullable_def nullable_def option.distinct(1))

copy_bnf 'a nullable

declare [[coercion "errorable :: bool \<Rightarrow> bool\<^sub>\<bottom>"]]
declare [[coercion "(\<lambda>x. nullable (errorable x)) :: bool \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box>"]]

(* values and operations *)

consts
  conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

locale logic =
  fixes conj :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<^bold>\<and>" 35)
  fixes not :: "'a \<Rightarrow> 'a" ("\<^bold>\<not> _" [40] 40)
  assumes conj_commutes: "(a \<^bold>\<and> b) = (b \<^bold>\<and> a)"
      and not_not: "(\<^bold>\<not> \<^bold>\<not> a) = a"
begin
adhoc_overloading OCLValues.conj conj
no_notation conj (infixr "\<^bold>\<and>" 35)
end

notation conj (infixr "\<^bold>\<and>" 35)

fun ebool_and :: "bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom>" (infixr "\<and>\<^sub>\<bottom>" 35) where
  "(a\<^sub>\<bottom> \<and>\<^sub>\<bottom> b\<^sub>\<bottom>) = (a \<and> b)\<^sub>\<bottom>"
| "(False \<and>\<^sub>\<bottom> _) = False"
| "(_ \<and>\<^sub>\<bottom> False) = False"
| "(\<bottom> \<and>\<^sub>\<bottom> _) = \<bottom>"
| "(_ \<and>\<^sub>\<bottom> \<bottom>) = \<bottom>"

fun obool_and :: "bool\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box>" (infixr "\<and>\<^sub>\<bottom>\<^sub>\<box>" 35) where
  "(a\<^sub>\<bottom>\<^sub>\<box> \<and>\<^sub>\<bottom>\<^sub>\<box> b\<^sub>\<bottom>\<^sub>\<box>) = (a \<and> b)\<^sub>\<bottom>\<^sub>\<box>"
| "(False \<and>\<^sub>\<bottom>\<^sub>\<box> _) = False"
| "(_ \<and>\<^sub>\<bottom>\<^sub>\<box> False) = False"
| "(\<bottom>\<^sub>\<box> \<and>\<^sub>\<bottom>\<^sub>\<box> _) = \<bottom>\<^sub>\<box>"
| "(_ \<and>\<^sub>\<bottom>\<^sub>\<box> \<bottom>\<^sub>\<box>) = \<bottom>\<^sub>\<box>"
| "(\<epsilon> \<and>\<^sub>\<bottom>\<^sub>\<box> _) = \<epsilon>"
| "(_ \<and>\<^sub>\<bottom>\<^sub>\<box> \<epsilon>) = \<epsilon>"

fun ebool_not :: "bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom>" ("\<not>\<^sub>\<bottom> _" [40] 40) where
  "ebool_not (a\<^sub>\<bottom>) = (\<not>a)\<^sub>\<bottom>"
| "ebool_not \<bottom> = \<bottom>"

fun obool_not :: "bool\<^sub>\<bottom>\<^sub>\<box> \<Rightarrow> bool\<^sub>\<bottom>\<^sub>\<box>" ("\<not>\<^sub>\<bottom>\<^sub>\<box> _" [40] 40) where
  "obool_not (a\<^sub>\<bottom>\<^sub>\<box>) = (\<not>a)\<^sub>\<bottom>\<^sub>\<box>"
| "obool_not (\<bottom>\<^sub>\<box>) = \<bottom>\<^sub>\<box>"
| "obool_not \<epsilon> = \<epsilon>"

lemma ebool_and_eq_obool_and:
  "(a\<^sub>\<bottom> \<and>\<^sub>\<bottom> b\<^sub>\<bottom>)\<^sub>\<box> = (a\<^sub>\<bottom>\<^sub>\<box> \<and>\<^sub>\<bottom>\<^sub>\<box> b\<^sub>\<bottom>\<^sub>\<box>)"
  by simp

lemma obool_and_conforms_to_spec:
  "obool_and False False = False"
  "obool_and False True = False"
  "obool_and True False = False"
  "obool_and True True = True"
  "obool_and False \<epsilon> = False"
  "obool_and True \<epsilon> = \<epsilon>"
  "obool_and False \<bottom>\<^sub>\<box> = False"
  "obool_and True \<bottom>\<^sub>\<box> = \<bottom>\<^sub>\<box>"
  "obool_and \<epsilon> False = False"
  "obool_and \<epsilon> True = \<epsilon>"
  "obool_and \<epsilon> \<epsilon> = \<epsilon>"
  "obool_and \<epsilon> \<bottom>\<^sub>\<box> = \<bottom>\<^sub>\<box>"
  "obool_and \<bottom>\<^sub>\<box> False = False"
  "obool_and \<bottom>\<^sub>\<box> True = \<bottom>\<^sub>\<box>"
  "obool_and \<bottom>\<^sub>\<box> \<epsilon> = \<bottom>\<^sub>\<box>"
  "obool_and \<bottom>\<^sub>\<box> \<bottom>\<^sub>\<box> = \<bottom>\<^sub>\<box>"
  by (simp_all)

lemma ebool_and_commut:
  "(a \<and>\<^sub>\<bottom> b) = (b \<and>\<^sub>\<bottom> a)"
  by (induct a b rule: ebool_and.induct; simp add: conj_commute)

lemma ebool_not_not [simp]:
  "(\<not>\<^sub>\<bottom> \<not>\<^sub>\<bottom> a) = a"
  by (induct a rule: ebool_not.induct; simp)

lemma obool_and_commut:
  "(a \<and>\<^sub>\<bottom>\<^sub>\<box> b) = (b \<and>\<^sub>\<bottom>\<^sub>\<box> a)"
  by (induct a b rule: obool_and.induct; simp add: conj_commute ebool_and_commut)

lemma obool_not_not [simp]:
  "(\<not>\<^sub>\<bottom>\<^sub>\<box> \<not>\<^sub>\<bottom>\<^sub>\<box> a) = a"
  by (induct a rule: obool_not.induct; simp)

interpretation ebool_logic: logic ebool_and ebool_not
  apply standard
  apply (simp add: ebool_and_commut)
  apply (simp)
  done

interpretation obool_logic: logic obool_and obool_not
  apply standard
  apply (simp add: obool_and_commut)
  apply (simp)
  done

adhoc_overloading OCLValues.conj obool_and
adhoc_overloading OCLValues.conj ebool_and

value "True\<^sub>\<bottom> \<^bold>\<and> \<bottom>"
value "False\<^sub>\<bottom>\<^sub>\<box> \<^bold>\<and> \<epsilon>"

(*** UnlimitedNatural ***)

(*declare [[coercion "errorable :: enat \<Rightarrow> enat\<^sub>\<bottom>"]]
declare [[coercion "(\<lambda>x. nullable (errorable x)) :: enat \<Rightarrow> enat\<^sub>\<bottom>\<^sub>\<box>"]]*)

(* Для бесконечности правила указаны явно, хотя можно было бы упростить.
   Но просто это не очень тривиально, обычно результат бесконечность, а не ошибка.
   Чтобы было явно видно *)

typedef unat = "UNIV :: nat option set" ..

definition "unat x \<equiv> Abs_unat (Some x)"

instantiation unat :: infinity
begin
definition "\<infinity> \<equiv> Abs_unat None"
instance ..
end

free_constructors cases_unat for
  unat
| "\<infinity> :: unat"
  apply (metis Abs_unat_cases infinity_unat_def option.exhaust unat_def)
  apply (metis Abs_unat_inverse iso_tuple_UNIV_I option.inject unat_def)
  by (simp add: Abs_unat_inject infinity_unat_def unat_def)

fun eunat_plus :: "unat\<^sub>\<bottom> \<Rightarrow> unat\<^sub>\<bottom> \<Rightarrow> unat\<^sub>\<bottom>" (infixl "+\<^sub>\<bottom>" 65) where
  "(unat x)\<^sub>\<bottom> +\<^sub>\<bottom> (unat y)\<^sub>\<bottom> = (unat (x + y))\<^sub>\<bottom>"
| "\<infinity>\<^sub>\<bottom> +\<^sub>\<bottom> _ = \<bottom>"
| "_ +\<^sub>\<bottom> \<infinity>\<^sub>\<bottom> = \<bottom>"
| "\<bottom> +\<^sub>\<bottom> _ = \<bottom>"
| "_ +\<^sub>\<bottom> \<bottom> = \<bottom>"

instantiation errorable :: (plus) plus
begin

fun plus_errorable where
  "plus_errorable a\<^sub>\<bottom> b\<^sub>\<bottom> = (a + b)\<^sub>\<bottom>"
| "plus_errorable _ _ = \<bottom>"

instance ..
end

instantiation nullable :: (bot) plus
begin

fun plus_nullable where
  "plus_nullable a\<^sub>\<box> b\<^sub>\<box> = (a + b)\<^sub>\<box>"
| "plus_nullable _ _ = \<bottom>\<^sub>\<box>"

instance ..
end

typedef eunat = "UNIV :: unat option set" ..

definition "eunat x \<equiv> Abs_eunat (Some (unat x))"

instantiation eunat :: infinity
begin
definition "\<infinity> \<equiv> Abs_eunat (Some \<infinity>)"
instance ..
end

instantiation eunat :: bot
begin
definition "\<bottom> \<equiv> Abs_eunat None"
instance ..
end

free_constructors cases_eunat for
  eunat
| "\<infinity> :: eunat"
| "\<bottom> :: eunat"
  apply (metis Rep_eunat_inverse bot_eunat_def eunat_def infinity_eunat_def not_None_eq unat.exhaust)
  apply (metis Abs_eunat_inverse eunat_def iso_tuple_UNIV_I option.inject unat.inject)
  apply (metis Abs_eunat_inverse eunat_def infinity_eunat_def iso_tuple_UNIV_I option.inject unat.distinct(1))
  apply (metis Abs_eunat_inverse bot_eunat_def eunat_def iso_tuple_UNIV_I option.simps(3))
  by (metis Abs_eunat_inverse UNIV_I bot_eunat_def infinity_eunat_def option.distinct(1))

instantiation eunat :: plus
begin
fun plus_eunat :: "eunat \<Rightarrow> eunat \<Rightarrow> eunat" where
  "plus_eunat (eunat x) (eunat y) = eunat (x + y)"
| "plus_eunat \<infinity> _ = \<bottom>"
| "plus_eunat _ \<infinity> = \<bottom>"
| "plus_eunat \<bottom> _ = \<bottom>"
| "plus_eunat _ \<bottom> = \<bottom>"
instance ..
end

value "(eunat 1) + \<infinity>"
value "(eunat 1) + (eunat 2)"
value "(eunat 1) + \<bottom>"

value "(eunat 1) + \<infinity>"
value "(eunat 1) + (eunat 2)"

value "(eunat 1)\<^sub>\<box> + (eunat 2)\<^sub>\<box>"
value "(eunat 1)\<^sub>\<box> + \<epsilon>"
value "(\<infinity>::eunat)\<^sub>\<box> + \<epsilon>"
value "(eunat 1)\<^sub>\<box> + (\<infinity>::eunat)\<^sub>\<box>"

(* Real *)

value "real 1 + real 2"
value "(real 1)\<^sub>\<bottom> + (real 2)\<^sub>\<bottom>"
value "(real 1)\<^sub>\<bottom>\<^sub>\<box> + (real 3 / real 2)\<^sub>\<bottom>\<^sub>\<box>"

value "int 1 + int 2"
value "(int 1)\<^sub>\<bottom> + (int 2)\<^sub>\<bottom>"
value "(int 1)\<^sub>\<bottom>\<^sub>\<box> + (int 2)\<^sub>\<bottom>\<^sub>\<box>"

(* Any *)

datatype any = BoolVal "bool\<^sub>\<bottom>" | UnlimNatVal "eunat" | RealVal "real\<^sub>\<bottom>" | InvalidAny unit

datatype oany = OBoolVal "bool\<^sub>\<bottom>\<^sub>\<box>" | OUnlimNatVal "eunat\<^sub>\<box>" | ORealVal "real\<^sub>\<bottom>\<^sub>\<box>" | OInvalidAny "unit\<^sub>\<box>"

inductive any_oany :: "any \<Rightarrow> oany \<Rightarrow> bool" where
  "any_oany (BoolVal x) (OBoolVal x\<^sub>\<box>)"
| "any_oany (UnlimNatVal x) (OUnlimNatVal x\<^sub>\<box>)"
| "any_oany (RealVal x) (ORealVal x\<^sub>\<box>)"
| "any_oany (InvalidAny \<bottom>) (OInvalidAny \<bottom>\<^sub>\<box>)"

fun any_to_oany :: "any \<Rightarrow> oany" where
  "any_to_oany (BoolVal x) = (OBoolVal x\<^sub>\<box>)"
| "any_to_oany (UnlimNatVal x) = (OUnlimNatVal x\<^sub>\<box>)"
| "any_to_oany (RealVal x) = (ORealVal x\<^sub>\<box>)"
| "any_to_oany (InvalidAny ()) = (OInvalidAny \<bottom>\<^sub>\<box>)"

lemma any_oany_eq_fun:
  "any_oany x y \<longleftrightarrow> any_to_oany x = y"
  by (cases x; cases y; auto simp: any_oany.simps)

declare [[coercion any_to_oany]]

lemma inj_any_to_oany':
  "any_to_oany x = any_to_oany y \<Longrightarrow> x = y"
  by (cases x; cases y; simp)

lemma inj_any_to_oany:
  "inj any_to_oany"
  apply (rule injI)
  apply (simp add: inj_any_to_oany')
  done

lemma bij_any_to_oany:
  "bij_betw any_to_oany UNIV (range any_to_oany)"
  using inj_any_to_oany by (simp add: bij_betw_def)

(* cast any and cast oany *)

inductive cast_any :: "any \<Rightarrow> any \<Rightarrow> bool" where
  "cast_any (UnlimNatVal \<bottom>) (RealVal \<bottom>)"
| "cast_any (UnlimNatVal (eunat x)) (RealVal (real x)\<^sub>\<bottom>)"
| "cast_any (UnlimNatVal \<infinity>) (RealVal \<bottom>)"
| "cast_any (BoolVal \<bottom>) (InvalidAny \<bottom>)"
| "cast_any (RealVal \<bottom>) (InvalidAny \<bottom>)"

inductive cast_oany :: "oany \<Rightarrow> oany \<Rightarrow> bool" where
  "cast_any x y \<Longrightarrow> any_oany x ox \<Longrightarrow> any_oany y oy \<Longrightarrow>
   cast_oany ox oy"
| "cast_oany (OUnlimNatVal \<epsilon>) (ORealVal \<epsilon>)"
| "cast_oany (OBoolVal \<epsilon>) (OInvalidAny \<epsilon>)"
| "cast_oany (ORealVal \<epsilon>) (OInvalidAny \<epsilon>)"

code_pred [show_modes] cast_oany .


lemma cast_any_implies_cast_oany:
  "cast_any x y \<Longrightarrow> cast_oany (any_to_oany x) (any_to_oany y)"
  by (simp add: any_oany_eq_fun cast_oany.intros(1))

lemma cast_oany_implies_cast_any:
  "cast_oany (any_to_oany x) (any_to_oany y) \<Longrightarrow> cast_any x y"
  by (cases x; cases y; simp add: any_oany.simps cast_oany.simps)


lemma cast_oany_closed_under_range1:
  "cast_oany (any_to_oany x) y \<Longrightarrow> y \<in> range any_to_oany"
  apply (erule cast_oany.cases)
  using any_oany_eq_fun apply auto[1]
  using any_to_oany.elims apply blast
  using any_to_oany.elims apply blast
  using any_to_oany.elims apply blast
  done

lemma cast_oany_closed_under_range2:
  "cast_oany x (any_to_oany y) \<Longrightarrow> x \<in> range any_to_oany"
  apply (erule cast_oany.cases)
  using any_oany_eq_fun apply auto[1]
  using any_to_oany.elims apply blast
  using any_to_oany.elims apply blast
  using any_to_oany.elims apply blast
  done

lemma cast_oany_closed_under_range:
  "rel_closed_under cast_oany (range any_to_oany)"
  by (auto simp: rel_closed_under_def cast_oany_closed_under_range1 cast_oany_closed_under_range2)


lemma any_to_oany_preserve_trancl_cast_oany1:
  fixes x y :: any
  assumes as: "cast_oany\<^sup>+\<^sup>+ (any_to_oany x) (any_to_oany y)" 
  shows "(\<lambda>x y. cast_oany (any_to_oany x) (any_to_oany y))\<^sup>+\<^sup>+ x y"
proof -
  obtain B where B: "B = range any_to_oany" by auto
  from bij_any_to_oany B have c_f: "bij_betw any_to_oany UNIV B" by simp
  from cast_oany_closed_under_range B have c_R: "rel_closed_under cast_oany B"
    by simp
  from tranclp_fun_preserve_gen_1 as B c_f c_R show ?thesis by metis
qed

lemma any_to_oany_preserve_trancl_cast_oany2:
  fixes x y :: any
  assumes as: "(\<lambda>x y. cast_oany (any_to_oany x) (any_to_oany y))\<^sup>+\<^sup>+ x y" 
  shows "cast_oany\<^sup>+\<^sup>+ (any_to_oany x) (any_to_oany y)"
proof -
  obtain B where B: "B = range any_to_oany" by auto
  from bij_any_to_oany B have c_f: "bij_betw any_to_oany UNIV B" by simp
  from cast_oany_closed_under_range B have c_R: "rel_closed_under cast_oany B"
    by simp
  from tranclp_fun_preserve_gen_2 as B c_f c_R show ?thesis by metis  
qed


lemma trancl_cast_any_implies_cast_oany':
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow>
   (\<lambda>x y. cast_oany (any_to_oany x) (any_to_oany y))\<^sup>+\<^sup>+ x y"
  apply (erule tranclp_trans_induct)
  apply (simp add: cast_any_implies_cast_oany tranclp.r_into_trancl)
  by auto

lemma trancl_cast_oany_implies_cast_any':
  "(\<lambda>x y. cast_oany (any_to_oany x) (any_to_oany y))\<^sup>+\<^sup>+ x y \<Longrightarrow>
   cast_any\<^sup>+\<^sup>+ x y"
  apply (erule tranclp_trans_induct)
  apply (simp add: cast_oany_implies_cast_any tranclp.r_into_trancl)
  by auto


lemma trancl_cast_oany_implies_cast_any:
  "cast_oany\<^sup>+\<^sup>+ (any_to_oany x) (any_to_oany y) \<Longrightarrow> cast_any\<^sup>+\<^sup>+ x y"
  by (simp add: any_to_oany_preserve_trancl_cast_oany1 trancl_cast_oany_implies_cast_any')

lemma trancl_cast_any_implies_cast_oany:
  "cast_any\<^sup>+\<^sup>+ x y \<Longrightarrow> cast_oany\<^sup>+\<^sup>+ (any_to_oany x) (any_to_oany y)"
  by (simp add: any_to_oany_preserve_trancl_cast_oany2 trancl_cast_any_implies_cast_oany')

(* any order*)

(* TODO: Replace by inductive_cases *)
lemma not_cast_any_InvalidAny:
  "\<not> cast_any (InvalidAny x) y"
  by (induct y; simp add: cast_any.simps)

lemma det_cast_any:
  "cast_any x y \<Longrightarrow> cast_any x z \<Longrightarrow> y = z"
  by (induct rule: cast_any.induct; simp add: cast_any.simps)

instantiation any :: order
begin

definition less_any where
  "less_any \<equiv> cast_any\<^sup>+\<^sup>+"

definition less_eq_any where
  "less_eq_any \<equiv> cast_any\<^sup>*\<^sup>*"

lemma antisym_cast_any:
  "cast_any x y \<Longrightarrow> \<not> cast_any y x"
  apply (erule cast_any.cases)
  using cast_any.simps by auto

(* TODO: Rename *)
lemma antisym_cast_any2:
  "cast_any\<^sup>*\<^sup>* x y \<Longrightarrow> \<not> cast_any y x"
  apply (induct rule: rtranclp_induct)
  using antisym_cast_any apply blast
  by (metis any.distinct(8) any.distinct(9) cast_any.simps rtranclp.simps)

(* TODO: Remove? *)
lemma not_trans_cast_any:
  "cast_any x y \<Longrightarrow> cast_any y z \<Longrightarrow> \<not> cast_any z x"
  apply (erule cast_any.cases)
  using cast_any.simps by auto

lemma less_le_not_le_any:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  for x :: any
  apply (auto simp add: less_any_def less_eq_any_def)
  apply (metis antisym_cast_any2 rtranclp_trans tranclpD)
  by (metis rtranclpD)

lemma order_trans_any:
  "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  for x :: any
  apply (simp add: less_eq_any_def)
  done

lemma antisym_any:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  for x :: any
  apply (simp add: less_eq_any_def)
  by (metis (mono_tags, lifting) less_any_def less_eq_any_def less_le_not_le_any rtranclpD)

instance
  apply (standard)
  apply (simp add: less_le_not_le_any)
  apply (simp add: less_eq_any_def)
  apply (simp add: order_trans_any)
  apply (simp add: antisym_any)
  done

end


lemma not_cast_oany_OInvalidAny:
  "\<not> cast_oany (OInvalidAny x) y"
  by (induct y; simp add: any_oany.simps cast_any.simps cast_oany.simps)

lemma det_cast_oany:
  "cast_oany x y \<Longrightarrow> cast_oany x z \<Longrightarrow> y = z"
  apply (induct rule: cast_oany.induct)
  using any_oany_eq_fun cast_oany_closed_under_range1 cast_oany_implies_cast_any det_cast_any apply fastforce
  apply (metis any_oany.simps cast_oany.cases nullable.distinct(1) oany.distinct(1) oany.distinct(7) oany.distinct(9) oany.inject(2))
  apply (metis any_oany.simps cast_oany.cases nullable.distinct(1) oany.distinct(1) oany.distinct(3) oany.distinct(5) oany.inject(1))
  by (metis any_oany.simps cast_oany.cases nullable.distinct(1) oany.distinct(11) oany.distinct(3) oany.distinct(7) oany.inject(3))

lemma antisym_cast_oany:
  "cast_oany x y \<Longrightarrow> \<not> cast_oany y x"
  apply (induct rule: cast_oany.induct)
  using antisym_cast_any any_oany_eq_fun cast_oany_implies_cast_any apply auto[1]
  using cast_oany.intros(4) det_cast_oany apply auto[1]
  apply (simp add: not_cast_oany_OInvalidAny)
  apply (simp add: not_cast_oany_OInvalidAny)
  done

instantiation oany :: order
begin

definition less_oany where
  "less_oany \<equiv> cast_oany\<^sup>+\<^sup>+"

definition less_eq_oany where
  "less_eq_oany \<equiv> cast_oany\<^sup>*\<^sup>*"

(* TODO: Rename *)
lemma antisym_cast_oany2:
  "cast_oany\<^sup>*\<^sup>* x y \<Longrightarrow> \<not> cast_oany y x"
  apply (erule converse_rtranclpE)
  using antisym_cast_oany apply blast
  apply (erule cast_oany.cases)
  apply (metis Nitpick.rtranclp_unfold antisym_cast_any2 any_oany_eq_fun inj_any_to_oany' rtranclp.rtrancl_into_rtrancl trancl_cast_oany_implies_cast_any)
  apply (metis antisym_cast_oany cast_oany.intros(2) cast_oany.intros(4) converse_tranclpE det_cast_oany not_cast_oany_OInvalidAny rtranclp_into_tranclp1)
  apply (metis converse_rtranclpE not_cast_oany_OInvalidAny)
  apply (metis converse_rtranclpE not_cast_oany_OInvalidAny)
  done

lemma less_le_not_le_oany:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  for x :: oany
  apply (auto simp add: less_oany_def less_eq_oany_def)
  apply (metis antisym_cast_oany2 rtranclp_trans tranclpD)
  by (metis rtranclpD)

lemma order_trans_oany:
  "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  for x :: oany
  apply (simp add: less_eq_oany_def)
  done

lemma antisym_oany:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  for x :: oany
  apply (simp add: less_eq_oany_def)
  by (metis antisym_cast_oany2 converse_rtranclpE rtranclp_trans)

instance
  apply (standard)
  apply (simp add: less_le_not_le_oany)
  apply (simp add: less_eq_oany_def)
  apply (simp add: order_trans_oany)
  apply (simp add: antisym_oany)
  done

end


(* Set *)

typedef 'a myset = "UNIV :: 'a fset option set" ..

setup_lifting type_definition_myset

lift_definition myset :: "'a fset \<Rightarrow> 'a myset" is Some .

lift_definition mysetempty :: "'a myset" is "Some fempty" .

lift_definition mysetinsert :: "'a \<Rightarrow> 'a myset \<Rightarrow> 'a myset" is "map_option \<circ> finsert" .

value "(map_option \<circ> finsert) 3 (Some {|1::nat,2|})"
value "(map_option \<circ> finsert) (3::nat) (None)"

instantiation myset :: (type) bot
begin
lift_definition bot_myset :: "'a myset" is None .
instance ..
end


free_constructors case_myset for
  myset
| "\<bottom> :: 'a myset"
  apply (simp_all add: bot_myset_def myset_def)
  apply (metis Rep_myset_inverse option.collapse)
  apply (metis Abs_myset_inverse iso_tuple_UNIV_I option.inject)
  apply (metis Abs_myset_inverse iso_tuple_UNIV_I option.distinct(1))
  done

lift_definition map_myset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a myset \<Rightarrow> 'b myset" 
  is "map_option \<circ> fimage" .
thm map_myset_def

copy_bnf 'a myset

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name myset} |> Option.map #ctrs\<close>
ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name fset} |> Option.map #ctrs\<close>


(* val *)

datatype val =
  InvalidVal unit
| VoidVal "unit\<^sub>\<box>"
| RequiredVal any
| OptionalVal oany
| SetVal type "val fset\<^sub>\<bottom>"

definition is_required_set :: "val fset \<Rightarrow> bool" where
  "is_required_set xs \<equiv> fBall xs (\<lambda>x. case x of RequiredVal _ \<Rightarrow> True | _ \<Rightarrow> False)"

inductive cast_val_set :: "val fset \<Rightarrow> val fset \<Rightarrow> bool" where
  "is_required_set xs \<Longrightarrow>
   cast_val_set xs ys"

code_pred [show_modes] cast_val_set .

fun type_of_any :: "any \<Rightarrow> simple_type" where
  "type_of_any (BoolVal _) = Boolean"
| "type_of_any (UnlimNatVal _) = UnlimitedNatural"
| "type_of_any (RealVal _) = Real"
| "type_of_any (InvalidAny _) = OclAny"

fun type_of_oany :: "oany \<Rightarrow> simple_type" where
  "type_of_oany (OBoolVal _) = Boolean"
| "type_of_oany (OUnlimNatVal _) = UnlimitedNatural"
| "type_of_oany (ORealVal _) = Real"
| "type_of_oany (OInvalidAny _) = OclAny"

fun type_of_val :: "val \<Rightarrow> type" where
  "type_of_val (InvalidVal _) = OclInvalid"
| "type_of_val (VoidVal _) = OclVoid"
| "type_of_val (RequiredVal x) = Required (type_of_any x)"
| "type_of_val (OptionalVal x) = Optional (type_of_oany x)"
| "type_of_val (SetVal \<tau> xs) = Set \<tau>"

fun val_is_ok :: "val \<Rightarrow> bool" where
  "val_is_ok (SetVal \<tau> xs\<^sub>\<bottom>) = fBall xs (\<lambda>x. type_of_val x \<le> \<tau>)"
| "val_is_ok _ = True"

inductive cast_val :: "val \<Rightarrow> val \<Rightarrow> bool" where
  "cast_val (InvalidVal \<bottom>) (VoidVal \<bottom>\<^sub>\<box>)"
| "cast_val (InvalidVal \<bottom>) (RequiredVal (BoolVal \<bottom>))"
| "cast_val (InvalidVal \<bottom>) (RequiredVal (UnlimNatVal \<bottom>))"
| "OclInvalid <: \<tau> \<Longrightarrow>
   cast_val (InvalidVal \<bottom>) (SetVal \<tau> \<bottom>)"
| "cast_val (VoidVal \<bottom>\<^sub>\<box>) (OptionalVal (OBoolVal \<bottom>\<^sub>\<box>))"
| "cast_val (VoidVal \<bottom>\<^sub>\<box>) (OptionalVal (OUnlimNatVal \<bottom>\<^sub>\<box>))"
| "cast_any x y \<Longrightarrow> cast_val (RequiredVal x) (RequiredVal y)"
| "cast_oany x y \<Longrightarrow> cast_val (OptionalVal x) (OptionalVal y)"
| "cast_val (RequiredVal x) (OptionalVal x)"
(*| "rel_fset cast_val xs ys \<Longrightarrow>
   xs \<noteq> {||} \<Longrightarrow>
   ys \<noteq> {||} \<Longrightarrow>
   cast_val (SetVal xs\<^sub>\<bottom>) (SetVal ys\<^sub>\<bottom>)"*)
| "\<tau> <: \<sigma> \<Longrightarrow>
   fBall xs (\<lambda>x. type_of_val x \<le> \<tau>) \<Longrightarrow>
   fBall ys (\<lambda>y. type_of_val y \<le> \<sigma>) \<Longrightarrow>
   cast_val (SetVal \<tau> xs\<^sub>\<bottom>) (SetVal \<sigma> ys\<^sub>\<bottom>)"
(*| "\<tau> < \<sigma> \<Longrightarrow>
   rel_fset (\<lambda>x y. x = y \<or> cast_val x y) xs ys \<Longrightarrow>
   cast_val (SetVal \<tau> xs\<^sub>\<bottom>) (SetVal \<sigma> ys\<^sub>\<bottom>)"*)
(*
| "rel_fset (\<lambda>x y. x = y \<or> cast_val x y) xs ys \<Longrightarrow>
   xs \<noteq> ys \<Longrightarrow>
   cast_val (SetVal xs\<^sub>\<bottom>) (SetVal ys\<^sub>\<bottom>)"
*)

(* Пустые множества равны сами себе, а это отношение нерефлексивное
   Кастование пустых множеств появится в cast_val\<^sup>*\<^sup>*

   Если мы добавляем тип элементов, то кастовать пустые множества уже можно

   Это значит, что каждый элемент должен быть скастован, хотя по идее должен хотя бы один:
   rel_fset cast_val xs ys \<Longrightarrow>
   cast_val (SetVal xs\<^sub>\<bottom>) (SetVal ys\<^sub>\<bottom>)

   Если множество содержит целые числа, то можно его скастовать во множество действительных чисел
   Если множество содержит разные по типу значения, то можно его скастовать в Set(OclAny)

   Нужно добавить условие, что все элементы одного типа, иначе в последовательности
   из нескольких null можно кастануть каждый null в какой-то свой тип (bool, nat, ...),
   а это не нужно.
   С другой стороны, множество может содержать разные значения. В этом случае оно
   имеет тип элемента any. Но операция кастования все равно должна кастовать элементы в один тип
   Как вариант можно просто явно перечислить все варианты: кастуем во множество bool,
   во множество real и т.д. Самый простой способ сделать это - это добавить в качестве
   параметра тип, либо включить тип во множество. Для простых типов это было не нужно,
   потому что соответствие значений и типов тривиальное. Да, без типов никак. Допустим
   при определении семантики для ->sum() мне нужно множество чисел, нужно каким-то образом
   задать этот тип

   Плюс с типами элементов проще доказывать теоремы

   На самом деле я и так в значениях дублирую типы, поэтому ничего страшного если у множеств
   будет явный параметр с типом элементов
 *)

code_pred [show_modes] cast_val .

value "SetVal UnlimitedNatural[1] {|
         RequiredVal (UnlimNatVal (eunat 1)), RequiredVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>"
value "val_is_ok (SetVal UnlimitedNatural[1] {|
         RequiredVal (UnlimNatVal (eunat 1)), RequiredVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>)"
value "val_is_ok (SetVal UnlimitedNatural[1] {|
         RequiredVal (UnlimNatVal (eunat 1)), OptionalVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>)"
value "cast_val
         (SetVal UnlimitedNatural[1] {|
             RequiredVal (UnlimNatVal (eunat 1)), RequiredVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>)
         (SetVal UnlimitedNatural[?] {|
             RequiredVal (UnlimNatVal (eunat 1)), OptionalVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>)"
value "cast_val
         (SetVal UnlimitedNatural[1] {|
             RequiredVal (UnlimNatVal (eunat 1)), RequiredVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>)
         (SetVal UnlimitedNatural[?] {|
             RequiredVal (UnlimNatVal (eunat 1)), OptionalVal (UnlimNatVal (eunat 2))|}\<^sub>\<bottom>)"

lemma antisym_cast_val1:
  "cast_val x y \<Longrightarrow> cast_val y x \<Longrightarrow> x = y"
  apply (induct rule: cast_val.induct)
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using antisym_cast_any cast_val.cases apply blast
  using antisym_cast_oany cast_val.cases apply blast
  using cast_val.cases apply blast
  by (smt cast_val.cases less_imp_not_less val.distinct(17) val.distinct(19) val.distinct(7) val.inject(5))

lemma antisym_cast_val:
  "cast_val x y \<Longrightarrow> \<not> cast_val y x"
  apply (induct rule: cast_val.induct)
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using antisym_cast_any cast_val.cases apply blast
  using antisym_cast_oany cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases less_imp_not_less by fastforce


inductive_cases cast_val_x_VoidVal[elim!]: "cast_val x (VoidVal ()\<^sub>\<box>)"
inductive_cases cast_val_x_RequiredVal[elim!]: "cast_val x (RequiredVal y)"
inductive_cases cast_val_RequiredVal_y[elim!]: "cast_val (RequiredVal x) y"
inductive_cases cast_val_x_OptionalVal[elim!]: "cast_val x (OptionalVal y)"
inductive_cases cast_val_OptionalVal_y[elim!]: "cast_val (OptionalVal x) y"
inductive_cases cast_val_RequiredVal_OptionalVal[elim!]: "cast_val (RequiredVal x) (OptionalVal y)"

inductive_cases cast_oany_OBoolVal_x[elim!]: "cast_oany (OBoolVal \<bottom>\<^sub>\<box>) y"
inductive_cases cast_oany_x_OBoolVal[elim!]: "cast_oany x (OBoolVal \<bottom>\<^sub>\<box>)"

inductive_cases any_oany_x_OBoolVal[elim!]: "any_oany x (OBoolVal \<bottom>\<^sub>\<box>)"

inductive_cases cast_any_BoolVal_x[elim!]: "cast_any (BoolVal \<bottom>) y"

inductive_cases any_oany_InvalidAny_x[elim!]: "any_oany (InvalidAny ()) y"

inductive_cases cast_oany_OUnlimNatVal_x[elim!]: "cast_oany (OUnlimNatVal \<bottom>\<^sub>\<box>) x"
inductive_cases any_oany_x_OUnlimNatVal[elim!]: "any_oany x (OUnlimNatVal \<bottom>\<^sub>\<box>)"
inductive_cases cast_any_UnlimNatVal_x[elim!]: "cast_any (UnlimNatVal \<bottom>) y"
inductive_cases any_oany_RealVal_x[elim!]: "any_oany (RealVal \<bottom>) x"
inductive_cases cast_oany_OInvalidAny_x[elim!]: "cast_oany (OInvalidAny ()\<^sub>\<box>) x"
inductive_cases any_oany_x_OInvalidAny[elim!]: "any_oany x (OInvalidAny ()\<^sub>\<box>)"
inductive_cases cast_any_InvalidAny_x[elim!]: "cast_any (InvalidAny ()) x"

inductive_cases cast_val_x_InvalidVal[elim!]: "cast_val x (InvalidVal \<bottom>)"

inductive_cases cast_val_OptionalVal_OptionalVal[elim!]: "cast_val (OptionalVal x) (OptionalVal y)"

thm notE

print_theorems

lemma q:
  "cast_val\<^sup>*\<^sup>* (OptionalVal x) y \<Longrightarrow>
   cast_oany z x \<Longrightarrow> \<not> cast_val y (OptionalVal z)"
  apply (cases y)
  apply auto[1]
  apply (smt cast_val.cases cast_val.intros(8) cast_val_x_InvalidVal rtranclp.cases val.distinct(11) val.distinct(13) val.distinct(9))
  apply (erule rtranclp.cases)
     apply simp

(*
  apply (induct rule: rtranclp_induct)
  using antisym_cast_val cast_val.intros(8) apply blast
  apply auto[1]
  apply (metis bot_unit_def cast_val_x_InvalidVal rtranclp.cases val.distinct(5))
  apply (metis bot_unit_def cast_val_x_InvalidVal rtranclp.cases val.distinct(5))
  apply (metis any_oany.intros(3) any_oany.intros(4) bot_unit_def cast_any.intros(5) cast_oany.intros(1) cast_val_OptionalVal_y converse_rtranclpE det_cast_oany not_cast_oany_OInvalidAny val.simps(17))
      apply (erule notE)
*)
(*
  apply (erule rtranclp.cases)
  using antisym_cast_val cast_val.intros(8) apply blast
  apply auto[1]
  apply (meson cast_val_OptionalVal_y converse_rtranclpE not_cast_oany_OInvalidAny val.distinct(6))
  apply (smt cast_val.cases rtranclp.cases val.distinct(1) val.distinct(3) val.distinct(5) val.distinct(7))
  using cast_any.intros(5) cast_any_implies_cast_oany converse_rtranclpE det_cast_oany apply fastforce
  apply (erule rtranclp.cases)
  apply (metis antisym_cast_oany2 rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl val.inject(4))
*)

lemma q:
  "cast_oany x y \<Longrightarrow>
   cast_val\<^sup>+\<^sup>+ (OptionalVal y) z \<Longrightarrow>
   \<not> cast_val z (OptionalVal x)"
  apply (erule cast_oany.cases)
  apply (cases x; auto)
  apply (meson cast_val_OptionalVal_y not_cast_oany_OInvalidAny tranclpD)
  using any_oany_eq_fun cast_any.simps apply force
  apply (metis any.simps(6) any_oany.simps any_oany_eq_fun cast_any.cases cast_val_OptionalVal_y not_cast_oany_OInvalidAny oany.distinct(1) oany.distinct(3) oany.simps(10) tranclpD)
  apply (metis bot_unit_def cast_val_x_InvalidVal cast_val_x_VoidVal tranclp.cases val.distinct(5))
  apply (erule cast_oany.cases)
  using any_oany.simps cast_any.simps apply fastforce
  apply simp
  apply simp
  apply simp
(*
  apply (cases x; cases z; auto)
  apply (meson cast_val_OptionalVal_y not_cast_oany_OInvalidAny tranclpD)

  apply (erule cast_oany.cases)
  apply (metis (no_types, lifting) any_oany_eq_fun any_to_oany.simps(2) any_to_oany.simps(4) bot_unit_def cast_any.simps cast_val_OptionalVal_y not_cast_oany_OInvalidAny oany.distinct(1) tranclpD)
  apply simp
  using any_to_oany.elims apply blast
  apply simp

  apply (erule cast_oany.cases)
  apply (metis any.simps(6) any_oany.simps any_oany_eq_fun cast_any.cases cast_val_OptionalVal_y not_cast_oany_OInvalidAny oany.distinct(1) oany.distinct(3) oany.simps(10) tranclpD)
  apply simp
  apply (meson cast_val_OptionalVal_y not_cast_oany_OInvalidAny tranclpD)
  apply simp
  apply (metis bot_unit_def cast_val_x_InvalidVal cast_val_x_VoidVal tranclp.cases val.distinct(5))
*)

lemma antisym_cast_val2:
  "cast_val\<^sup>+\<^sup>+ x y \<Longrightarrow> \<not> cast_val y x"
  apply (erule converse_tranclpE)
  using antisym_cast_val apply blast
  apply (erule cast_val.cases)
  using cast_val_x_InvalidVal apply auto[1]
  using cast_val_x_InvalidVal apply auto[1]
  using cast_val_x_InvalidVal apply auto[1]
  using cast_val_x_InvalidVal apply auto[1]
  apply (metis bot_unit_def cast_val_x_InvalidVal cast_val_x_VoidVal tranclp.cases)
  apply (metis bot_unit_def cast_val_x_InvalidVal cast_val_x_VoidVal tranclp.cases)
  apply (erule tranclp.cases)
  using not_trans_cast_any apply blast

  apply (erule cast_any.cases)
  using any.distinct(7) cast_any.cases cast_val_x_InvalidVal apply fastforce
  using cast_any.cases apply blast
  using cast_any.simps apply blast
  using any.distinct(3) cast_any.cases cast_val_x_InvalidVal apply fastforce
  apply auto[1]
  apply (metis bot_unit_def cast_val_x_InvalidVal tranclp.cases)
  apply (metis antisym_cast_any any.distinct(8) cast_any.simps)
(*
  apply (erule cast_oany.cases)
  apply (erule cast_any.cases)
  apply (metis any_oany.intros(4) cast_any.intros(5) cast_oany.intros(1) cast_val_OptionalVal_y det_cast_oany not_cast_oany_OInvalidAny rtranclp_into_tranclp1 tranclpD)
*)
(*
  apply (smt antisym_cast_any any.distinct(7) cast_any.cases cast_any.intros(5) cast_val.cases cast_val_x_InvalidVal tranclp.cases val.distinct(15) val.distinct(17) val.inject(3))
  apply (smt antisym_cast_any antisym_cast_any2 bot_unit_def cast_val.cases cast_val_RequiredVal_y cast_val_x_InvalidVal cast_val_x_RequiredVal r_into_rtranclp rtranclp.rtrancl_into_rtrancl val.distinct(15) val.inject(3))

  apply (smt any.distinct(7) any_to_oany.simps(4) bot_unit_def cast_any.cases cast_any_implies_cast_oany cast_val_x_InvalidVal cast_val_x_RequiredVal not_cast_oany_OInvalidAny tranclp.cases val.inject(3))
*)

(* TODO: Rename *)
(* Это доказывает, что нет циклов *)
lemma antisym_cast_val2:
  "cast_val\<^sup>*\<^sup>* x y \<Longrightarrow> \<not> cast_val y x"
  apply (erule converse_rtranclpE)
  using antisym_cast_val apply blast
  apply (erule cast_val.cases)
  using cast_val_x_InvalidVal apply auto[1]
  using cast_val_x_InvalidVal apply auto[1]
  using cast_val_x_InvalidVal apply auto[1]
  using cast_val_x_InvalidVal apply auto[1]
  apply (metis bot_unit_def cast_val_x_InvalidVal cast_val_x_VoidVal rtranclp.cases val.distinct(5))
  apply (metis bot_unit_def cast_val_x_InvalidVal cast_val_x_VoidVal rtranclp.cases val.distinct(5))
  apply (erule rtranclp.cases)
  using antisym_cast_val cast_val.intros(7) apply blast

  apply auto[1]
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  apply (metis bot_unit_def cast_val.intros(7) cast_val_x_InvalidVal rtranclp.cases)
  apply (metis any.distinct(7) any_to_oany.simps(4) bot_unit_def cast_any.cases cast_any_implies_cast_oany not_cast_oany_OInvalidAny)

(*
  using cast_any.intros(4) det_cast_any not_cast_any_InvalidAny apply auto[1]
  apply (erule rtranclp.cases)
  apply auto[1]
  using cast_val.cases apply blast
  apply (metis any.distinct(7) cast_any.cases not_cast_any_InvalidAny)

  apply auto[1]
  apply (meson cast_val_OptionalVal_y converse_rtranclpE not_cast_oany_OInvalidAny val.simps(17))
  apply (metis any_to_oany.simps(2) any_to_oany.simps(4) bot_unit_def cast_any.intros(1) cast_any.intros(5) cast_any_implies_cast_oany cast_val_OptionalVal_y converse_rtranclpE det_cast_oany not_cast_oany_OInvalidAny val.simps(17))
  apply (erule rtranclp.cases)
  using antisym_cast_oany apply blast
  apply (erule rtranclp.cases)
  apply (metis antisym_cast_oany2 cast_val_OptionalVal_y rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl val.inject(4))
  apply auto[1]
  apply (simp add: not_cast_oany_OInvalidAny)
  apply (metis any_to_oany.simps(2) any_to_oany.simps(4) bot_unit_def cast_any.intros(1) cast_any.intros(5) cast_any_implies_cast_oany cast_val_OptionalVal_y converse_rtranclpE det_cast_oany not_cast_oany_OInvalidAny val.distinct(5))
  apply (simp add: not_cast_oany_OInvalidAny)
  apply (metis any_to_oany.simps(2) any_to_oany.simps(4) bot_unit_def cast_any.intros(1) cast_any.intros(5) cast_any_implies_cast_oany det_cast_oany not_cast_oany_OInvalidAny)

*)
    (*
  apply (smt antisym_cast_val cast_val.simps 
 val.distinct(3) val.distinct(5) val.distinct(7))
*)
(*
  apply (smt cast_val.cases rtranclp.cases val.distinct(1) val.distinct(3) val.distinct(5) val.distinct(7))
  apply (drule cast_val_x_VoidVal)
*)
(*
  apply (smt antisym_cast_val cast_val.simps cast_val_x_VoidVal rtranclp.simps val.distinct(3) val.distinct(5) val.distinct(7))
  apply (smt antisym_cast_val cast_val.simps rtranclp.simps val.distinct(11) val.distinct(13) val.distinct(3) val.distinct(5) val.distinct(7) val.distinct(9))
*)

lemma antisym_cast_val:
  "cast_val\<^sup>*\<^sup>* x y \<Longrightarrow> cast_val\<^sup>*\<^sup>* y x \<Longrightarrow> x = y"
  apply (induct rule: rtranclp_induct)
  apply simp
(*
  apply (induct rule: cast_val.induct)
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using cast_val.cases apply blast
  using antisym_cast_any cast_val.cases apply blast
  using antisym_cast_oany cast_val.cases apply blast
  using cast_val.cases apply blast
*)



instantiation val :: order
begin

definition less_val where
  "less_val \<equiv> cast_val\<^sup>+\<^sup>+"

definition less_eq_val where
  "less_eq_val \<equiv> cast_val\<^sup>*\<^sup>*"

lemma less_le_not_le_val:
  "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  for x y :: val
  apply (simp add: less_val_def less_eq_val_def)


lemma order_refl_val [iff]:
  "x \<le> x"
  for x :: val
  by (simp add: less_eq_val_def)

lemma order_trans_val:
  "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  for x :: val
  by (auto simp add: less_eq_val_def)

lemma antisym_val:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  for x :: val

instance
  apply (standard)
(*
  apply (simp add: less_eq_val_def less_le_not_le_val less_val_def)
  apply (simp add: less_eq_val_def)
  apply (metis less_eq_val_def order_trans_val)
  by (simp add: antisym_val less_eq_val_def)
*)
end



end

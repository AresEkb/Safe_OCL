theory ClosureTest
  imports 
    Complex_Main
    "HOL-Library.FuncSet"
begin

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

(*** general theory of functions that preserve the properties of closure ***)

definition rel_closed_under :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"rel_closed_under R A = 
(\<forall>x x'::'a. R x x' \<longrightarrow> (x \<in> A \<and> x' \<in> A) \<or> (x \<in> -A \<and> x' \<in> -A))"

lemma rel_tcl_closed_under:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and A :: "'a set"
  assumes as_ra: "rel_closed_under R A"
  shows "rel_closed_under R\<^sup>+\<^sup>+ A"
proof -
  obtain P where P: 
    "P = (\<lambda> x x' :: 'a. (x \<in> A \<and> x' \<in> A) \<or> (x \<in> -A \<and> x' \<in> -A))"
    by auto 
  {
    fix x x' :: 'a  
    assume as_major: "R\<^sup>+\<^sup>+ x x'"
    from as_ra P have cases_1: 
      "\<And>x y. R x y \<Longrightarrow> P x y" by (simp add: rel_closed_under_def)
    from P have "\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> R\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
      by blast
    with as_major cases_1 tranclp_trans_induct have "P x x'" by smt    
  }
  then have "\<And>x x'. R\<^sup>+\<^sup>+ x x' \<Longrightarrow> P x x'" by blast
  with P rel_closed_under_def show ?thesis by blast 
qed

lemma tranclp_fun_preserve_gen_1:
  fixes f:: "'a \<Rightarrow> 'b"
    and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and B :: "'b set"
    and x x'::'a
  assumes as_f: "bij_betw f UNIV B"
    and as_R: "rel_closed_under R B"
    and prem: "R\<^sup>+\<^sup>+ (f x) (f x')"
  shows "(\<lambda> x x'. R (f x) (f x'))\<^sup>+\<^sup>+ x x'"
proof -
  obtain g where g: "g = the_inv_into UNIV f" by auto
  obtain gr where gr: "gr = restrict g (range f)" by auto
  obtain P where P: 
    "P = 
    (\<lambda> y y'. y \<in> B \<longrightarrow> y' \<in> B \<longrightarrow> (\<lambda> x x'. R (f x) (f x'))\<^sup>+\<^sup>+ (gr y) (gr y'))" 
    by auto
  obtain y where y: "y = f x" by auto
  with as_f have y_in_B: "y \<in> B" using bij_betw_imp_surj_on by blast
  obtain y' where y': "y' = f x'" by auto
  with as_f have y'_in_B: "y' \<in> B" using bij_betw_imp_surj_on by blast   
  from prem y y' have major: "R\<^sup>+\<^sup>+ y y'" by blast
  from P as_f as_R g y_in_B y'_in_B have cases_1: "\<And>y y'. R y y' \<Longrightarrow> P y y'"
    by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_imp_surj_on 
        f_the_inv_into_f gr restrict_apply' tranclp.r_into_trancl)
  from P have cases_2: 
    "\<And>x y z. R\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> R\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    by (smt ComplD as_R rel_closed_under_def rel_tcl_closed_under tranclp_trans)
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P y y'" by smt
  with P as_f y y' g gr y'_in_B y_in_B show ?thesis 
    by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_imp_surj_on 
        restrict_apply' the_inv_f_f)   
qed

lemma tranclp_fun_preserve_gen_2:
  fixes f:: "'a \<Rightarrow> 'b"
    and R :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and B :: "'b set"
    and x x'::'a
  assumes as_f: "bij_betw f UNIV B"
    and as_R: "rel_closed_under R B"
    and prem: "(\<lambda> x x'. R (f x) (f x'))\<^sup>+\<^sup>+ x x'"
  shows "R\<^sup>+\<^sup>+ (f x) (f x')"
proof -
  obtain P where P: "P = (\<lambda> x x'. (\<lambda> y y'. R y y')\<^sup>+\<^sup>+ (f x) (f x'))" 
    by auto
  obtain r where r: "r = (\<lambda> x x'. R (f x) (f x'))" by auto
  obtain y where y: "y = f x" by auto
  obtain y' where y': "y' = f x'" by auto
  from prem r y y' have major: "r\<^sup>+\<^sup>+ x x'" by blast
  from P as_f r have cases_1: "\<And>y y'. r y y' \<Longrightarrow> P y y'"
    using bij_betw_imp_surj_on bij_is_inj f_the_inv_into_f by fastforce
  from P have cases_2: 
    "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
    by auto
  from tranclp_trans_induct major cases_1 cases_2 have inv_conc: "P x x'" by smt 
  with P as_f y y' show ?thesis by (simp add: bij_is_inj the_inv_f_f)
qed


(*** errorable ***)

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

(*** nullable ***)

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

datatype any = BoolVal "bool\<^sub>\<bottom>" | NatVal "nat\<^sub>\<bottom>" | RealVal "real\<^sub>\<bottom>" | InvalidAny unit

datatype oany = OBoolVal "bool\<^sub>\<bottom>\<^sub>\<box>" | ONatVal "nat\<^sub>\<bottom>\<^sub>\<box>" | ORealVal "real\<^sub>\<bottom>\<^sub>\<box>" | OInvalidAny "unit\<^sub>\<box>"

inductive any_oany :: "any \<Rightarrow> oany \<Rightarrow> bool" where
  "any_oany (BoolVal x) (OBoolVal x\<^sub>\<box>)"
| "any_oany (NatVal x) (ONatVal x\<^sub>\<box>)"
| "any_oany (RealVal x) (ORealVal x\<^sub>\<box>)"
| "any_oany (InvalidAny x) (OInvalidAny x\<^sub>\<box>)"

fun any_to_oany :: "any \<Rightarrow> oany" where
  "any_to_oany (BoolVal x) = (OBoolVal x\<^sub>\<box>)"
| "any_to_oany (NatVal x) = (ONatVal x\<^sub>\<box>)"
| "any_to_oany (RealVal x) = (ORealVal x\<^sub>\<box>)"
| "any_to_oany (InvalidAny x) = (OInvalidAny x\<^sub>\<box>)"

lemma any_oany_eq_fun:
  "any_oany x y \<longleftrightarrow> any_to_oany x = y"
  by (cases x; cases y; auto simp: any_oany.simps)

inductive cast_any :: "any \<Rightarrow> any \<Rightarrow> bool" where
  "cast_any (BoolVal \<bottom>) (InvalidAny ())"
| "cast_any (NatVal \<bottom>) (RealVal \<bottom>)"
| "cast_any (NatVal x\<^sub>\<bottom>) (RealVal (real x)\<^sub>\<bottom>)"
| "cast_any (RealVal \<bottom>) (InvalidAny ())"

inductive cast_oany :: "oany \<Rightarrow> oany \<Rightarrow> bool" where
  "cast_any x y \<Longrightarrow> any_oany x ox \<Longrightarrow> any_oany y oy \<Longrightarrow>
   cast_oany ox oy"
| "cast_oany (OBoolVal \<epsilon>) (OInvalidAny \<epsilon>)"
| "cast_oany (ONatVal \<epsilon>) (ORealVal \<epsilon>)"
| "cast_oany (ORealVal \<epsilon>) (OInvalidAny \<epsilon>)"

lemma cast_any_implies_cast_oany:
  "cast_any x y \<Longrightarrow> cast_oany (any_to_oany x) (any_to_oany y)"
  by (simp add: any_oany_eq_fun cast_oany.intros(1))

lemma cast_oany_implies_cast_any:
  "cast_oany (any_to_oany x) (any_to_oany y) \<Longrightarrow> cast_any x y"
  by (cases x; cases y; simp add: any_oany.simps cast_oany.simps)

lemma cast_oany_closed_under_range: 
  "rel_closed_under cast_oany (range any_to_oany)"
proof -
  obtain B where B: "B = range any_to_oany" by auto
  obtain P where P: 
    "P = (\<lambda> x x'. (x \<in> B \<and> x' \<in> B) \<or> (x \<in> -B \<and> x' \<in> -B))"
    by auto 
  {
    fix x x'
    assume as_c: "cast_oany x x'"
    have obv_p: "(OBoolVal \<epsilon>) \<notin> range any_to_oany" 
    proof - 
      have "\<And>x. any_to_oany x \<noteq> (OBoolVal \<epsilon>)"
        using any_oany.simps any_oany_eq_fun by auto
      then show ?thesis by fastforce
    qed
    have oia_p: "(OInvalidAny \<epsilon>) \<notin> range any_to_oany"
    proof -
      have "\<And>x. any_to_oany x \<noteq> (OInvalidAny \<epsilon>)"
        using any_oany.simps any_oany_eq_fun by auto
      then show ?thesis by fastforce
    qed
    have onv_p: "(ONatVal \<epsilon>) \<notin> range any_to_oany"
    proof -
      have "\<And>x. any_to_oany x \<noteq> (ONatVal \<epsilon>)"
        using any_oany.simps any_oany_eq_fun by auto
      then show ?thesis by fastforce
    qed
    have orv_p: "(ORealVal \<epsilon>) \<notin> range any_to_oany"
    proof -
      have "\<And>x. any_to_oany x \<noteq> (ORealVal \<epsilon>)"
        using any_oany.simps any_oany_eq_fun by auto
      then show ?thesis by fastforce
    qed
    have "cast_oany x x' \<Longrightarrow> P x x'"
    proof (induction rule: cast_oany.induct)
      case (1 x y ox oy) then show ?case using B P any_oany_eq_fun by auto
    next
      case 2 then show ?case
      proof - 
        from B obv_p have obv: "(OBoolVal \<epsilon>) \<in> -B" by simp       
        from B oia_p have oia: "(OInvalidAny \<epsilon>) \<in> -B" by simp
        from P obv oia show ?thesis by auto     
      qed
    next
      case 3 then show ?case
      proof -
        from onv_p B have onv: "(ONatVal \<epsilon>) \<in> -B" by simp       
        from orv_p B have orv: "(ORealVal \<epsilon>) \<in> -B" by simp
        from P onv orv show ?thesis by auto     
      qed
    next
      case 4 then show ?case
      proof -
        from orv_p B have orv: "(ORealVal \<epsilon>) \<in> -B" by simp       
        from oia_p B have oia: "(OInvalidAny \<epsilon>) \<in> -B" by simp
        from P orv oia show ?thesis by auto           
      qed
    qed
  }  
  with B P show ?thesis by (simp add: rel_closed_under_def)
qed

lemma inj_any_to_oany: "inj any_to_oany"
proof
  fix x x' :: any
  assume as_1: "x \<in> UNIV" 
  assume as_2: "x' \<in> UNIV" 
  assume as_3: "any_to_oany x = any_to_oany x'"
  show "x = x'"
  proof (case_tac x)
    show c_1: "\<And>x1::bool\<^sub>\<bottom>. x = BoolVal x1 \<Longrightarrow> x = x'"
      by (metis any.exhaust any_to_oany.simps(1) 
          any_to_oany.simps(2) any_to_oany.simps(3) any_to_oany.simps(4) 
          as_3 nullable.inject oany.distinct(2) oany.distinct(4) 
          oany.inject(1) oany.simps(10))
    show c_2: "\<And>x2::nat\<^sub>\<bottom>. x = NatVal x2 \<Longrightarrow> x = x'"
      by (metis any_to_oany.cases any_to_oany.simps(1) 
          any_to_oany.simps(2) any_to_oany.simps(3) any_to_oany.simps(4) 
          as_3 nullable.inject oany.distinct(1) oany.distinct(9) 
          oany.inject(2) oany.simps(12))
    show c_3: "\<And>x3::real\<^sub>\<bottom>. x = RealVal x3 \<Longrightarrow> x = x'"
      by (metis any.distinct(12) any.distinct(4) any.distinct(8) 
          any_oany.cases any_oany.intros(3) any_to_oany.elims 
          any_to_oany.simps(1) any_to_oany.simps(3) as_3 nullable.inject 
          oany.distinct(12) oany.distinct(3) oany.inject(3) oany.simps(12))
    show c_4: "\<And>x4::unit. x = InvalidAny x4 \<Longrightarrow> x = x'"
      by (metis any.distinct(5) any_to_oany.cases any_to_oany.simps(1) 
          any_to_oany.simps(2) any_to_oany.simps(3) any_to_oany.simps(4) as_3  
          nullable.inject oany.distinct(5) oany.inject(4) oany.simps(14) 
          oany.simps(16))
  qed
qed

lemma bij_any_to_oany: "bij_betw any_to_oany UNIV (range any_to_oany)"
  using inj_any_to_oany by (simp add: bij_betw_def)

lemma tranclp_fun_preserve:
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

lemma tranclp_fun_preserve2:
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

end
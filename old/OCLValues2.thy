theory OCLValues2
  imports
    Main
begin

datatype t = A | B | C

inductive less_t :: "t \<Rightarrow> t \<Rightarrow> bool" where
  "less_t A B"
| "less_t B C"

code_pred [show_modes] less_t .

fun less_t_fun :: "t \<Rightarrow> t \<Rightarrow> bool" where
  "less_t_fun A A = False"
| "less_t_fun A B = True"
| "less_t_fun A C = True"
| "less_t_fun B C = True"
| "less_t_fun B _ = False"
| "less_t_fun C _ = False"

lemma tancl_less_t_code [code]:
  "less_t\<^sup>+\<^sup>+ x y \<longleftrightarrow> less_t_fun x y"
  apply (rule iffI)
  apply (erule tranclp_trans_induct)
  apply (erule less_t.cases; simp)
  apply (metis less_t_fun.elims(2) less_t_fun.simps(3) t.simps(4))
  apply (induct rule: less_t_fun.induct; simp)
  using less_t.intros apply auto
  done

term less_t

value "less_t A B"
value "less_t_fun A C"
value "less_t\<^sup>+\<^sup>+ A C"


class ExpSYM =
  fixes lit :: "int \<Rightarrow> 'a itself"
    and neg :: "'a \<Rightarrow> 'a"
    and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

term "TYPEREP"

instantiation int :: ExpSYM
begin
definition "lit_int (n :: int) \<equiv> n"
definition "neg_int (e :: int) \<equiv> -e"
definition "add_int (e1 :: int) (e2) \<equiv> e1 + e2"
instance ..
end

definition eval :: "int \<Rightarrow> int" where
  "eval \<equiv> id"

term "add (lit 1) (lit 2)"
term "eval (add (lit 1) (lit 2))"
value "eval (add (lit 1) (lit 2))"

class MulSYM =
  fixes mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

instantiation int :: MulSYM
begin
definition "mul_int (e1 :: int) (e2) \<equiv> e1 * e2"
instance ..
end

term "eval (mul (add (lit 1) (lit 2)) (lit 5))"
value "eval (mul (add (lit 1) (lit 2)) (lit 5))"



datatype iexpr =
  IConst int
| Add iexpr iexpr

datatype ('a, 'b) fexpr =
  Lam "'a fexpr \<Rightarrow> 'b fexpr"
| App fexpr iexpr

(*
data Exp env t where
    B :: Bool \<rightarrow> Exp env Bool
    V :: Var env t \<rightarrow> Exp env t
    L :: Exp (a,env) b \<rightarrow> Exp env (a \<rightarrow> b)
    A :: Exp env (a \<rightarrow> b) \<rightarrow> Exp env a \<rightarrow> Exp env b

data Var env t where
    VZ :: Var (t, env) t
    VS :: Var env t \<rightarrow> Var (a, env) t
*)

(*
data Expr a where
    EBool  :: Bool     -> Expr Bool
    EInt   :: Int      -> Expr Int
    EEqual :: Expr Int -> Expr Int  -> Expr Bool
*)

datatype 'a expr =
  EBool bool
| EInt int
| ESum "'a expr" "'a expr"
| EEqual "'a expr" "'a expr"

inductive_set wt_expr :: "'a expr set"


inductive expr_is_wt :: "'a expr \<Rightarrow> bool" where
  "expr_is_wt (EBool _)"
| "expr_is_wt x \<Longrightarrow>
   expr_is_wt y \<Longrightarrow>
   expr_is_wt (EEqual x y)"

fun expr_is_well_typed :: "'a expr \<Rightarrow> bool" where
  "expr_is_well_typed (EBool _) = True"
| "expr_is_well_typed (EInt _) = True"
| "expr_is_well_typed (EEqual (EInt _) (EInt _)) = True"
| "expr_is_well_typed (EEqual (ESum _ _) (EInt _)) = True"
| "expr_is_well_typed (EEqual _ _) = False"

(*
datatype 'a var =
  VZ
| VS "'a var"

datatype 'a exp =
  B bool
| V "'a var"
| L "'a exp"
| A "'a exp" "'a exp"

term UNIV
*)


datatype ty = BoolType | IntType | ListType ty

datatype val = BoolVal bool | IntVal int | SetVal "val fset"

datatype expr =
  BoolConst bool
| IntConst int
| AndExpr expr expr
| SetExpr "expr list"
| SumSetExpr expr
| AllSetExpr expr
(*
*)
(*
locale Symantics =
   fixes lit :: "int \<Rightarrow> 'a"
     and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
     and lam :: "('b \<Rightarrow> 'c) \<Rightarrow> 'd"
     and app :: "'d \<Rightarrow> 'b \<Rightarrow> 'c"
*)

(*
    class Symantics repr where
        int :: Int \<rightarrow> repr Int
        add :: repr Int \<rightarrow> repr Int \<rightarrow> repr Int
        lam :: (repr a \<rightarrow> repr b) \<rightarrow> repr (a \<rightarrow> b)
        app :: repr (a \<rightarrow> b) \<rightarrow> repr a \<rightarrow> repr b
*)




locale symantics =
   fixes lit :: "int \<Rightarrow> 'a"
     and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
     and lam :: "('b \<Rightarrow> 'c) \<Rightarrow> 'd"
     and app :: "'d \<Rightarrow> 'b \<Rightarrow> 'c"


interpretation symantics1: symantics plus .

term "add (lit 1) (lit 2)"

datatype 'a exp1 =
  NConst nat
| Plus "'a exp1"

inductive_set ty1 :: "'a set" where
  ""


datatype expr2 =
  BoolConst bool
| IntConst int
| AndExpr expr expr
| SetExpr "expr list"
| SumSetExpr expr
| AllSetExpr expr


(* Вместо undefined можно возвращать \<bottom>
   А лучше как-то проверять, чтобы такая ситуация гарантированно не возникала
   \<bottom> возвращать не корректно, по идее вообще множество не должно кастоваться
 *)
definition untag_bool_set :: "val fset \<Rightarrow> bool fset" where
  "untag_bool_set xs \<equiv> (\<lambda>x. case x of BoolVal b \<Rightarrow> b) |`| xs"

definition untag_int_set :: "val fset \<Rightarrow> int fset" where
  "untag_int_set xs \<equiv> (\<lambda>x. case x of IntVal b \<Rightarrow> b) |`| xs"

definition is_bool_set :: "val fset \<Rightarrow> bool" where
  "is_bool_set xs \<equiv> fBall xs (\<lambda>x. case x of BoolVal _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition is_int_set :: "val fset \<Rightarrow> bool" where
  "is_int_set xs \<equiv> fBall xs (\<lambda>x. case x of IntVal _ \<Rightarrow> True | _ \<Rightarrow> False)"

value "untag_bool_set {||}"
value "untag_bool_set {|BoolVal True|}"
value "untag_bool_set {|BoolVal True, IntVal 1|}"
value "is_int_set {|BoolVal True, IntVal 1|}"

inductive big_step :: "expr \<Rightarrow> val \<Rightarrow> bool" ("_ \<mapsto> _" [61,61] 60) where
  "BoolConst x \<mapsto> BoolVal x"
| "IntConst x \<mapsto> IntVal x"
| "x \<mapsto> BoolVal a \<Longrightarrow>
   y \<mapsto> BoolVal b \<Longrightarrow>
   AndExpr x y \<mapsto> BoolVal (a \<and> b)"
| "SetExpr [] \<mapsto> SetVal {||}"
| "x \<mapsto> a \<Longrightarrow>
   SetExpr xs \<mapsto> SetVal as \<Longrightarrow>
   SetExpr (x#xs) \<mapsto> SetVal (finsert a as)"
| "s \<mapsto> SetVal xs \<Longrightarrow>
   is_bool_set xs \<Longrightarrow>
   AllSetExpr s \<mapsto> BoolVal (fBall (untag_bool_set xs) id)"
| "s \<mapsto> SetVal xs \<Longrightarrow>
   is_int_set xs \<Longrightarrow>
   SumSetExpr s \<mapsto> IntVal (sum id (fset (untag_int_set xs)))"

code_pred [show_modes] big_step .

values "{x. AllSetExpr (SetExpr [BoolConst True, AndExpr (BoolConst False) (BoolConst True)]) \<mapsto> x}"
values "{x. AllSetExpr (SetExpr [BoolConst True, AndExpr (BoolConst True) (BoolConst True)]) \<mapsto> x}"
values "{x. AllSetExpr (SetExpr [BoolConst True, AndExpr (BoolConst True) (IntConst 1)]) \<mapsto> x}"
values "{x. AllSetExpr (SetExpr [BoolConst True, IntConst 1]) \<mapsto> x}"
values "{x. SumSetExpr (SetExpr [BoolConst True, IntConst 1]) \<mapsto> x}"
values "{x. SumSetExpr (SetExpr [IntConst 1, IntConst 2]) \<mapsto> x}"

value "AllSetExpr (SetExpr [BoolConst True, AndExpr (BoolConst True) (BoolConst True)]) \<mapsto> BoolVal True"





datatype simple_val = BoolVal bool | IntVal int
datatype 'a generic_val =
  VoidVal
| ReqVal 'a
| OptVal "'a option"
| ListVal "'a list"

inductive big_step :: "'a expr \<Rightarrow> 'a generic_val \<Rightarrow> bool" where
  "big_step (BoolConst x) (ReqVal x)"


fun evalB :: "bool expr \<Rightarrow> (bool generic_val) option" where
  "evalB (BoolConst x) = Some (ReqVal x)"

fun eval :: "'a expr \<Rightarrow> ('a generic_val) option" where
  "eval (BoolConst x) = Some (ReqVal x)"
| "eval (ListConst xs) = Some (ListVal xs)"


datatype 'a val = Req 'a

term "Req (1::nat)"

end
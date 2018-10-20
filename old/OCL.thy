theory OCL
  imports Complex_Main ProgLang OCLType
begin
(*
no_notation ProgLang.big_step (infix "\<Rightarrow>" 55)
no_notation ProgLang.typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50)
no_notation ProgLang.etyping (infix "\<turnstile>" 50)
*)
(*** Syntax *****************************************************************************)

(* TODO: A result of combined navigation (self.prop1.prop2...) is a Bag *)
datatype exp =
  NullLiteral
| BooleanLiteral bool
| RealLiteral real
| IntegerLiteral int
| UnlimNatLiteral enat
| StringLiteral string
| Let vname exp exp
| Var vname
| And exp exp
| Or exp exp
| Xor exp exp
| Implies exp exp
| Not exp
| Plus exp exp
| Divide exp exp
| Less exp exp
| AttributeCall exp attr
| AssociationEndCall exp role role

(*** Typing *****************************************************************************)

inductive typing :: "type env \<times> model \<Rightarrow> exp \<Rightarrow> type \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50) where
 NullLiteralT:
  "\<Gamma> \<turnstile> NullLiteral : VoidType" 
|BooleanLiteralT:
  "\<Gamma> \<turnstile> BooleanLiteral c : BooleanType"
|RealLiteralT:
  "\<Gamma> \<turnstile> RealLiteral c : RealType"
|IntegerLiteralT:
  "\<Gamma> \<turnstile> IntegerLiteral c : IntegerType"
|UnlimNatLiteralT:
  "\<Gamma> \<turnstile> UnlimNatLiteral c : UnlimNatType"
|StringLiteralT:
  "\<Gamma> \<turnstile> StringLiteral c : StringType"
|LetT:
  "(\<Gamma>, \<M>) \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>\<^sub>1), \<M>) \<turnstile> body : \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Let var init body : \<tau>"
|VarT:
  "\<Gamma> var = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Var var : \<tau>"
|AndT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = BooleanType \<Longrightarrow>
   \<Gamma> \<turnstile> And a b : BooleanType"
|OrT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = BooleanType \<Longrightarrow>
   \<Gamma> \<turnstile> Or a b : BooleanType"
|XorT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = BooleanType \<Longrightarrow>
   \<Gamma> \<turnstile> Xor a b : BooleanType"
|ImpliesT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = BooleanType \<Longrightarrow>
   \<Gamma> \<turnstile> Implies a b : BooleanType"
|NotT:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow>
   \<tau> = BooleanType \<Longrightarrow>
   \<Gamma> \<turnstile> Not a : BooleanType"
|RealPlusT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = RealType \<Longrightarrow>
   \<Gamma> \<turnstile> Plus a b : RealType"
|IntegerPlusT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = IntegerType \<Longrightarrow>
   \<Gamma> \<turnstile> Plus a b : IntegerType"
|UnlimNatPlusT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = UnlimNatType \<Longrightarrow>
   \<Gamma> \<turnstile> Plus a b : UnlimNatType"
|DivideT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> RealType \<Longrightarrow>
   VoidType < \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Divide a b : RealType"
|LessT:
  "\<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<le> RealType \<Longrightarrow>
   VoidType < \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Less a b : BooleanType"
|AttributeCallT:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : ObjectType cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> AttributeCall src prop : \<tau>"
|AssociationEndCallT:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : ObjectType cls \<Longrightarrow>
   find_assoc2 assocs cls from to = Some end \<Longrightarrow>
   (*find_assoc assocs cls role = assoc \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>*)
   cls2 = assoc_end_class end \<Longrightarrow>
   (*cls |\<in>| assoc_classes ends \<Longrightarrow>
   find_assoc_end ends to = Some i \<Longrightarrow>
   assoc_end_class (ends!i) = cls2 \<Longrightarrow>*)
   (\<Gamma>, \<M>) \<turnstile> AssociationEndCall src from to : ObjectType cls2"

(*code_pred [show_modes] typing .*)

code_pred (modes:
    i * i * i * i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as check_type,
    i * i * i * i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as synthesize_type) typing .

values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile> And (BooleanLiteral True) (NullLiteral) : t}"
values "{t. ([''self''\<mapsto>ObjectType ''Person''], model1) \<turnstile>
  AttributeCall (Var ''self'') ''name'' : t}"
values "{t. ([''self''\<mapsto>ObjectType ''Person''], model1) \<turnstile>
  AssociationEndCall (Var ''self'') ''driver'' ''car'' : t}"

inductive_cases NullLiteralTE[elim!]: "\<Gamma> \<turnstile> NullLiteral : \<tau>"
inductive_cases BooleanLiteralTE[elim!]: "\<Gamma> \<turnstile> BooleanLiteral c : \<tau>"
inductive_cases RealLiteralTE[elim!]: "\<Gamma> \<turnstile> RealLiteral c : \<tau>"
inductive_cases IntegerLiteralTE[elim!]: "\<Gamma> \<turnstile> IntegerLiteral c : \<tau>"
inductive_cases UnlimNatLiteralTE[elim!]: "\<Gamma> \<turnstile> UnlimNatLiteral c : \<tau>"
inductive_cases StringLiteralTE[elim!]: "\<Gamma> \<turnstile> StringLiteral c : \<tau>"
inductive_cases LetTE[elim!]: "\<Gamma> \<turnstile> Let var init body : \<tau>"
inductive_cases VarTE[elim!]: "\<Gamma> \<turnstile> Var var : \<tau>"
inductive_cases AndTE[elim!]: "\<Gamma> \<turnstile> And a b : \<tau>"
inductive_cases OrTE[elim!]: "\<Gamma> \<turnstile> Or a b : \<tau>"
inductive_cases XorTE[elim!]: "\<Gamma> \<turnstile> Xor a b : \<tau>"
inductive_cases ImpliesTE[elim!]: "\<Gamma> \<turnstile> Implies a b : \<tau>"
inductive_cases NotTE[elim!]: "\<Gamma> \<turnstile> Not a : \<tau>"
inductive_cases PlusTE[elim!]: "\<Gamma> \<turnstile> Plus a b : \<tau>"
inductive_cases DivideTE[elim!]: "\<Gamma> \<turnstile> Divide a b : \<tau>"
inductive_cases LessTE[elim!]: "\<Gamma> \<turnstile> Less a b : \<tau>"
inductive_cases AttributeCallTE[elim!]: "\<Gamma> \<turnstile> AttributeCall src prop : \<tau>"
inductive_cases AssociationEndCallTE[elim!]: "\<Gamma> \<turnstile> AssociationEndCall src from to : \<tau>"
(*

values "{t. Map.empty \<turnstile> And NullLiteral NullLiteral : t}"
values "{t. Map.empty \<turnstile> Plus NullLiteral NullLiteral : t}"
values "{t. Map.empty \<turnstile> Less NullLiteral NullLiteral : t}"

values "{t. Map.empty \<turnstile> And (BooleanLiteral True) (NullLiteral) : t}"
values "{t. Map.empty \<turnstile> Plus (UnlimNatLiteral 1) (RealLiteral 2.5) : t}"

value "Map.empty \<turnstile> Plus (UnlimNatLiteral 1) (RealLiteral 2.5) : RealType"
value "Map.empty \<turnstile> Plus (UnlimNatLiteral 1) (IntegerLiteral 2) : RealType"
value "UnlimNatType \<le> RealType"
value "VoidType \<le> RealType"
*)
(*
lemma type_sup_eq:
  "\<tau>\<^sub>1 \<le> \<tau> \<Longrightarrow> \<tau>\<^sub>2 \<le> \<tau> \<Longrightarrow>
   \<tau>\<^sub>1 \<squnion> \<tau>\<^sub>2 = (\<sigma> :: type) \<Longrightarrow>
   \<not> \<tau> < \<sigma>"
  by (metis (full_types) le_iff_sup sup.assoc sup.strict_order_iff)
*)
lemma typing_is_fun:
  "\<Gamma> \<turnstile> exp1 : \<tau>\<^sub>1 \<Longrightarrow>
   \<Gamma> \<turnstile> exp1 : \<tau>\<^sub>2 \<Longrightarrow>
   \<tau>\<^sub>1 = \<tau>\<^sub>2"
  apply (induct \<Gamma> exp1 \<tau>\<^sub>1 arbitrary: \<tau>\<^sub>2 rule: typing.induct)
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
  apply (erule PlusTE; auto)
  apply fastforce
  apply (erule PlusTE; auto)
  apply (erule DivideTE; auto)
  apply (erule LessTE; auto)
  apply fastforce
  apply fastforce
  done

(*** Semantics **************************************************************************)

(* Just case must be first because it allows to prove it by simplification.
   And so it simplifies proofs of more complicated lemmas related to
   semantic equivalence. *)
fun and_val :: "ebool \<Rightarrow> ebool \<Rightarrow> ebool" where
  "and_val (Just a) (Just b)  = Just (a \<and> b)"
| "and_val (Just False) _ = Just False"
| "and_val _ (Just False) = Just False"
| "and_val Error _ = Error"
| "and_val _ Error = Error"
| "and_val Void _ = Void"
| "and_val _ Void = Void"

fun or_val :: "ebool \<Rightarrow> ebool \<Rightarrow> ebool" where
  "or_val (Just a) (Just b)  = Just (a \<or> b)"
| "or_val (Just True) _ = Just True"
| "or_val _ (Just True) = Just True"
| "or_val Error _ = Error"
| "or_val _ Error = Error"
| "or_val Void _ = Void"
| "or_val _ Void = Void"

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<equiv> (x \<and> \<not> y) \<or> (\<not> x \<and> y)"

fun xor_val :: "ebool \<Rightarrow> ebool \<Rightarrow> ebool" where
  "xor_val (Just a) (Just b)  = Just (xor a b)"
| "xor_val Error _ = Error"
| "xor_val _ Error = Error"
| "xor_val Void _ = Void"
| "xor_val _ Void = Void"

fun implies_val :: "ebool \<Rightarrow> ebool \<Rightarrow> ebool" where
  "implies_val (Just False) _ = Just True"
| "implies_val _ (Just True) = Just True"
| "implies_val (Just True) (Just False) = Just False"
| "implies_val Error _ = Error"
| "implies_val _ Error = Error"
| "implies_val Void _ = Void"
| "implies_val _ Void = Void"

fun not_val :: "ebool \<Rightarrow> ebool" where
  "not_val (Just a) = Just (\<not>a)"
| "not_val Error = Error"
| "not_val Void  = Void"
(*
lemma and_commut:
  "and_val a b = and_val b a"
  by (cases a; cases b; simp; metis and_val.simps)

lemma or_commut:
  "or_val a b = or_val b a"
  by (cases a; cases b; simp; metis or_val.simps)

lemma xor_commut:
  "xor_val a b = xor_val b a"
  by (cases a; cases b; simp add: xor_def; metis xor_val.simps)

lemma not_not_elim:
  "not_val (not_val a) = a"
  by (cases a; simp)

lemma log11:
  "not_val (and_val a b) = or_val (not_val a) (not_val b)"
  by (cases a; cases b; simp; metis (full_types) and_val.simps not_val.simps or_val.simps)

lemma log12:
  "not_val (or_val a b) = and_val (not_val a) (not_val b)"
  by (cases a; cases b; simp; metis (full_types) and_val.simps not_val.simps or_val.simps)

lemma log21:
  "and_val (and_val a b) c = and_val a (and_val b c)"
  by (cases a; cases b; cases c; simp; metis (full_types) and_val.simps)

lemma log22:
  "or_val (or_val a b) c = or_val a (or_val b c)"
  by (cases a; cases b; cases c; simp; metis (full_types) or_val.simps)

lemma log23:
  "xor_val (xor_val a b) c = xor_val a (xor_val b c)"
  by (cases a; cases b; cases c; simp add: xor_def; metis xor_val.simps)

lemma log31:
  "\<exists>a b c. and_val (or_val a b) c \<noteq> or_val (and_val a c) (and_val b c)"
  by (metis and_val.simps(13) and_val.simps(7) errorable.distinct(5) or_val.simps(5) or_val.simps(7))

lemma log32:
  "\<exists>a b c. or_val (and_val a b) c \<noteq> and_val (or_val a c) (or_val b c)"
  by (metis and_val.simps(5) and_val.simps(7) errorable.distinct(5) or_val.simps(13) or_val.simps(7))

lemma implies_eq_not_or:
  "implies_val a b = or_val (not_val a) b"
  by (cases a; cases b; simp; metis (full_types) implies_val.simps or_val.simps)
*)

fun real_plus_val :: "ereal \<Rightarrow> ereal \<Rightarrow> ereal" where
  "real_plus_val (Just a) (Just b) = Just (a + b)"
| "real_plus_val _ _ = Error"

fun integer_plus_val :: "eint \<Rightarrow> eint \<Rightarrow> eint" where
  "integer_plus_val (Just a) (Just b) = Just (a + b)"
| "integer_plus_val _ _ = Error"

fun unlim_nat_plus_val :: "eunat \<Rightarrow> eunat \<Rightarrow> eunat" where
  "unlim_nat_plus_val (Just \<infinity>) (Just _) = Error"
| "unlim_nat_plus_val (Just _) (Just \<infinity>) = Error"
| "unlim_nat_plus_val (Just a) (Just b) = Just (a + b)"
| "unlim_nat_plus_val _ _ = Error"
(*
value "real_plus_val (Just 1.54567456) (Just 2)"
value "unlim_nat_plus_val (Just \<infinity>) (Just 2)"
*)

fun real_divide_val :: "ereal \<Rightarrow> ereal \<Rightarrow> ereal" where
  "real_divide_val (Just a) (Just b) = (if b = 0 then Error else Just (a / b))"
| "real_divide_val _ _ = Error"

lemma real_divide_val_has_value:
  "x = Just a \<Longrightarrow>
   y = Just b \<Longrightarrow>
   b \<noteq> 0 \<Longrightarrow>
   \<exists>z. real_divide_val x y = Just z"
  by simp

fun integer_divide_val :: "eint \<Rightarrow> eint \<Rightarrow> ereal" where
  "integer_divide_val (Just a) (Just b) = (if b = 0 then Error else Just (a / b))"
| "integer_divide_val _ _ = Error"

lemma integer_divide_val_has_value:
  "x = Just a \<Longrightarrow>
   y = Just b \<Longrightarrow>
   b \<noteq> 0 \<Longrightarrow>
   \<exists>z. integer_divide_val x y = Just z"
  by simp

fun unlim_nat_to_integer :: "eunat \<Rightarrow> eint" where
  "unlim_nat_to_integer (Just \<infinity>) = Error"
| "unlim_nat_to_integer (Just a) = Just (the_enat a)"
| "unlim_nat_to_integer Void = Void"
| "unlim_nat_to_integer Error = Error"

definition unlim_nat_divide_val :: "eunat \<Rightarrow> eunat \<Rightarrow> ereal" where
  "unlim_nat_divide_val a b \<equiv>
    integer_divide_val (unlim_nat_to_integer a) (unlim_nat_to_integer b)"
(*
value "unlim_nat_divide_val (Just 5) (Just 2)"
value "unlim_nat_divide_val (Just \<infinity>) (Just 2)"
*)

fun real_less_val :: "ereal \<Rightarrow> ereal \<Rightarrow> ebool" where
  "real_less_val (Just a) (Just b) = Just (a < b)"
| "real_less_val _ _ = Error"

fun integer_less_val :: "eint \<Rightarrow> eint \<Rightarrow> ebool" where
  "integer_less_val (Just a) (Just b) = Just (a < b)"
| "integer_less_val _ _ = Error"

fun unlim_nat_less_val :: "eunat \<Rightarrow> eunat \<Rightarrow> ebool" where
  "unlim_nat_less_val (Just \<infinity>) (Just _) = Just False"
| "unlim_nat_less_val (Just _) (Just \<infinity>) = Just True"
| "unlim_nat_less_val (Just a) (Just b) = Just (a < b)"
| "unlim_nat_less_val _ _ = Error"
(*
datatype oval = ObjectVal oid
type_synonym aval = "val + oval"
abbreviation NullVal where "NullVal \<equiv> Inl val.NullVal"
abbreviation BooleanVal where "BooleanVal \<equiv> Inl val.BooleanVal"
abbreviation RealVal where "RealVal \<equiv> Inl val.RealVal"
abbreviation IntegerVal where "IntegerVal \<equiv> Inl val.IntegerVal"
abbreviation UnlimNatVal where "UnlimNatVal \<equiv> Inl val.UnlimNatVal"
abbreviation StringVal where "StringVal \<equiv> Inl val.StringVal"
abbreviation AnyVal where "AnyVal \<equiv> Inl val.AnyVal"
abbreviation ObjectVal where "ObjectVal \<equiv> Inr oval.ObjectVal"
*)
inductive big_step :: "exp \<times> val env \<times> data \<Rightarrow> val \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
 NullLiteralVal:
  "(NullLiteral, e) \<Rightarrow> NullVal"
|BooleanLiteralVal:
  "(BooleanLiteral c, e) \<Rightarrow> BooleanVal (Just c)"
|RealLiteralVal:
  "(RealLiteral c, e) \<Rightarrow> RealVal (Just c)"
|IntegerLiteralVal:
  "(IntegerLiteral c, e) \<Rightarrow> IntegerVal (Just c)"
|UnlimNatLiteralVal:
  "(UnlimNatLiteral c, e) \<Rightarrow> UnlimNatVal (Just c)"
|StringLiteralVal:
  "(StringLiteral c, e) \<Rightarrow> StringVal (Just c)"
|LetVal:
  "(init, e, d) \<Rightarrow> x \<Longrightarrow>
   object_val_ok (\<T> x) x objects \<Longrightarrow>
   (body, e(var \<mapsto> x), d) \<Rightarrow> v \<Longrightarrow>
   d = (objects, attr_vals, links) \<Longrightarrow>
   (Let var init body, e, d) \<Rightarrow> v"
|VarVal:
  "e var = Some v \<Longrightarrow>
   (Var var, e, d) \<Rightarrow> v"
|AndVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   (And a b, e) \<Rightarrow> BooleanVal (and_val xb yb)"
|OrVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   (Or a b, e) \<Rightarrow> BooleanVal (or_val xb yb)"
|XorVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   (Xor a b, e) \<Rightarrow> BooleanVal (xor_val xb yb)"
|ImpliesVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (BooleanVal xb, BooleanVal yb) \<Longrightarrow>
   (Implies a b, e) \<Rightarrow> BooleanVal (implies_val xb yb)"
|NotVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   x = BooleanVal xb \<Longrightarrow>
   (Not a, e) \<Rightarrow> BooleanVal (not_val xb)"
|RealPlusVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   (Plus a b, e) \<Rightarrow> RealVal (real_plus_val xn yn)"
|IntegerPlusVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (IntegerVal xn, IntegerVal yn) \<Longrightarrow>
   (Plus a b, e) \<Rightarrow> IntegerVal (integer_plus_val xn yn)"
|UnlimNatPlusVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   (Plus a b, e) \<Rightarrow> UnlimNatVal (unlim_nat_plus_val xn yn)"
|RealDivideVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   (Divide a b, e) \<Rightarrow> RealVal (real_divide_val xn yn)"
|IntegerDivideVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (IntegerVal xn, IntegerVal yn) \<Longrightarrow>
   (Divide a b, e) \<Rightarrow> RealVal (integer_divide_val xn yn)"
|UnlimNatDivideVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   (Divide a b, e) \<Rightarrow> RealVal (unlim_nat_divide_val xn yn)"
|RealLessVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   (Less a b, e) \<Rightarrow> BooleanVal (real_less_val xn yn)"
|IntegerLessVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (IntegerVal xn, IntegerVal yn) \<Longrightarrow>
   (Less a b, e) \<Rightarrow> BooleanVal (integer_less_val xn yn)"
|UnlimNatLessVal:
  "(a, e) \<Rightarrow> x \<Longrightarrow>
   (b, e) \<Rightarrow> y \<Longrightarrow>
   (x, y) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   (Less a b, e) \<Rightarrow> BooleanVal (unlim_nat_less_val xn yn)"
|AttributeCallVal:
  "d = (objects, attr_vals, links) \<Longrightarrow>
   (src, e, d) \<Rightarrow> ObjectVal cls obj \<Longrightarrow>
   (* It's interesting that we have to check class *)
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   (AttributeCall src prop, e, d) \<Rightarrow> v"
(* TODO: В зависимости от множественности ассоциации в модели значение будет
   либо ссылкой, либо множеством. Для N-арных ассоциаций - всегда множество.
   Проблема в том, что модель тут не доступна. Как вариант, перед вычислением
   выражения можно преобразовывать его в более сложное выражение. В котором
   из множества будет извлекаться единственный элемент. Преобразование
   будет принимать на вход модель. *)
|AssociationEndCallVal:
  "d = (objects, attr_vals, links) \<Longrightarrow>
   (src, e, d) \<Rightarrow> ObjectVal cls obj \<Longrightarrow>
   (* It's interesting that we have to check class *)
   fmlookup objects obj = Some cls \<Longrightarrow>
   find_link2 links obj from to = Some objs \<Longrightarrow>
   obj2 = obj \<Longrightarrow> (* Bug *)
   (*find_link links obj role = assoc \<Longrightarrow>
   fmlookup links assoc = Some link_set \<Longrightarrow>
   fmlookup link_set role = Some obj2 \<Longrightarrow>*)
   fmlookup objects obj2 = Some cls2 \<Longrightarrow>
   (*fmlookup assocs assoc = Some ends \<Longrightarrow>
   find_assoc_end ends from = Some i \<Longrightarrow>
   find_assoc_end ends to = Some j \<Longrightarrow>
   linked_objs link_set obj i j = vs \<Longrightarrow>
   obj2 |\<in>| vs \<Longrightarrow>
   fmlookup objects obj2 = Some cls2 \<Longrightarrow>
   v = ObjectVal cls2 obj2 \<Longrightarrow>*)
   v = ObjectVals cls2 objs \<Longrightarrow>
   (AssociationEndCall src from to, e, d) \<Rightarrow> v"

code_pred (modes:
    i * i * i * i * i \<Rightarrow> i \<Rightarrow> bool as check_val,
    i * i * i * i * i \<Rightarrow> o \<Rightarrow> bool as eval) big_step .

values "{t. (AttributeCall (Var ''self'') ''name'',
  [''self''\<mapsto>ObjectVal ''Person'' ''Ivan''], data1) \<Rightarrow> t}"
values "{t. (AssociationEndCall (Var ''self'') ''driver'' ''car'',
  [''self''\<mapsto>ObjectVal ''Person'' ''Ivan''], data1) \<Rightarrow> t}"

inductive_cases NullLiteralE[elim!]: "(NullLiteral, e) \<Rightarrow> v"
inductive_cases BooleanLiteralE[elim!]: "(BooleanLiteral c, e) \<Rightarrow> v"
inductive_cases RealLiteralE[elim!]: "(RealLiteral c, e) \<Rightarrow> v"
inductive_cases IntegerLiteralE[elim!]: "(IntegerLiteral c, e) \<Rightarrow> v"
inductive_cases UnlimNatLiteralE[elim!]: "(UnlimNatLiteral c, e) \<Rightarrow> v"
inductive_cases StringLiteralE[elim!]: "(StringLiteral c, e) \<Rightarrow> v"
inductive_cases LetE[elim!]: "(Let var init body, e) \<Rightarrow> v"
inductive_cases VarE[elim!]: "(Var var, e) \<Rightarrow> v"
inductive_cases AndE[elim!]: "(And a b, e) \<Rightarrow> v"
inductive_cases OrE[elim!]: "(Or a b, e) \<Rightarrow> v"
inductive_cases XorE[elim!]: "(Xor a b, e) \<Rightarrow> v"
inductive_cases ImpliesE[elim!]: "(Implies a b, e) \<Rightarrow> v"
inductive_cases NotE[elim!]: "(Not a, e) \<Rightarrow> v"
inductive_cases PlusE[elim!]: "(Plus a b, e) \<Rightarrow> v"
inductive_cases DivideE[elim!]: "(Divide a b, e) \<Rightarrow> v"
inductive_cases LessE[elim!]: "(Less a b, e) \<Rightarrow> v"
inductive_cases AttributeCallE[elim!]: "(AttributeCall src prop, e) \<Rightarrow> v"
inductive_cases AssociationEndCallE[elim!]: "(AssociationEndCall src role, e) \<Rightarrow> v"
(*
code_pred [show_modes] big_step .

values "{(t,s). (UnlimNatVal (Just 1), UnlimNatVal (Just 2)) as* (t,s)}"
values "{t. (Plus (UnlimNatLiteral 1) (UnlimNatLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Plus (IntegerLiteral 1) (IntegerLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Plus (RealLiteral 1.5) (RealLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Plus (RealLiteral 1.5) (IntegerLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Plus (UnlimNatLiteral 1) (IntegerLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Plus (UnlimNatLiteral \<infinity>) (IntegerLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Less (UnlimNatLiteral 2) (UnlimNatLiteral \<infinity>), Map.empty) \<Rightarrow> t}"
values "{t. (Less (UnlimNatLiteral \<infinity>) (UnlimNatLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Less (IntegerLiteral 2) (UnlimNatLiteral \<infinity>), Map.empty) \<Rightarrow> t}"
values "{t. (Less (UnlimNatLiteral 1) (IntegerLiteral 2), Map.empty) \<Rightarrow> t}"
values "{t. (Less (RealLiteral 1.5) (IntegerLiteral 2), Map.empty) \<Rightarrow> t}"
*)
lemma big_step_is_fun:
  "(exp1, env) \<Rightarrow> v\<^sub>1 \<Longrightarrow>
   (exp1, env) \<Rightarrow> v\<^sub>2 \<Longrightarrow>
   v\<^sub>1 = v\<^sub>2"
  apply (induct arbitrary: v\<^sub>2 rule: big_step.induct)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply blast
  apply auto[1]
  apply (erule AndE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule OrE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule XorE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule ImpliesE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule NotE; blast)
  apply (erule PlusE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule PlusE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule PlusE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule DivideE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule DivideE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule DivideE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule LessE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule LessE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply (erule LessE; auto simp: cast.simps cast_eq_def cast_either.simps)
  apply force
  apply force
  done

(*** Environment Typing *****************************************************************)

(*
fun val_of_type :: "type \<Rightarrow> val" where
  "val_of_type VoidType = NullVal" |
  "val_of_type AnyType = NullVal" |
(*  "val_of_type VoidType = BooleanVal (Void)" |
  "val_of_type AnyType = BooleanVal (Void)" |*)
  "val_of_type BooleanType = BooleanVal (Just False)" |
  "val_of_type RealType = RealVal (Just 0)" |
  "val_of_type IntegerType = IntegerVal (Just 0)" |
  "val_of_type UnlimNatType = UnlimNatVal (Just 0)" |
  "val_of_type StringType = StringVal (Just '''')"
*)
definition default_tenv :: "val env \<Rightarrow> type env" where
  "default_tenv env \<equiv> (map_option type_of_val) \<circ> env"
(*
definition default_env :: "type env \<Rightarrow> val env" where
  "default_env \<Gamma> \<equiv> (map_option val_of_type) \<circ> \<Gamma>"

definition etyping :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>" 50) where
  "\<Gamma> \<turnstile> env \<equiv> \<forall>x. (case (env x, \<Gamma> x) of
    (Some v, Some t) \<Rightarrow> type_of_val v = t |
    (None, None) \<Rightarrow> True |
    _ \<Rightarrow> False)"
*)
definition etyping1 :: "type env \<Rightarrow> val env \<Rightarrow> bool" (infix "\<turnstile>1" 50)  where
  "\<Gamma> \<turnstile>1 env \<equiv> \<forall>x. the ((map_option type_of_val) (env x)) = the (\<Gamma> x)"

lemma etyping2_eq1:
  "etyping \<Gamma> env \<Longrightarrow> etyping1 \<Gamma> env"
  by (smt None_eq_map_option_iff eq_iff etyping1_def etyping_def fst_conv option.case_eq_if option.map_sel prod.case_eq_if snd_conv)
(*  by (smt case_prod_conv etyping1_def etyping_def option.case_eq_if option.map_sel option.simps(8) subtype_fun_def)*)
(*  by (smt case_prod_conv etyping1_def etyping_def option.case_eq_if option.map_sel option.simps(8) subtype.intros(1))*)
(*
lemma type_eq_then_subtype:
  "type_of_val v = t \<Longrightarrow> type_of_val v \<le> t"
  by (simp add: subtype_fun_def)
(*  by (simp add: subtype.intros(1))*)
*)
(*
lemma default_tenv_exists:
  "default_tenv env \<turnstile> env"
  by (simp add: default_tenv_def etyping_def option.case_eq_if option.map_sel)
*)
(*
lemma default_env_exists:
  "\<Gamma> \<turnstile> default_env \<Gamma>"
  apply (simp add: etyping_def)
(*  by (smt comp_apply default_env_def map_option_is_None option.case_eq_if option.map_sel subtype.intros(1) subtype.intros(2) type_of_val.simps(1) type_of_val.simps(2) type_of_val.simps(3) val_of_type.elims val_of_type.simps(3))*)
*)

(*** Lemma 1 ****************************************************************************)

lemma type_preservation:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> (exp1, env) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow>
   \<T> v = \<tau>"
  apply (induct arbitrary: env v rule: typing.induct)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  using etyping2_preserv_type2 apply blast
  (*using etyping_def apply auto[1]*)
  (*apply (erule etyping2.cases)
  apply (erule VarE)
  apply (simp add: object_vals_ok_def)
  apply (metis (mono_tags, lifting) etyping_preserv_type option.simps(5))*)
  apply (erule VarE; simp add: etyping2_preserv_type)
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply auto[1]
  apply (erule PlusE)
  using type_of_pair_eq apply fastforce
  using type_of_pair_eq apply fastforce
  using type_of_pair_eq apply fastforce
  apply (erule PlusE)
  using type_of_pair_eq apply fastforce
  using type_of_pair_eq apply fastforce
  using type_of_pair_eq apply fastforce
  apply (erule PlusE)
  using type_of_pair_eq apply fastforce
  using type_of_pair_eq apply fastforce
  using type_of_pair_eq apply fastforce
  (*apply (erule PlusE)
  apply simp
  apply (metis type_of_pair_eq type_of_val.simps(4))
  apply (metis type_of_pair_eq type_of_val.simps(5))
  apply (erule PlusE)
  apply (metis type_of_pair_eq type_of_val.simps(3))
  apply simp
  apply (metis type_of_pair_eq type_of_val.simps(5))
  apply (erule PlusE)
  apply (metis type_of_pair_eq type_of_val.simps(3))
  apply (metis type_of_pair_eq type_of_val.simps(4))
  apply simp*)
  apply (erule DivideE; simp)
  apply (erule LessE; simp)
  apply (erule AttributeCallE)
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)[1]
  apply (smt conforms_to_model.intros etyping2.intros model_preserv_type type.inject type_of_val.simps(8))
  apply (erule AssociationEndCallE)
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)[1]
  done


lemma q:
  "links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   find_assoc assocs cls role = Some end \<Longrightarrow>

   find_link links obj role = Some obj2 \<Longrightarrow>
   fmlookup objects obj2 = Some cls2a \<Longrightarrow>

   cls2a = assoc_end_class end"
  apply (simp add: links_ok_def)
  apply (simp add: find_assoc_def find_link_def)


lemma q:
  "(*\<M> = (classes, attrs, assocs) \<Longrightarrow>
   env = (e, objects, attr_vals, links) \<Longrightarrow>

   (\<Gamma>, \<M>) \<turnstile> src : ObjectType cls \<Longrightarrow>
       (\<And>a aa ab b v.
           (src, a, aa, ab, b) \<Rightarrow> v \<Longrightarrow>
           (\<Gamma>, classes, attrs, assocs) \<turnstile> (a, aa, ab, b) \<Longrightarrow> \<T> v = ObjectType cls) \<Longrightarrow>
       cls2 = assoc_end_class end \<Longrightarrow>
       v = ObjectVal cls2a obj2 \<Longrightarrow>
       (src, e, objects, attr_vals, links) \<Rightarrow> ObjectVal clsa obj \<Longrightarrow>
       fmlookup objects obj = Some clsa \<Longrightarrow>
       \<Gamma> \<turnstile> e \<Longrightarrow>
       object_vals_ok \<Gamma> e objects \<Longrightarrow>
       model_is_ok (classes, attrs, assocs) \<Longrightarrow>
       data_is_ok (objects, attr_vals, links) \<Longrightarrow>
       fmran objects |\<subseteq>| classes \<Longrightarrow>
       attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
       assoc = find_assoc assocs cls role \<Longrightarrow>
*)
   links_ok objects assocs links \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   fmlookup assocs (find_assoc assocs cls role) = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>

   fmlookup links (find_link links obj role) = Some link_set \<Longrightarrow>
   fmlookup link_set role = Some obj2 \<Longrightarrow>
   fmlookup objects obj2 = Some cls2a \<Longrightarrow>

   cls2a = assoc_end_class end"
  apply (simp add: links_ok_def)
  apply (simp add: find_assoc_def find_assocs2_def)
  apply (simp add: find_link_def find_links2_def)


lemma q:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
       (\<Gamma>, \<M>) \<turnstile> src : ObjectType cls \<Longrightarrow>
       (\<And>env v. (src, env) \<Rightarrow> v \<Longrightarrow> (\<Gamma>, \<M>) \<turnstile> env \<Longrightarrow> \<T> v = ObjectType cls) \<Longrightarrow>
       find_assoc assocs cls role = assoc \<Longrightarrow>
       fmlookup assocs assoc = Some ends \<Longrightarrow>
       fmlookup ends role = Some end \<Longrightarrow>
       cls2 = assoc_end_class end \<Longrightarrow>
       (AssociationEndCall src role, env) \<Rightarrow> v \<Longrightarrow>
       (\<Gamma>, \<M>) \<turnstile> env \<Longrightarrow> \<T> v = ObjectType cls2"
  apply (erule AssociationEndCallE)
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)[1]



































lemma type_preservation2:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> (exp1, env, d) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> (env, d) \<Longrightarrow>
   d = (objects, attr_vals, links) \<Longrightarrow>
   object_val_ok \<tau> v objects"
  apply (induct arbitrary: env v rule: typing.induct)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  using etyping2_preserv_type2 type_preservation apply auto[1]
  apply (erule etyping2.cases)
  apply (simp add: object_vals_ok_def)
  apply (metis VarE fst_conv option.simps(5))
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (simp add: object_val_ok_def)
  apply (erule AttributeCallE)
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)
  apply (metis attr_vals_is_ok_then_object_val_ok conforms_to_model.intros etyping2.intros type.inject type_of_val.simps(8) type_preservation)
  done

(* Well-typed expression has value *)
(*
lemma let_simp22:
  "\<Gamma> \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   type_of_val v\<^sub>1 = \<tau>\<^sub>1 \<Longrightarrow>
   (\<Gamma> \<turnstile> env \<Longrightarrow> (init, env) \<Rightarrow> v\<^sub>1) \<Longrightarrow>
   \<Gamma>(var\<mapsto>\<tau>\<^sub>1) \<turnstile> body : \<tau> \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>\<^sub>1) \<turnstile> env(var\<mapsto>v\<^sub>1) \<Longrightarrow> (body, env(var\<mapsto>v\<^sub>1)) \<Rightarrow> v) \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow> (Let var init body, env) \<Rightarrow> v"
  by (simp add: etyping_def LetVal)

lemma let_simp22:
  "(\<Gamma>,\<M>) \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   type_of_val v\<^sub>1 = \<tau>\<^sub>1 \<Longrightarrow>
   ((\<Gamma>,\<M>) \<turnstile> (env,d) \<Longrightarrow> (init, env,d) \<Rightarrow> v\<^sub>1) \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>\<^sub>1),\<M>) \<turnstile> body : \<tau> \<Longrightarrow>
   ((\<Gamma>(var\<mapsto>\<tau>\<^sub>1),\<M>) \<turnstile> (env(var\<mapsto>v\<^sub>1),d) \<Longrightarrow> (body, env(var\<mapsto>v\<^sub>1),d) \<Rightarrow> v) \<Longrightarrow>
   (\<Gamma>,\<M>) \<turnstile> (env,d) \<Longrightarrow> (Let var init body, env,d) \<Rightarrow> v"
  by (simp add: LetVal etyping2_preserv_type2)

lemma let_simp31:
  "(exp1, env) \<Rightarrow> v1 \<Longrightarrow>
   (\<Gamma> \<turnstile> env \<Longrightarrow> \<Gamma> \<turnstile> exp1 : \<tau>1) \<Longrightarrow>
   (exp2, env(var\<mapsto>v1)) \<Rightarrow> v2 \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>1) \<turnstile> env(var\<mapsto>v1) \<Longrightarrow> \<Gamma>(var\<mapsto>\<tau>1) \<turnstile> exp2 : \<tau>) \<Longrightarrow>
   (Let var exp1 exp2, env) \<Rightarrow> v2 \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow> \<Gamma> \<turnstile> (Let var exp1 exp2) : \<tau>"
  by (simp add: etyping_def type_preservation typing.intros(7))
*)
lemma let_simp31:
  "(exp1, env, d) \<Rightarrow> v1 \<Longrightarrow>
   ((\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow> (\<Gamma>, \<M>) \<turnstile> exp1 : \<tau>1) \<Longrightarrow>
   (exp2, env(var\<mapsto>v1), d) \<Rightarrow> v2 \<Longrightarrow>
   ((\<Gamma>(var\<mapsto>\<tau>1), \<M>) \<turnstile> (env(var\<mapsto>v1), d) \<Longrightarrow> (\<Gamma>(var\<mapsto>\<tau>1), \<M>) \<turnstile> exp2 : \<tau>) \<Longrightarrow>
   (Let var exp1 exp2, env, d) \<Rightarrow> v2 \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow> (\<Gamma>, \<M>) \<turnstile> (Let var exp1 exp2) : \<tau>"
  apply (erule LetE)
  by (metis LetT Pair_inject big_step_is_fun etyping2_preserv_type2 type_preservation)

lemma boolean_val_pair_exists2:
  "\<Gamma> \<turnstile> a : \<tau>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>2 \<Longrightarrow>
   (a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow>
   \<tau>1 \<squnion> \<tau>2 = BooleanType \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (BooleanVal xn, BooleanVal yn)"
  by (simp add: boolean_val_pair_exists type_preservation)

lemma real_val_pair_exists2:
  "\<Gamma> \<turnstile> a : \<tau>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>2 \<Longrightarrow>
   (a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow>
   \<tau>1 \<squnion> \<tau>2 = RealType \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (RealVal xn, RealVal yn)"
  by (simp add: real_val_pair_exists type_preservation)

lemma integer_val_pair_exists2:
  "\<Gamma> \<turnstile> a : \<tau>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>2 \<Longrightarrow>
   (a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow>
   \<tau>1 \<squnion> \<tau>2 = IntegerType \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (IntegerVal xn, IntegerVal yn)"
  by (simp add: integer_val_pair_exists type_preservation)

lemma unlim_nat_val_pair_exists2:
  "\<Gamma> \<turnstile> a : \<tau>1 \<Longrightarrow>
   \<Gamma> \<turnstile> b : \<tau>2 \<Longrightarrow>
   (a, env) \<Rightarrow> x \<Longrightarrow>
   (b, env) \<Rightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile> env \<Longrightarrow>
   \<tau>1 \<squnion> \<tau>2 = UnlimNatType \<Longrightarrow>
   \<exists>xn yn. (x, y) as* (UnlimNatVal xn, UnlimNatVal yn)"
  by (simp add: unlim_nat_val_pair_exists type_preservation)

lemma q11:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   \<exists>vals v.
      fmlookup attr_vals obj = Some vals \<and>
      fmlookup vals prop = Some v"
  by (meson attr_vals_is_ok_then attr_vals_is_ok_then2_rev attr_vals_is_ok_then_rev fmdomI fmdom_notI)

lemma q12:
  "(\<Gamma>, \<M>) \<turnstile> (e, d) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : ObjectType cls \<Longrightarrow>
   (src, e, d) \<Rightarrow> ObjectVal cls2 obj \<Longrightarrow>
   d = (objects, attr_vals, links) \<Longrightarrow>
   cls = cls2"
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)
  using conforms_to_model.intros etyping2.intros type_preservation by fastforce

lemma object_type_implies_object_value:
  "\<T> v = \<tau> \<Longrightarrow>
   \<tau> = ObjectType cls \<Longrightarrow>
   \<exists>obj. v = ObjectVal cls obj"
  by (cases v ; simp)

lemma let51:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : ObjectType cls \<Longrightarrow>
   ((\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow> (src, env, d) \<Rightarrow> v1) \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow>
(*
   d = (objects, attr_vals, links) \<Longrightarrow>
   v1 = ObjectVal cls obj \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>

   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
*)
   \<exists>v. (AttributeCall src prop, env, d) \<Rightarrow> v"
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)
  by (smt AttributeCallVal conforms_to_model.intros etyping2.intros object_type_implies_object_value object_val_ok_def q11 type_preservation type_preservation2)

(*** Lemma 2 ****************************************************************************)

lemma type_system_is_sound:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>v. (exp1, env) \<Rightarrow> v"
  apply (induct arbitrary: env rule: typing.induct)
  using NullLiteralVal apply blast
  using BooleanLiteralVal apply blast
  using RealLiteralVal apply blast
  using IntegerLiteralVal apply blast
  using UnlimNatLiteralVal apply blast
  using StringLiteralVal apply blast
  apply (smt Pair_inject etyping2.cases LetVal etyping2_preserv_type2 type_preservation type_preservation2)
  apply (smt Pair_inject VarVal etyping2.cases var_has_type_impies_has_value)
  (*apply (smt etyping2.cases let41)
  apply (metis Pair_inject VarVal etyping2.cases var_has_type_impies_has_value)
  apply (metis (no_types, lifting) let_simp22 type_preservation)
  apply (meson VarVal var_has_type_impies_has_value)*)
  apply (meson AndVal boolean_val_pair_exists2)
  apply (meson OrVal boolean_val_pair_exists2)
  apply (meson XorVal boolean_val_pair_exists2)
  apply (meson ImpliesVal boolean_val_pair_exists2)
  using NotVal boolean_val_exists type_preservation apply blast
  apply (meson RealPlusVal real_val_pair_exists2)
  apply (meson IntegerPlusVal integer_val_pair_exists2)
  apply (meson UnlimNatPlusVal unlim_nat_val_pair_exists2)
  apply (erule num_type_cases; simp)
  apply (meson RealDivideVal real_val_pair_exists2)
  apply (meson IntegerDivideVal integer_val_pair_exists2)
  apply (meson UnlimNatDivideVal unlim_nat_val_pair_exists2)
  apply (erule num_type_cases; simp)
  apply (meson RealLessVal real_val_pair_exists2)
  apply (meson IntegerLessVal integer_val_pair_exists2)
  apply (meson UnlimNatLessVal unlim_nat_val_pair_exists2)
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)
  apply (meson conforms_to_model.intros etyping2.intros let51)
  done

(* If has value then has type *)

lemma boolean_val_pair_type:
  "(x, y) as* (BooleanVal xn, BooleanVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y = BooleanType"
  by (simp add: type_of_pair_eq)

lemma real_val_pair_type:
  "(x, y) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y = RealType"
  by (simp add: type_of_pair_eq)

lemma real_val_pair_type2:
  "(x, y) as* (RealVal xn, RealVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y \<le> RealType \<and>
   VoidType < type_of_val x \<squnion> type_of_val y"
  by (simp add: real_val_pair_type)

lemma integer_val_pair_type:
  "(x, y) as* (IntegerVal xn, IntegerVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y = IntegerType"
  by (simp add: type_of_pair_eq)

lemma integer_val_pair_type2:
  "(x, y) as* (IntegerVal xn, IntegerVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y \<le> RealType \<and>
   VoidType < type_of_val x \<squnion> type_of_val y"
  by (simp add: dual_order.strict_implies_order integer_val_pair_type)

lemma unlim_nat_val_pair_type:
  "(x, y) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y = UnlimNatType"
  by (simp add: type_of_pair_eq)

lemma unlim_nat_val_pair_type2:
  "(x, y) as* (UnlimNatVal xn, UnlimNatVal yn) \<Longrightarrow>
   type_of_val x \<squnion> type_of_val y \<le> RealType \<and>
   VoidType < type_of_val x \<squnion> type_of_val y"
  by (simp add: dual_order.strict_implies_order unlim_nat_val_pair_type)

lemma let52:
  "(\<And>v1. (exp11, env, d) \<Rightarrow> v1 \<Longrightarrow> (\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow> (\<Gamma>, \<M>) \<turnstile> exp11 : \<tau>1) \<Longrightarrow>
   (\<And>v v1. (exp12, env(x1\<mapsto>v1), d) \<Rightarrow> v \<Longrightarrow>
    (\<Gamma>(x1\<mapsto>\<tau>1), \<M>) \<turnstile> (env(x1\<mapsto>v1), d) \<Longrightarrow>
    Ex (OCL.typing (\<Gamma>(x1\<mapsto>\<tau>1), \<M>) exp12)) \<Longrightarrow>
   (exp.Let x1 exp11 exp12, env, d) \<Rightarrow> v \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow>
   Ex (OCL.typing (\<Gamma>, \<M>) (exp.Let x1 exp11 exp12))"
  apply (erule LetE)
  apply (auto)
  apply (metis LetT etyping2_preserv_type2 type_preservation)
  done

lemma let53:
  "(\<And>v1. (exp11, env, d) \<Rightarrow> v1 \<Longrightarrow> (\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow> \<exists>\<tau>1. (\<Gamma>, \<M>) \<turnstile> exp11 : \<tau>1) \<Longrightarrow>
   (\<And>v v1 \<tau>1. (exp12, env(x1\<mapsto>v1), d) \<Rightarrow> v \<Longrightarrow>
    (\<Gamma>(x1\<mapsto>\<tau>1), \<M>) \<turnstile> (env(x1\<mapsto>v1), d) \<Longrightarrow>
    Ex (OCL.typing (\<Gamma>(x1\<mapsto>\<tau>1), \<M>) exp12)) \<Longrightarrow>
   (exp.Let x1 exp11 exp12, env, d) \<Rightarrow> v \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> (env, d) \<Longrightarrow>
   Ex (OCL.typing (\<Gamma>, \<M>) (exp.Let x1 exp11 exp12))"
  by (metis (no_types, hide_lams) let52)

lemma q13:
  "attr_vals_is_ok attrs objects attr_vals \<Longrightarrow>
   fmlookup objects obj = Some cls \<Longrightarrow>
   fmlookup attr_vals obj = Some vals \<Longrightarrow>
   fmlookup vals prop = Some v \<Longrightarrow>
   \<exists>cls_attrs \<tau>.
      fmlookup attrs cls = Some cls_attrs \<and>
      fmlookup cls_attrs prop = Some \<tau>"
  by (meson attr_vals_is_ok_then attr_vals_is_ok_then2_rev attr_vals_is_ok_then_rev fmdom'I fmdom'_notI)

lemma object_value_implies_object_type:
  "\<T> v = \<tau> \<Longrightarrow>
   v = ObjectVal cls obj \<Longrightarrow>
   \<tau> = ObjectType cls"
  by (cases v ; simp)

















(*** Lemma 3 ****************************************************************************)

lemma type_system_is_complete:
  "(exp1, env) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>"
  apply (induct exp1 arbitrary: env v \<Gamma>)
  using NullLiteralT apply blast
  using BooleanLiteralT apply blast
  using RealLiteralT apply blast
  using IntegerLiteralT apply blast
  using UnlimNatLiteralT apply blast
  using StringLiteralT apply blast
  apply (smt etyping2.simps let53)
  apply (smt Pair_inject VarE VarT etyping2.cases var_has_value_impies_has_type)
  (*apply (smt LetE let_simp31)
  apply (meson VarE typing.intros(8) var_has_value_impies_has_type)*)
  apply (erule AndE; metis boolean_val_pair_type type_preservation typing.intros(9))
  apply (erule OrE; metis boolean_val_pair_type type_preservation typing.intros(10))
  apply (erule XorE; metis boolean_val_pair_type type_preservation typing.intros(11))
  apply (erule ImpliesE; metis boolean_val_pair_type type_preservation typing.intros(12))
  apply (erule NotE)
  using type_of_val.simps(2) type_preservation typing.intros(13) apply blast
  apply (erule PlusE)
  apply (metis type_preservation typing.intros(14) real_val_pair_type)
  apply (metis type_preservation typing.intros(15) integer_val_pair_type)
  apply (metis type_preservation typing.intros(16) unlim_nat_val_pair_type)
  apply (erule DivideE)
  apply (metis type_preservation typing.intros(17) real_val_pair_type2)
  apply (metis type_preservation typing.intros(17) integer_val_pair_type2)
  apply (metis type_preservation typing.intros(17) unlim_nat_val_pair_type2)
  apply (erule LessE)
  apply (metis type_preservation typing.intros(18) real_val_pair_type2)
  apply (metis type_preservation typing.intros(18) integer_val_pair_type2)
  apply (metis type_preservation typing.intros(18) unlim_nat_val_pair_type2)
  apply (erule AttributeCallE)
  apply (erule etyping2.cases)
  apply (erule conforms_to_model.cases)
  apply (auto)
  apply (smt AttributeCallT conforms_to_model.intros etyping2.intros object_value_implies_object_type q13 type_preservation)
  done

(*** Lemma 4 ****************************************************************************)

lemma has_type_eq_has_value:
  "\<Gamma> \<turnstile> env \<Longrightarrow> (\<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>) = (\<exists>v. (exp1, env) \<Rightarrow> v)"
  using type_system_is_sound type_system_is_complete by auto



(*
inductive_cases AndTE2[elim!]: "\<Gamma> \<turnstile> And (BooleanLiteral True) (BooleanLiteral False) : \<tau>"

lemma well_typed_and:
  "\<Gamma> \<turnstile> And a b : \<tau> \<Longrightarrow> \<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<Gamma> \<turnstile> a : \<tau>\<^sub>1 \<and> \<Gamma> \<turnstile> b : \<tau>\<^sub>2"
  by blast
*)
(*
lemma well_typed_exp_has_value7:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> \<exists>env v. \<Gamma> \<turnstile> env \<and> (exp1, env) \<Rightarrow> v"
  using default_env_exists well_typed_exp_has_value by blast
*)

(*** Lemma 5 ****************************************************************************)

lemma has_value_then_well_typed7:
  "(exp1, env) \<Rightarrow> v \<Longrightarrow> \<exists>\<Gamma> \<tau>. \<Gamma> \<turnstile> env \<and> \<Gamma> \<turnstile> exp1 : \<tau>"
  using default_tenv_exists type_system_is_complete by blast

(*


https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus#Typing_rules
exp1 :: exp - well-formed, syntactically correct
\<Gamma> \<turnstile> exp1 : \<tau> - typing relation
\<Gamma> \<turnstile> exp1 : \<tau> - exp1 is well-typed

bidirectional type checking:
\<Gamma> \<turnstile> exp1 \<Leftarrow> \<tau> - type checking (all inputs)
\<Gamma> \<turnstile> exp1 \<Rightarrow> \<tau> - type synthesis (\<tau> is output)

type system is sound = it rejects all incorrect programs
prog lang is type safe = it discourages or prevents type errors

proving the preservation of correctness under some program transformation

http://logan.tw/posts/2014/11/12/soundness-and-completeness-of-the-type-system/
A type-system is sound implies that all of type-checked programs are correct (in the other words, all of the incorrect program can't be type checked), i.e. there won't be any false negative [1].
A type-system is complete implies that all of the correct program can be accepted by the type checker, i.s. there won't be any false positive [2].
[1]	For negative, we mean that the type checker claims that there is no error in the input program, i.e. the input program is correct.
[2]	For positive, we mean that the type checker claims that there are some errors in the input program, i.e. the input program is incorrect.

https://en.wikipedia.org/wiki/Program_transformation
transformed program is semantically equivalent

A generalisation of semantic equivalence is the notion of program refinement: one program is a refinement of another if it terminates on all the initial states for which the original program terminates, and for each such state it is guaranteed to terminate in a possible final state for the original program. In other words, a refinement of a program is more defined and more deterministic than the original program. If two programs are refinements of each other, then the programs are equivalent.

https://stackoverflow.com/questions/23049730/soundness-and-completeness-of-a-algorithm

http://www.cs.cornell.edu/courses/cs6110/2013sp/lectures/lec27-sp13.pdf
type preservation


http://isabelle.in.tum.de/website-Isabelle2009/dist/Isabelle/doc/locales.pdf
A map ϕ between partial orders \<sqsubseteq> and \<prec> is called order preserving if x \<sqsubseteq> y implies ϕ x \<prec> ϕ y. 


lemma type_preservation:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> (exp1, env) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow>
   type_of_val v = \<tau>"

lemma type_system_is_sound:
  "\<Gamma> \<turnstile> exp1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>v. (exp1, env) \<Rightarrow> v"

lemma type_system_is_complete:
  "(exp1, env) \<Rightarrow> v \<Longrightarrow> \<Gamma> \<turnstile> env \<Longrightarrow> \<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>"

Это лишнее, нет термина для выполнения обоих утверждений:
lemma has_type_eq_has_value:
  "\<Gamma> \<turnstile> env \<Longrightarrow> (\<exists>\<tau>. \<Gamma> \<turnstile> exp1 : \<tau>) = (\<exists>v. (exp1, env) \<Rightarrow> v)"

Тут добавляется только \<Gamma> по умолчанию, возможно, лемма лишняя
lemma has_value_then_well_typed7:
  "(exp1, env) \<Rightarrow> v \<Longrightarrow> \<exists>\<Gamma> \<tau>. \<Gamma> \<turnstile> env \<and> \<Gamma> \<turnstile> exp1 : \<tau>"

*)

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

interpretation OCL: prog_lang type_of_val typing big_step etyping
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

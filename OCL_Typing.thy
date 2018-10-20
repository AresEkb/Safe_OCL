theory OCL_Typing
  imports
    OCL_Types
    OCL_Model
    OCL_Syntax
begin

(*** Typing *****************************************************************************)

(* Используем индуктивное определение, потому что-то не для любой комбинации
   будет тип. Частично определенные функции точно отпадают. А option всё усложняет *)

inductive unop_typing where
  "\<tau> \<le> Boolean[?] \<Longrightarrow>
   unop_typing Not \<tau> \<tau>"
| "\<tau> \<le> Real[?] \<Longrightarrow>
   unop_typing UMinus \<tau> \<tau>"

inductive to_required_type where
  "to_required_type \<tau>[1] \<sigma> \<tau>[1]"
| "to_required_type \<tau>[?] \<sigma> \<tau>[1]"
| "to_required_type OclVoid \<sigma> \<sigma>[1]"

inductive binop_typing where
  "\<sigma> \<squnion> \<rho> = \<tau> \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   binop_typing Or \<sigma> \<rho> \<tau>"
| "\<sigma> \<squnion> \<rho> = \<tau> \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   binop_typing And \<sigma> \<rho> \<tau>"
| "\<sigma> \<squnion> \<rho> = \<pi> \<Longrightarrow>
   \<pi> \<le> Real[?] \<Longrightarrow>
   to_required_type \<pi> UnlimitedNatural \<tau> \<Longrightarrow>
   binop_typing Plus \<sigma> \<rho> \<tau>"
| "\<sigma> \<squnion> \<rho> \<le> Real[?] \<Longrightarrow>
   binop_typing Less \<sigma> \<rho> Boolean[1]"


code_pred [show_modes] binop_typing .

inductive typing :: "type env \<times> model \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50) where
 NullLiteralT:
  "\<Gamma> \<turnstile> NullLiteral : OclVoid"
|BooleanLiteralT:
  "\<Gamma> \<turnstile> BooleanLiteral c : Boolean[1]"
|RealLiteralT:
  "\<Gamma> \<turnstile> RealLiteral c : Real[1]"
|IntegerLiteralT:
  "\<Gamma> \<turnstile> IntegerLiteral c : Integer[1]"
|UnlimNatLiteralT:
  "\<Gamma> \<turnstile> UnlimNatLiteral c : UnlimitedNatural[1]"
|StringLiteralT:
  "\<Gamma> \<turnstile> StringLiteral c : String[1]"

|LetT:
  "(\<Gamma>, \<M>) \<turnstile> init : \<tau>\<^sub>1 \<Longrightarrow>
   (\<Gamma>(var\<mapsto>\<tau>\<^sub>1), \<M>) \<turnstile> body : \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Let var init body : \<tau>"
|VarT:
  "\<Gamma> var = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> Var var : \<tau>"

|UnaryOperationCallT:
  "(\<Gamma>, \<M>) \<turnstile> x : \<sigma> \<Longrightarrow>
   unop_typing op \<sigma> \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> UnaryOperationCall op x : \<tau>"
|BinaryOperationCallT:
  "(\<Gamma>, \<M>) \<turnstile> x : \<sigma> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> y : \<rho> \<Longrightarrow>
   binop_typing op \<sigma> \<rho> \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> BinaryOperationCall op x y : \<tau>"

code_pred (modes:
    i * i * i * i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool as check_type,
    i * i * i * i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as synthesize_type) typing .

values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall And (BooleanLiteral True) (NullLiteral) : t}"
values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall And (BooleanLiteral True) (BooleanLiteral False) : t}"
(* В статье нужно описать разные варианты
   Разрешаем мы такие выражения или нет и какой у них тип
   По идее сейчас сделано нормально, пусть будет void *)
values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall And (NullLiteral) (NullLiteral) : t}"

values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall Plus (UnlimNatLiteral (unat 1)) (RealLiteral 2.5) : t}"
values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall Plus (UnlimNatLiteral (unat 1)) (IntegerLiteral 2) : t}"
values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall Plus (UnlimNatLiteral (unat 1)) (NullLiteral) : t}"
values "{t. (Map.empty, (fempty, fmempty, fmempty)) \<turnstile>
  BinaryOperationCall Plus (NullLiteral) (NullLiteral) : t}"

values "{t. Map.empty \<turnstile> Plus (UnlimNatLiteral 1) (RealLiteral 2.5) : t}"
value "Map.empty \<turnstile> Plus (UnlimNatLiteral 1) (RealLiteral 2.5) : RealType"
value "Map.empty \<turnstile> Plus (UnlimNatLiteral 1) (IntegerLiteral 2) : RealType"

values "{t. ([''self''\<mapsto>ObjectType ''Person''], model1) \<turnstile>
  AttributeCall (Var ''self'') ''name'' : t}"
values "{t. ([''self''\<mapsto>ObjectType ''Person''], model1) \<turnstile>
  AssociationEndCall (Var ''self'') ''driver'' ''car'' : t}"


values "{t. Map.empty \<turnstile> And NullLiteral NullLiteral : t}"
values "{t. Map.empty \<turnstile> Plus NullLiteral NullLiteral : t}"
values "{t. Map.empty \<turnstile> Less NullLiteral NullLiteral : t}"




(*
|BooleanExprT:
  "\<Gamma> \<turnstile> x : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> y : \<rho> \<Longrightarrow>
   \<tau> = \<sigma> \<squnion> \<rho> \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> BooleanExpr op x y : \<tau>"
|NotT:
  "\<Gamma> \<turnstile> x : \<tau> \<Longrightarrow>
   \<tau> \<le> Boolean[?] \<Longrightarrow>
   \<Gamma> \<turnstile> Not x : \<tau>"

|RealArithmeticExprT:
  "\<Gamma> \<turnstile> x : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> y : \<rho> \<Longrightarrow>
   \<tau> = \<sigma> \<squnion> \<rho> \<Longrightarrow>
   Integer[?] < \<tau> \<Longrightarrow>
   \<tau> \<le> Real[?] \<Longrightarrow>
   \<Gamma> \<turnstile> ArithmeticExpr op x y : \<tau>"
|IntegerArithmeticExprT:
  "\<Gamma> \<turnstile> x : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> y : \<rho> \<Longrightarrow>
   \<tau> = \<sigma> \<squnion> \<rho> \<Longrightarrow>
   UnlimitedNatural[?] < \<tau> \<Longrightarrow>
   \<tau> \<le> Integer[?] \<Longrightarrow>
   \<Gamma> \<turnstile> ArithmeticExpr op x y : \<tau>"
|UnlimitedNaturalArithmeticExprT:
  "\<Gamma> \<turnstile> x : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> y : \<rho> \<Longrightarrow>
   \<tau> = \<sigma> \<squnion> \<rho> \<Longrightarrow>
   \<tau> \<le> UnlimitedNatural[?] \<Longrightarrow>
   \<Gamma> \<turnstile> ArithmeticExpr op x y : \<tau>"

|ComparisionExprT:
  "\<Gamma> \<turnstile> x : \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> y : \<rho> \<Longrightarrow>
   \<tau> = \<sigma> \<squnion> \<rho> \<Longrightarrow>
   \<tau> \<le> Real[?] \<Longrightarrow>
   \<Gamma> \<turnstile> ComparisionExpr op x y : Boolean[1]"

|AttributeCallT:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : (ObjectType cls)[?] \<Longrightarrow>
   fmlookup attrs cls = Some cls_attrs \<Longrightarrow>
   fmlookup cls_attrs prop = Some \<tau> \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> AttributeCall src prop : \<tau>"
*)
(*|AssociationEndCallT:
  "\<M> = (classes, attrs, assocs) \<Longrightarrow>
   (\<Gamma>, \<M>) \<turnstile> src : (ObjectType cls)[?] \<Longrightarrow>
   find_assoc2 assocs cls from to = Some end \<Longrightarrow>
   (*find_assoc assocs cls role = assoc \<Longrightarrow>
   fmlookup assocs assoc = Some ends \<Longrightarrow>
   fmlookup ends role = Some end \<Longrightarrow>*)
   cls2 = assoc_end_class end \<Longrightarrow>
   (*cls |\<in>| assoc_classes ends \<Longrightarrow>
   find_assoc_end ends to = Some i \<Longrightarrow>
   assoc_end_class (ends!i) = cls2 \<Longrightarrow>*)
   (\<Gamma>, \<M>) \<turnstile> AssociationEndCall src from to : (ObjectType cls2)[?]"
*)
(*code_pred [show_modes] typing .*)



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


end

theory OCL_Syntax
  imports
    Complex_Main
    OCL_Common
begin
(*
datatype boolean_op = AndOp | OrOp | ImpliesOp | XorOp
datatype arithmetic_op = PlusOp | MinusOp | MultOp | DevideOp
datatype comparision_op = LessOp | LessEqOp | GreaterOp | GreaterEqOp
datatype equality_op = EqualOp | NotEqualOp
*)
datatype unop =
  Not
| UMinus
| ToInteger | ToString

datatype binop =
  Or | Xor | And | Implies
| Plus | Minus | Mult | Divide | Div | Mod
| Equal | NotEqual
| Less | LessEq | Greater | GreaterEq

(* Большая часть выражений - это не часть синтаксиса, а операции из стандартной библиотеки
   Подумать, как их описывать
 *)

(*
  Не реализовано:
  EnumLiteralExp
  InvalidLiteralExp (есть на схеме на 52 странице, но по-моему это ошибка)
  CollectionLiteralExp
  TupleLiteralExp
  MessageExp
  StateExp
  TypeExp
  IfExp
  



  
*)


(* TODO: A result of combined navigation (self.prop1.prop2...) is a Bag *)
datatype expr =
  NullLiteral
| BooleanLiteral bool
| RealLiteral real
| IntegerLiteral int
| UnlimNatLiteral unat
| StringLiteral string

| Let vname expr expr
| Var vname

| UnaryOperationCall unop expr
| BinaryOperationCall binop expr expr

(*| EqualityExpr equality_op expr expr

| BooleanExpr boolean_op expr expr
| Not expr

| ArithmeticExpr arithmetic_op expr expr
| UnaryMinus expr expr

| ComparisionExpr comparision_op expr expr*)

| AttributeCall expr attr
| AssociationEndCall expr role role

end

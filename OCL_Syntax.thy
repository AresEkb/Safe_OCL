(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* OCL Syntax *}
theory OCL_Syntax
  imports Complex_Main OCL_Common OCL_Types
begin

section{* Standard Library Operations *}

(* Only BasicOCL (EssentialOCL) is defined. So there is no states, messages, etc. *)

(* В A.3.1.1 говорится, что в предыдущих версиях OCL это были обычные операции
   с аргументом типа OclType. А сейчас это просто синтаксические конструкции -
   ровно как я их и описал *)

(* oclType() - эту операцию проблематично описать, непонятно какой у неё тип.
   В спецификации говорится, что метатипа OclType сейчас нет, соответственно тип
   не может быть значением, не может быть результатом какой-то операции.
   Учитывая, что эта операция используется в основном для определения
   oclAsType(), oclIsTypeOf(), oclIsKindOf(), то может она и не нужна?
   Может её просто забыли убрать или оставили по ошибке *)

datatype typeop = OclAsTypeOp | OclIsTypeOfOp | OclIsKindOfOp
| SelectByKindOp | SelectByTypeOp

datatype suptype_binop = EqualOp | NotEqualOp

datatype any_unop = OclAsSetOp | OclIsNewOp
| OclIsUndefinedOp | OclIsInvalidOp | OclLocaleOp | ToStringOp

datatype boolean_unop = NotOp
datatype boolean_binop = AndOp | OrOp | XorOp | ImpliesOp

datatype numeric_unop = UMinusOp | AbsOp | FloorOp | RoundOp | ToIntegerOp
datatype numeric_binop = PlusOp | MinusOp | MultOp | DivideOp
| DivOp | ModOp | MaxOp | MinOp
| LessOp | LessEqOp | GreaterOp | GreaterEqOp

datatype string_unop = SizeOp | ToUpperCaseOp | ToLowerCaseOp | CharactersOp
| ToBooleanOp | ToIntegerOp | ToRealOp
datatype string_binop = ConcatOp | IndexOfOp | EqualsIgnoreCaseOp | AtOp
| LessOp | LessEqOp | GreaterOp | GreaterEqOp
datatype string_ternop = SubstringOp

datatype collection_unop = CollectionSizeOp | IsEmptyOp | NotEmptyOp
| CollectionMaxOp | CollectionMinOp | SumOp
| AsSetOp | AsOrderedSetOp | AsSequenceOp | AsBagOp | FlattenOp
| FirstOp | LastOp | ReverseOp
datatype collection_binop = IncludesOp | ExcludesOp
| CountOp| IncludesAllOp | ExcludesAllOp | ProductOp
| UnionOp | IntersectionOp | SetMinusOp | SymmetricDifferenceOp
| IncludingOp | ExcludingOp
| AppendOp | PrependOp | CollectionAtOp | CollectionIndexOfOp
datatype collection_ternop = InsertAtOp | SubOrderedSetOp | SubSequenceOp

type_synonym unop =
  "any_unop + boolean_unop + numeric_unop + string_unop + collection_unop"
type_synonym binop =
  "suptype_binop + boolean_binop + numeric_binop + string_binop + collection_binop"
type_synonym ternop =
  "string_ternop + collection_ternop"

declare [[coercion "Inl :: any_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inl :: boolean_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl :: numeric_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_unop \<Rightarrow> unop"]]

declare [[coercion "Inl :: suptype_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inl :: boolean_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl :: numeric_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_binop \<Rightarrow> binop"]]

declare [[coercion "Inl :: string_ternop \<Rightarrow> ternop"]]
declare [[coercion "Inr :: collection_ternop \<Rightarrow> ternop"]]

datatype iterator = AnyIter | ClosureIter | CollectIter | CollectNestedIter
| ExistsIter | ForAllIter | IsUniqueIter | OneIter
| RejectIter | SelectIter | SortedByIter

section{* Expressions *}

datatype collection_literal_kind =
  CollectionKind | SetKind | OrderedSetKind | BagKind | SequenceKind

datatype 'a expr =
  Literal "'a literal_expr"
| Let (var : vname) (type : "'a type") (init_expr : "'a expr") (body_expr : "'a expr")
| Var (var : vname)
| If (if_expr : "'a expr") (then_expr : "'a expr") (else_expr : "'a expr")
| Call "'a call_expr"
and 'a literal_expr =
  NullLiteral
| InvalidLiteral
| BooleanLiteral (boolean_symbol : bool)
| RealLiteral (real_symbol : real)
| IntegerLiteral (integer_symbol : int)
| UnlimitedNaturalLiteral (unlimited_natural_symbol : unat)
| StringLiteral (string_symbol : string)
| EnumLiteral (type : "'a type") (literal : vname)
| CollectionLiteral (kind : collection_literal_kind)
    (parts : "'a collection_literal_part_expr list")
| TupleLiteral (elements : "(nat \<times> 'a type \<times> 'a expr) list")
and 'a collection_literal_part_expr =
  CollectionItem (item : "'a expr")
| CollectionRange (first : "'a expr") (last : "'a expr")
and 'a call_expr =
  OclType (source : "'a expr")
| TypeOperationCall typeop (source : "'a expr") (type : "'a type")
| UnaryOperationCall unop (source : "'a expr")
| BinaryOperationCall binop (source : "'a expr") (arg1 : "'a expr")
| TernaryOperationCall ternop (source : "'a expr") (arg1 : "'a expr") (arg2 : "'a expr")
| Iterate (source : "'a expr") (iterators : "vname list")
    (var : vname) (type : "'a type") (init_expr : "'a expr") (body_expr : "'a expr")
| Iterator iterator (source : "'a expr") (iterators : "vname list") (body_expr : "'a expr")
| AttributeCall (source : "'a expr") attr
| AssociationEndCall (source : "'a expr") role

declare [[coercion "Literal :: 'a literal_expr \<Rightarrow> 'a expr"]]
declare [[coercion "Call :: 'a call_expr \<Rightarrow> 'a expr"]]

end

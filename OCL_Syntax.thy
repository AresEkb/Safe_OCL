(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>OCL Syntax\<close>
theory OCL_Syntax
  imports Complex_Main Object_Model OCL_Types
begin

section \<open>Preliminaries\<close>

type_synonym vname = "String.literal"
type_synonym 'a env = "vname \<rightharpoonup>\<^sub>f 'a"

text \<open>
  In OCL @{text "1 + \<infinity> = \<bottom>"}. So we don't use @{typ enat} and
  define the new data type.\<close>

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

section \<open>Standard Library Operations\<close>

text \<open>
  The OCL specification doesn't define OclType. So we implement
  type operations as a syntactic constructs.\<close>

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
| ExistsIter | ForAllIter | OneIter | IsUniqueIter
| SelectIter | RejectIter | SortedByIter

section \<open>Expressions\<close>

datatype collection_literal_kind =
  SetKind | OrderedSetKind | BagKind | SequenceKind | CollectionKind

text \<open>
  It could be defined as 2 boolean values (is_arrow_call, is_safe_call).
  Also we could derive is_arrow_call value automatically based on an operation kind.
  But it's much easier and more natural to define such an enumeration.\<close>
datatype call_kind = DotCall | ArrowCall | SafeDotCall | SafeArrowCall

datatype 'a expr =
  Literal "'a literal_expr"
| Let (var : vname) (type : "'a type") (init_expr : "'a expr") (body_expr : "'a expr")
| Var (var : vname)
| If (if_expr : "'a expr") (then_expr : "'a expr") (else_expr : "'a expr")
| Call (source : "'a expr") (kind : call_kind) "'a call_expr"
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
| TupleLiteral (elements : "(literal \<times> 'a type \<times> 'a expr) list")
and 'a collection_literal_part_expr =
  CollectionItem (item : "'a expr")
| CollectionRange (first : "'a expr") (last : "'a expr")
and 'a call_expr =
  OclType
| TypeOperation typeop (type : "'a type")
| UnaryOperation unop
| BinaryOperation binop
    (arg1 : "'a expr")
| TernaryOperation ternop
    (arg1 : "'a expr") (arg2 : "'a expr")
| Iterate (iterators : "vname list")
    (var : vname) (type : "'a type") (init_expr : "'a expr") (body_expr : "'a expr")
| Iterator iterator
    (iterators : "vname list") (body_expr : "'a expr")
| Attribute attr
| AssociationEnd role
| Operation oper (args : "'a expr list")

definition "tuple_literal_name \<equiv> fst"
definition "tuple_literal_type \<equiv> fst \<circ> snd"
definition "tuple_literal_expr \<equiv> snd \<circ> snd"

declare [[coercion "Literal :: 'a literal_expr \<Rightarrow> 'a expr"]]
(*declare [[coercion "Call :: 'a call_expr \<Rightarrow> 'a expr"]]*)

abbreviation "OclTypeCall src s \<equiv> Call src s OclType"
abbreviation "TypeOperationCall src s op ty \<equiv> Call src s (TypeOperation op ty)"
abbreviation "UnaryOperationCall src s op \<equiv> Call src s (UnaryOperation op)"
abbreviation "BinaryOperationCall src s op a \<equiv> Call src s (BinaryOperation op a)"
abbreviation "TernaryOperationCall src s op a b \<equiv> Call src s (TernaryOperation op a b)"
abbreviation "IterateCall src s its v ty init body \<equiv> Call src s (Iterate its v ty init body)"
abbreviation "IteratorCall src s op its body \<equiv> Call src s (Iterator op its body)"
abbreviation "AttributeCall src s attr \<equiv> Call src s (Attribute attr)"
abbreviation "AssociationEndCall src s role \<equiv> Call src s (AssociationEnd role)"
abbreviation "OperationCall src s op as \<equiv> Call src s (Operation op as)"

end

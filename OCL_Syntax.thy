(*  Title:       Safe OCL
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Abstract Syntax\<close>
theory OCL_Syntax
  imports Complex_Main Object_Model OCL_Types
begin

section \<open>Preliminaries\<close>

type_synonym vname = "String.literal"
type_synonym 'a env = "vname \<rightharpoonup>\<^sub>f 'a"

text \<open>
  In OCL @{text "1 + \<infinity> = \<bottom>"}. So we do not use @{typ enat} and
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
  unfolding unat_def infinity_unat_def
  apply (metis Rep_unat_inverse option.collapse)
  apply (metis Abs_unat_inverse UNIV_I option.sel)
  by (simp add: Abs_unat_inject)

section \<open>Standard Library Operations\<close>

datatype metaop = AllInstancesOp

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

type_synonym unop = "any_unop + boolean_unop + numeric_unop + string_unop + collection_unop"

declare [[coercion "Inl :: any_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inl :: boolean_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl :: numeric_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_unop \<Rightarrow> unop"]]

type_synonym binop = "suptype_binop + boolean_binop + numeric_binop + string_binop + collection_binop"

declare [[coercion "Inl :: suptype_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inl :: boolean_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl :: numeric_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_binop \<Rightarrow> binop"]]

type_synonym ternop = "string_ternop + collection_ternop"

declare [[coercion "Inl :: string_ternop \<Rightarrow> ternop"]]
declare [[coercion "Inr :: collection_ternop \<Rightarrow> ternop"]]

type_synonym op = "unop + binop + ternop + oper"

declare [[coercion "Inl \<circ> Inl :: any_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inl :: boolean_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inr \<circ> Inl :: numeric_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_unop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inl \<circ> Inl :: suptype_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inl :: boolean_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inl :: numeric_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_binop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inr \<circ> Inl \<circ> Inl :: string_ternop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl \<circ> Inr :: collection_ternop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inr \<circ> Inr :: oper \<Rightarrow> op"]]

datatype iterator = AnyIter | ClosureIter | CollectIter | CollectNestedIter
| ExistsIter | ForAllIter | OneIter | IsUniqueIter
| SelectIter | RejectIter | SortedByIter

section \<open>Expressions\<close>

datatype collection_literal_kind =
  SetKind | OrderedSetKind | BagKind | SequenceKind | CollectionKind

text \<open>
  A call kind could be defined as 2 boolean values (@{text "is_arrow_call"},
  @{text "is_safe_call"}). Also we could derive @{text "is_arrow_call"}
  value automatically based on an operation kind.
  But it's much easier and more natural to use the following enumeration.\<close>
datatype call_kind = DotCall | ArrowCall | SafeDotCall | SafeArrowCall

text \<open>
  We do not define a @{text Classifier} type (a type of all types),
  because it will add unnecessary complications to the theory.
  So we have to define type operations as a pure syntactic constructs.
  We do not define @{text Type} expressions either.\<close>

text \<open>
  We do not define @{text InvalidLiteral}, because it allows us to
  exclude @{text OclInvalid} type from typing rules. It simplifies
  the types system.\<close>

datatype 'a expr =
  Literal "'a literal_expr"
| Let (var : vname) (type : "'a type") (init_expr : "'a expr") (body_expr : "'a expr")
| Var (var : vname)
| If (if_expr : "'a expr") (then_expr : "'a expr") (else_expr : "'a expr")
| MetaOperationCall (type : "'a type") metaop
| StaticOperationCall (type : "'a type") oper (args : "'a expr list")
| Call (source : "'a expr") (kind : call_kind) "'a call_expr"
and 'a literal_expr =
  NullLiteral
| BooleanLiteral (boolean_symbol : bool)
| RealLiteral (real_symbol : real)
| IntegerLiteral (integer_symbol : int)
| UnlimitedNaturalLiteral (unlimited_natural_symbol : unat)
| StringLiteral (string_symbol : string)
| EnumLiteral (enum_type : "'a enum") (enum_literal : elit)
| CollectionLiteral (kind : collection_literal_kind)
    (parts : "'a collection_literal_part_expr list")
| TupleLiteral (tuple_elements : "(telem \<times> 'a type \<times> 'a expr) list")
and 'a collection_literal_part_expr =
  CollectionItem (item : "'a expr")
| CollectionRange (first : "'a expr") (last : "'a expr")
and 'a call_expr =
  TypeOperation typeop (type : "'a type")
| Attribute attr
| AssociationEnd role
| Operation op (args : "'a expr list")
| TupleElement telem
| Iterate (iterators : "vname list") (var : vname) (type : "'a type")
    (init_expr : "'a expr") (body_expr : "'a expr")
| Iterator iterator (iterators : "vname list") (body_expr : "'a expr")

definition "tuple_element_name \<equiv> fst"
definition "tuple_element_type \<equiv> fst \<circ> snd"
definition "tuple_element_expr \<equiv> snd \<circ> snd"

declare [[coercion "Literal :: 'a literal_expr \<Rightarrow> 'a expr"]]

abbreviation "TypeOperationCall src k op ty \<equiv>
  Call src k (TypeOperation op ty)"
abbreviation "AttributeCall src attr \<equiv>
  Call src DotCall (Attribute attr)"
abbreviation "AssociationEndCall src role \<equiv>
  Call src DotCall (AssociationEnd role)"
abbreviation "OperationCall src k op as \<equiv>
  Call src k (Operation op as)"
abbreviation "TupleElementCall src elem \<equiv>
  Call src DotCall (TupleElement elem)"
abbreviation "IterateCall src its v ty init body \<equiv>
  Call src ArrowCall (Iterate its v ty init body)"
abbreviation "AnyIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator AnyIter its body)"
abbreviation "ClosureIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator ClosureIter its body)"
abbreviation "CollectIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator CollectIter its body)"
abbreviation "CollectNestedIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator CollectNestedIter its body)"
abbreviation "ExistsIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator ExistsIter its body)"
abbreviation "ForAllIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator ForAllIter its body)"
abbreviation "OneIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator OneIter its body)"
abbreviation "IsUniqueIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator IsUniqueIter its body)"
abbreviation "SelectIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator SelectIter its body)"
abbreviation "RejectIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator RejectIter its body)"
abbreviation "SortedByIteratorCall src its body \<equiv>
  Call src ArrowCall (Iterator SortedByIter its body)"

end

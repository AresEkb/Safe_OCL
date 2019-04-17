(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
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
| SelectByTypeOp | SelectByKindOp

datatype any_unop = OclAsSetOp | OclIsNewOp
| OclIsUndefinedOp | OclIsInvalidOp | ToStringOp
datatype any_binop = EqualOp | NotEqualOp

datatype boolean_unop = NotOp
datatype boolean_binop = AndOp | OrOp | XorOp | ImpliesOp

datatype numeric_unop = UMinusOp | AbsOp | FloorOp | RoundOp | ToIntegerOp
datatype numeric_binop = PlusOp | MinusOp | MultOp | DivideOp
| DivOp | ModOp | NumericMaxOp | NumericMinOp
| NumericLessOp | NumericLessEqOp | NumericGreaterOp | NumericGreaterEqOp

datatype string_unop = StringSizeOp | ToUpperCaseOp | ToLowerCaseOp | CharactersOp
| ToBooleanOp | ToIntegerOp | ToRealOp
datatype string_binop = ConcatOp | StringIndexOfOp | EqualsIgnoreCaseOp | StringAtOp
| StringLessOp | StringLessEqOp | StringGreaterOp | StringGreaterEqOp
datatype string_ternop = SubstringOp

datatype iterable_unop = SizeOp | IsEmptyOp | NotEmptyOp
| MaxOp | MinOp | SumOp
| AsSetOp | AsOrderedSetOp | AsBagOp | AsSequenceOp | FlattenOp
| FirstOp | LastOp | ReverseOp
| KeysOp | ValuesOp
datatype iterable_binop = CountOp
| IncludesOp | ExcludesOp | IncludesValueOp | ExcludesValueOp
| IncludesAllOp | ExcludesAllOp | IncludesMapOp | ExcludesMapOp
| ProductOp
| UnionOp | IntersectionOp | SetMinusOp | SymmetricDifferenceOp
| IncludingOp | ExcludingOp
| IncludingAllOp | ExcludingAllOp | IncludingMapOp | ExcludingMapOp
| AppendOp | PrependOp | AppendAllOp | PrependAllOp | AtOp | IndexOfOp
datatype iterable_ternop = InsertAtOp | SubOrderedSetOp | SubSequenceOp
| IncludesPairOp | ExcludesPairOp| IncludingPairOp | ExcludingPairOp

type_synonym unop = "any_unop + boolean_unop + numeric_unop + string_unop + iterable_unop"

declare [[coercion "Inl :: any_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inl :: boolean_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl :: numeric_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_unop \<Rightarrow> unop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inr :: iterable_unop \<Rightarrow> unop"]]

type_synonym binop = "any_binop + boolean_binop + numeric_binop + string_binop + iterable_binop"

declare [[coercion "Inl :: any_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inl :: boolean_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl :: numeric_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_binop \<Rightarrow> binop"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inr \<circ> Inr :: iterable_binop \<Rightarrow> binop"]]

type_synonym ternop = "string_ternop + iterable_ternop"

declare [[coercion "Inl :: string_ternop \<Rightarrow> ternop"]]
declare [[coercion "Inr :: iterable_ternop \<Rightarrow> ternop"]]

type_synonym op = "unop + binop + ternop + oper"

declare [[coercion "Inl \<circ> Inl :: any_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inl :: boolean_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inr \<circ> Inl :: numeric_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_unop \<Rightarrow> op"]]
declare [[coercion "Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inr :: iterable_unop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inl \<circ> Inl :: any_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inl :: boolean_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inl :: numeric_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inr :: iterable_binop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inr \<circ> Inl \<circ> Inl :: string_ternop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl \<circ> Inr :: iterable_ternop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inr \<circ> Inr :: oper \<Rightarrow> op"]]

datatype iteration = AnyIter | ClosureIter
| CollectIter | CollectByIter | CollectNestedIter
| ExistsIter | ForAllIter | OneIter | IsUniqueIter
| SelectIter | RejectIter | SortedByIter

section \<open>Expressions\<close>

text \<open>
  A call kind could be defined as two boolean values (@{text "is_arrow_call"},
  @{text "is_safe_call"}). Also we could derive @{text "is_arrow_call"}
  value automatically based on an operation kind.
  However, it is much easier and more natural to use the following enumeration.\<close>

datatype call_kind = DotCall | ArrowCall | SafeDotCall | SafeArrowCall

text \<open>
  We do not define a @{text Classifier} type (a type of all types),
  because it will add unnecessary complications to the theory.
  So we have to define type operations as a pure syntactic constructs.
  We do not define @{text Type} expressions either.

  We do not define @{text InvalidLiteral}, because it allows us to
  exclude @{text OclInvalid} type from typing rules. It simplifies
  the types system.

  Please take a note that for @{text AssociationEnd} and
  @{text AssociationClass} call expressions one can specify an
  optional role of a source class (@{text from_role}).
  It differs from the OCL specification, which allows one to specify
  a role of a destination class. However, the latter one does not
  allow one to determine uniquely a set of linked objects, for example,
  in a ternary self relation.\<close>

datatype 'a expr =
  Literal "'a literal_expr"
| Let (var : vname) (var_type : "'a type\<^sub>N\<^sub>E option") (init_expr : "'a expr")
    (body_expr : "'a expr")
| Var (var : vname)
| If (if_expr : "'a expr") (then_expr : "'a expr") (else_expr : "'a expr")
| MetaOperationCall (type : "'a type\<^sub>N\<^sub>E") metaop
| StaticOperationCall (type : "'a type\<^sub>N\<^sub>E") oper (args : "'a expr list")
| Call (source : "'a expr") (kind : call_kind) "'a call_expr"
and 'a literal_expr =
  NullLiteral
| BooleanLiteral (boolean_symbol : bool)
| RealLiteral (real_symbol : real)
| IntegerLiteral (integer_symbol : int)
| UnlimitedNaturalLiteral (unlimited_natural_symbol : unat)
| StringLiteral (string_symbol : string)
| EnumLiteral (enum_type : "'a enum_type") (enum_literal : elit)
| TupleLiteral (tuple_elements : "(telem \<times> 'a type\<^sub>N\<^sub>E option \<times> 'a expr) list")
| CollectionLiteral (collection_kind : collection_kind)
    (collection_parts : "'a collection_literal_part_expr list")
| MapLiteral (map_elements : "('a expr \<times> 'a expr) list")
and 'a collection_literal_part_expr =
  CollectionItem (item : "'a expr")
| CollectionRange (range_first : "'a expr") (range_last : "'a expr")
and 'a call_expr =
  TypeOperation typeop (type : "'a type\<^sub>N\<^sub>E")
| Attribute attr
| AssociationEnd (from_role : "role option") role
| AssociationClass (from_role : "role option") 'a
| AssociationClassEnd role
| Operation op (args : "'a expr list")
| TupleElement telem
| Iterate
    (iters : "(vname \<times> vname option) list")
    (iters_type : "'a type\<^sub>N\<^sub>E option \<times> 'a type\<^sub>N\<^sub>E option")
    (var : vname) (var_type : "'a type\<^sub>N\<^sub>E option") (init_expr : "'a expr")
    (body_expr : "'a expr")
| Iterator iteration
    (iters : "(vname \<times> vname option) list")
    (iters_type : "'a type\<^sub>N\<^sub>E option \<times> 'a type\<^sub>N\<^sub>E option")
    (body_expr : "'a expr")

definition "map_literal_element_key \<equiv> fst"
definition "map_literal_element_value \<equiv> snd"

definition "tuple_literal_element_name \<equiv> fst"
definition "tuple_literal_element_type \<equiv> fst \<circ> snd"
definition "tuple_literal_element_expr \<equiv> snd \<circ> snd"

declare [[coercion "Literal :: 'a literal_expr \<Rightarrow> 'a expr"]]

abbreviation "TypeOperationCall src k op ty \<equiv>
  Call src k (TypeOperation op ty)"
abbreviation "AttributeCall src attr \<equiv>
  Call src DotCall (Attribute attr)"
abbreviation "AssociationEndCall src from role \<equiv>
  Call src DotCall (AssociationEnd from role)"
abbreviation "AssociationClassCall src from cls \<equiv>
  Call src DotCall (AssociationClass from cls)"
abbreviation "AssociationClassEndCall src role \<equiv>
  Call src DotCall (AssociationClassEnd role)"
abbreviation "OperationCall src k op as \<equiv>
  Call src k (Operation op as)"
abbreviation "TupleElementCall src elem \<equiv>
  Call src DotCall (TupleElement elem)"
abbreviation "IterateCall src its its_ty v ty init body \<equiv>
  Call src ArrowCall (Iterate its its_ty v ty init body)"
abbreviation "AnyIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator AnyIter its its_ty body)"
abbreviation "ClosureIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator ClosureIter its its_ty body)"
abbreviation "CollectIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator CollectIter its its_ty body)"
abbreviation "CollectByIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator CollectByIter its its_ty body)"
abbreviation "CollectNestedIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator CollectNestedIter its its_ty body)"
abbreviation "ExistsIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator ExistsIter its its_ty body)"
abbreviation "ForAllIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator ForAllIter its its_ty body)"
abbreviation "OneIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator OneIter its its_ty body)"
abbreviation "IsUniqueIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator IsUniqueIter its its_ty body)"
abbreviation "SelectIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator SelectIter its its_ty body)"
abbreviation "RejectIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator RejectIter its its_ty body)"
abbreviation "SortedByIterationCall src its its_ty body \<equiv>
  Call src ArrowCall (Iterator SortedByIter its its_ty body)"

section \<open>Notation\<close>

subsection \<open>Literals\<close>

abbreviation "null \<equiv> Literal NullLiteral"
abbreviation "true \<equiv> Literal (BooleanLiteral True)"
abbreviation "false \<equiv> Literal (BooleanLiteral False)"

syntax
  "_int0" :: "'a expr" ("\<^bold>0")
  "_int1" :: "'a expr" ("\<^bold>1")
  "_int2" :: "'a expr" ("\<^bold>2")
  "_int3" :: "'a expr" ("\<^bold>3")
  "_int4" :: "'a expr" ("\<^bold>4")
  "_int5" :: "'a expr" ("\<^bold>5")
  "_int6" :: "'a expr" ("\<^bold>6")
  "_int7" :: "'a expr" ("\<^bold>7")
  "_int8" :: "'a expr" ("\<^bold>8")
  "_int9" :: "'a expr" ("\<^bold>9")

translations
  "\<^bold>0" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 0)"
  "\<^bold>1" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 1)"
  "\<^bold>2" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 2)"
  "\<^bold>3" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 3)"
  "\<^bold>4" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 4)"
  "\<^bold>5" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 5)"
  "\<^bold>6" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 6)"
  "\<^bold>7" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 7)"
  "\<^bold>8" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 8)"
  "\<^bold>9" \<rightleftharpoons> "CONST Literal (CONST IntegerLiteral 9)"

syntax
  "_enum_literal" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a expr" ("_\<^bold>:\<^bold>:_")

translations
  "_enum_literal enm lit" \<rightharpoonup> "CONST EnumLiteral enm lit"

nonterminal collection_parts and collection_part

syntax
  "_set" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Set{_}")
  "_ordered_set" :: "collection_parts \<Rightarrow> 'a literal_expr" ("OrderedSet{_}")
  "_bag" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Bag{_}")
  "_sequence" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Sequence{_}")

  "_collection_parts" ::
      "collection_part \<Rightarrow> collection_parts \<Rightarrow> collection_parts" ("_, _")
  "_collection_empty_parts" :: "collection_parts" ("")
  "_collection_single_part" :: "collection_part \<Rightarrow> collection_parts" ("_")

  "_collection_item" :: "'a expr \<Rightarrow> collection_part" ("_")
  "_collection_range" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> collection_part" ("_.._")

translations
  "_set xs" \<rightleftharpoons> "CONST CollectionLiteral CONST SetKind xs"
  "_ordered_set xs" \<rightleftharpoons> "CONST CollectionLiteral CONST OrderedSetKind xs"
  "_bag xs" \<rightleftharpoons> "CONST CollectionLiteral CONST BagKind xs"
  "_sequence xs" \<rightleftharpoons> "CONST CollectionLiteral CONST SequenceKind xs"

  "_collection_parts x xs" \<rightharpoonup> "x # xs"
  "_collection_empty_parts" \<rightharpoonup> "[]"
  "_collection_single_part x" \<rightharpoonup> "[x]"

  "_collection_item x" \<rightleftharpoons> "CONST CollectionItem x"
  "_collection_range x y" \<rightleftharpoons> "CONST CollectionRange x y"

nonterminal map_parts and map_part

syntax
  "_map" :: "map_parts \<Rightarrow> 'a literal_expr" ("Map{_}")
  "_map_parts" :: "map_part \<Rightarrow> map_parts \<Rightarrow> map_parts" ("_,/ _")
  "_map_empty_parts" :: "map_parts" ("")
  "_map_single_part" :: "map_part \<Rightarrow> map_parts" ("_")
  "_map_part" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> map_part" ("_ <- _")

translations
  "_map xs" \<rightleftharpoons> "CONST MapLiteral xs"
  "_map_parts x xs" \<rightharpoonup> "x # xs"
  "_map_empty_parts" \<rightharpoonup> "[]"
  "_map_single_part x" \<rightharpoonup> "[x]"
  "_map_part x y" \<rightharpoonup> "(x, y)"

subsection \<open>Types\<close>

nonterminal tuple_type_element and tuple_type_elements

syntax
  "_tuple_type" :: "tuple_type_elements \<Rightarrow> 'a type" ("Tuple'(_')")

  "_tuple_type_elements" ::
      "tuple_type_element \<Rightarrow> tuple_type_elements \<Rightarrow> tuple_type_elements" ("_, _")
  "_tuple_type_empty_elements" :: "tuple_type_elements" ("")
  "_tuple_type_single_element" :: "tuple_type_element \<Rightarrow> tuple_type_elements" ("_")

  "_tuple_type_element" :: "vname \<Rightarrow> 'a type\<^sub>N \<Rightarrow> tuple_type_element" ("_ : _")

translations
  "_tuple_type \<pi>" \<rightleftharpoons> "CONST Tuple (CONST fmap_of_list \<pi>)"

  "_tuple_type_elements x xs" \<rightharpoonup> "x # xs"
  "_tuple_type_empty_elements" \<rightharpoonup> "[]"
  "_tuple_type_single_element x" \<rightharpoonup> "[x]"

  "_tuple_type_element elem \<tau>" \<rightharpoonup> "(elem, \<tau>)"

subsection \<open>Misc Expressions\<close>

notation Var ("\<lparr>_\<rparr>")

syntax
  "_let" :: "vname \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr"
                ("let _ = _ in _" [101,101,101] 100)
  "_typed_let" :: "vname \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr"
                ("let _ : _ = _ in _" [101,101,101,101] 100)
  "_if" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr"
                ("if _ then _ else _ endif")

translations
  "_let v init body" \<rightleftharpoons> "CONST Let v CONST None init body"
  "_typed_let v \<tau> init body" \<rightleftharpoons> "CONST Let v (CONST Some \<tau>) init body"
  "_if cnd thn els" \<rightleftharpoons> "CONST If cnd thn els"

subsection \<open>Call Expressions\<close>

nonterminal op_args

syntax
  "_op_args" :: "'a expr \<Rightarrow> op_args \<Rightarrow> op_args" ("_, _")
  "_op_empty_args" :: "op_args" ("")
  "_op_single_arg" :: "'a expr \<Rightarrow> op_args" ("_")

translations
  "_op_args x xs" \<rightharpoonup> "x # xs"
  "_op_empty_args" \<rightharpoonup> "[]"
  "_op_single_arg x" \<rightharpoonup> "[x]"

nonterminal call and nav_call and op_call and type_op_call and loop_call and op_name

syntax
  "_call" :: "nav_call \<Rightarrow> call" ("_")
  "_call" :: "op_call \<Rightarrow> call" ("_")
  "_call" :: "type_op_call \<Rightarrow> call" ("_")
  "_call" :: "loop_call \<Rightarrow> call" ("_")
  "_nav_call" :: "'a \<Rightarrow> nav_call" ("_" [1000] 300)
  "_op_call" :: "op_name \<Rightarrow> op_args \<Rightarrow> op_call" ("_('(_'))" [1000,100] 200)
  "_op_call_no_args" :: "op_name \<Rightarrow> op_call" ("_('('))" [1000] 200)

translations
  "_call call" \<rightharpoonup> "call"
  "_nav_call call" \<rightharpoonup> "call"
  "_op_call op args" \<rightharpoonup> "op args"
  "_op_call_no_args op" \<rightharpoonup> "op []"

syntax
  "_dotCall" :: "'a expr \<Rightarrow> call \<Rightarrow> 'a expr" (infixl "\<^bold>." 300)
  "_safeDotCall" :: "'a expr \<Rightarrow> call \<Rightarrow> 'a expr" (infixl "?." 300)
  "_arrowCall" :: "'a expr \<Rightarrow> call \<Rightarrow> 'a expr" (infixl "->" 300)
  "_safeArrowCall" :: "'a expr \<Rightarrow> call \<Rightarrow> 'a expr" (infixl "?->" 300)
  "_staticOpCall" :: "'a expr \<Rightarrow> 'b \<Rightarrow> op_args \<Rightarrow> 'a expr"
      ("_::_('(_'))"  [1000,1000,100] 300)
  "_staticOpCall_no_args" :: "'a expr \<Rightarrow> 'b \<Rightarrow> 'a expr"
      ("_::_('('))"  [1000,1000] 300)

translations
  "_dotCall src call" \<rightleftharpoons> "CONST Call src (CONST DotCall) call"
  "_safeDotCall src call" \<rightleftharpoons> "CONST Call src (CONST SafeDotCall) call"
  "_arrowCall src call" \<rightleftharpoons> "CONST Call src (CONST ArrowCall) call"
  "_safeArrowCall src call" \<rightleftharpoons> "CONST Call src (CONST SafeArrowCall) call"
  "_staticOpCall src op args" \<rightleftharpoons> "CONST StaticOperationCall src op args"
  "_staticOpCall_no_args src op" \<rightleftharpoons> "CONST StaticOperationCall src op []"

subsection \<open>Operations\<close>

\<comment> \<open>Meta Operations\<close>
syntax
  "_allInstances" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr" ("_\<^bold>.allInstances'(')")

translations
  "_allInstances \<tau>" \<rightleftharpoons> "CONST MetaOperationCall \<tau> (CONST AllInstancesOp)"

\<comment> \<open>Type Operations\<close>
syntax
  "_oclAsType" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> type_op_call" ("oclAsType('(_'))")
  "_oclIsTypeOf" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> type_op_call" ("oclIsTypeOf('(_'))")
  "_oclIsKindOf" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> type_op_call" ("oclIsKindOf('(_'))")
  "_selectByType" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> type_op_call" ("selectByType('(_'))")
  "_selectByKind" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> type_op_call" ("selectByKind('(_'))")

translations
  "_oclAsType \<tau>" \<rightleftharpoons> "CONST TypeOperation (CONST OclAsTypeOp) \<tau>"
  "_oclIsTypeOf \<tau>" \<rightleftharpoons> "CONST TypeOperation (CONST OclIsTypeOfOp) \<tau>"
  "_oclIsKindOf \<tau>" \<rightleftharpoons> "CONST TypeOperation (CONST OclIsKindOfOp) \<tau>"
  "_selectByType \<tau>" \<rightleftharpoons> "CONST TypeOperation (CONST SelectByTypeOp) \<tau>"
  "_selectByKind \<tau>" \<rightleftharpoons> "CONST TypeOperation (CONST SelectByKindOp) \<tau>"

syntax
  \<comment> \<open>User-defined Operations\<close>
  "_user_defined_op" :: "'a \<Rightarrow> op_name" ("_")

  \<comment> \<open>OclAny Operations\<close>
  "_oclAsSet" :: "op_name" ("oclAsSet")
  "_oclIsNew" :: "op_name" ("oclIsNew")
  "_oclIsUndefined" :: "op_name" ("oclIsUndefined")
  "_oclIsInvalid" :: "op_name" ("oclIsInvalid")
  "_toString" :: "op_name" ("toString")
  "_equal" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>=" 250)
  "_notEqual" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "<>" 250)

  \<comment> \<open>Boolean Operations\<close>
  "_not" :: "'a expr \<Rightarrow> 'a expr" ("not _" [240] 240)
  "_and" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixr "and" 235)
  "_or" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixr "or" 230)
  "_xor" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixr "xor" 230)
  "_implies" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixr "implies" 225)

  \<comment> \<open>Numeric Operations\<close>
  "_uminus" :: "'a expr \<Rightarrow> 'a expr" ("\<^bold>- _" [281] 280)
  "_absOp" :: "op_name" ("abs") (* Should not be named _abs. It could cause strange exceptions *)
  "_floor" :: "op_name" ("floor")
  "_round" :: "op_name" ("round")
  "_toInteger" :: "op_name" ("toInteger")
  "_plus" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>+" 265)
  "_minus" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>-" 265)
  "_mult" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>*" 270)
  "_divide" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>'/" 270)
  "_div" :: "op_name" ("div")
  "_mod" :: "op_name" ("mod")
  "_numericMax" :: "op_name" ("max\<^sub>N")
  "_numericMin" :: "op_name" ("min\<^sub>N")
  "_numericLess" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold><" 250)
  "_numericLessEq" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold><\<^bold>=" 250)
  "_numericGreater" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold>>" 250)
  "_numericGreaterEq" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold>>\<^bold>=" 250)

  \<comment> \<open>String Operations\<close>
  "_stringSize" :: "op_name" ("size\<^sub>S")
  "_toUpperCase" :: "op_name" ("toUpperCase")
  "_toLowerCase" :: "op_name" ("toLowerCase")
  "_characters" :: "op_name" ("characters")
  "_toBoolean" :: "op_name" ("toBoolean")
  "_toInteger" :: "op_name" ("toInteger")
  "_toReal" :: "op_name" ("toReal")
  "_concat" :: "op_name" ("concat")
  "_stringIndexOf" :: "op_name" ("indexOf\<^sub>S")
  "_equalsIgnoreCase" :: "op_name" ("equalsIgnoreCase")
  "_stringAt" :: "op_name" ("at\<^sub>S")
  "_stringLess" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold><\<^sub>S" 250)
  "_stringLessEq" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold><\<^bold>=\<^sub>S" 250)
  "_stringGreater" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold>>\<^sub>S" 250)
  "_stringGreaterEq" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold>>\<^bold>=\<^sub>S" 250)
  "_substring" :: "op_name" ("substring")

  \<comment> \<open>Iterable Operations\<close>
  "_size" :: "op_name" ("size")
  "_isEmpty" :: "op_name" ("isEmpty")
  "_notEmpty" :: "op_name" ("notEmpty")
  "_max" :: "op_name" ("max")
  "_min" :: "op_name" ("min")
  "_sum" :: "op_name" ("sum")
  "_asSet" :: "op_name" ("asSet")
  "_asOrderedSet" :: "op_name" ("asOrderedSet")
  "_asBag" :: "op_name" ("asBag")
  "_asSequence" :: "op_name" ("asSequence")
  "_flatten" :: "op_name" ("flatten")
  "_first" :: "op_name" ("first")
  "_last" :: "op_name" ("last")
  "_reverse" :: "op_name" ("reverse")
  "_keys" :: "op_name" ("keys")
  "_values" :: "op_name" ("values")
  "_count" :: "op_name" ("count")
  "_includes" :: "op_name" ("includes")
  "_excludes" :: "op_name" ("excludes")
  "_includesValue" :: "op_name" ("includesValue")
  "_excludesValue" :: "op_name" ("excludesValue")
  "_includesAll" :: "op_name" ("includesAll")
  "_excludesAll" :: "op_name" ("excludesAll")
  "_includesMap" :: "op_name" ("includesMap")
  "_excludesMap" :: "op_name" ("excludesMap")
  "_product" :: "op_name" ("product")
  "_union" :: "op_name" ("union")
  "_intersection" :: "op_name" ("intersection")
  "_setMinus" :: "op_name" ("setMinus")
  "_symmetricDifference" :: "op_name" ("symmetricDifference")
  "_including" :: "op_name" ("including")
  "_excluding" :: "op_name" ("excluding")
  "_includingAll" :: "op_name" ("includingAll")
  "_excludingAll" :: "op_name" ("excludingAll")
  "_includingMap" :: "op_name" ("includingMap")
  "_excludingMap" :: "op_name" ("excludingMap")
  "_append" :: "op_name" ("append")
  "_prepend" :: "op_name" ("prepend")
  "_appendAll" :: "op_name" ("appendAll")
  "_prependAll" :: "op_name" ("prependAll")
  "_at" :: "op_name" ("at")
  "_indexOf" :: "op_name" ("indexOf")
  "_insertAt" :: "op_name" ("insertAt")
  "_subOrderedSet" :: "op_name" ("subOrderedSet")
  "_subSequence" :: "op_name" ("subSequence")
  "_includesPair" :: "op_name" ("includes\<^sub>P")
  "_excludesPair" :: "op_name" ("excludes\<^sub>P")
  "_includingPair" :: "op_name" ("including\<^sub>P")
  "_excludingPair" :: "op_name" ("excluding\<^sub>P")

translations
  \<comment> \<open>User-defined Operations\<close>
  "_user_defined_op op" \<rightleftharpoons> "CONST Operation op"

  \<comment> \<open>OclAny Operations\<close>
  "_oclAsSet" \<rightleftharpoons> "CONST Operation (CONST OclAsSetOp)"
  "_oclIsNew" \<rightleftharpoons> "CONST Operation (CONST OclIsNewOp)"
  "_oclIsUndefined" \<rightleftharpoons> "CONST Operation (CONST OclIsUndefinedOp)"
  "_oclIsInvalid" \<rightleftharpoons> "CONST Operation (CONST OclIsInvalidOp)"
  "_toString" \<rightleftharpoons> "CONST Operation (CONST ToStringOp)"
  "_equal x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST EqualOp) [y])"
  "_notEqual x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST NotEqualOp) [y])"

  \<comment> \<open>Boolean Operations\<close>
  "_not x" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST NotOp) [])"
  "_and x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST AndOp) [y])"
  "_or x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST OrOp) [y])"
  "_xor x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST XorOp) [y])"
  "_implies x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST ImpliesOp) [y])"

  \<comment> \<open>Numeric Operations\<close>
  "_uminus x" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST UMinusOp) [])"
  "_absOp" \<rightleftharpoons> "CONST Operation (CONST AbsOp)"
  "_floor" \<rightleftharpoons> "CONST Operation (CONST FloorOp)"
  "_round" \<rightleftharpoons> "CONST Operation (CONST RoundOp)"
  "_toInteger" \<rightleftharpoons> "CONST Operation (CONST ToIntegerOp)"
  "_plus x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST PlusOp) [y])"
  "_minus x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST MinusOp) [y])"
  "_mult x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST MultOp) [y])"
  "_divide x y" \<rightleftharpoons> "CONST Call x (CONST DotCall)
      (CONST Operation (CONST DivideOp) [y])"
  "_div" \<rightleftharpoons> "CONST Operation (CONST DivOp)"
  "_mod" \<rightleftharpoons> "CONST Operation (CONST ModOp)"
  "_numericMax" \<rightleftharpoons> "CONST Operation (CONST NumericMaxOp)"
  "_numericMin" \<rightleftharpoons> "CONST Operation (CONST NumericMinOp)"
  "_numericLess" \<rightleftharpoons> "CONST Operation (CONST NumericLessOp)"
  "_numericLessEq" \<rightleftharpoons> "CONST Operation (CONST NumericLessEqOp)"
  "_numericGreater" \<rightleftharpoons> "CONST Operation (CONST NumericGreaterOp)"
  "_numericGreaterEq" \<rightleftharpoons> "CONST Operation (CONST NumericGreaterEqOp)"

  \<comment> \<open>String Operations\<close>
  "_stringSize" \<rightleftharpoons> "CONST Operation (CONST StringSizeOp)"
  "_toUpperCase" \<rightleftharpoons> "CONST Operation (CONST ToUpperCaseOp)"
  "_toLowerCase" \<rightleftharpoons> "CONST Operation (CONST ToLowerCaseOp)"
  "_characters" \<rightleftharpoons> "CONST Operation (CONST CharactersOp)"
  "_toBoolean" \<rightleftharpoons> "CONST Operation (CONST ToBooleanOp)"
  "_toInteger" \<rightleftharpoons> "CONST Operation (CONST ToIntegerOp)"
  "_toReal" \<rightleftharpoons> "CONST Operation (CONST ToRealOp)"
  "_concat" \<rightleftharpoons> "CONST Operation (CONST ConcatOp)"
  "_stringIndexOf" \<rightleftharpoons> "CONST Operation (CONST StringIndexOfOp)"
  "_equalsIgnoreCase" \<rightleftharpoons> "CONST Operation (CONST EqualsIgnoreCaseOp)"
  "_stringAt" \<rightleftharpoons> "CONST Operation (CONST StringAtOp)"
  "_stringLess" \<rightleftharpoons> "CONST Operation (CONST StringLessOp)"
  "_stringLessEq" \<rightleftharpoons> "CONST Operation (CONST StringLessEqOp)"
  "_stringGreater" \<rightleftharpoons> "CONST Operation (CONST StringGreaterOp)"
  "_stringGreaterEq" \<rightleftharpoons> "CONST Operation (CONST StringGreaterEqOp)"
  "_substring" \<rightleftharpoons> "CONST Operation (CONST SubstringOp)"

  \<comment> \<open>Iterable Operations\<close>
  "_size" \<rightleftharpoons> "CONST Operation (CONST SizeOp)"
  "_isEmpty" \<rightleftharpoons> "CONST Operation (CONST IsEmptyOp)"
  "_notEmpty" \<rightleftharpoons> "CONST Operation (CONST NotEmptyOp)"
  "_max" \<rightleftharpoons> "CONST Operation (CONST MaxOp)"
  "_min" \<rightleftharpoons> "CONST Operation (CONST MinOp)"
  "_sum" \<rightleftharpoons> "CONST Operation (CONST SumOp)"
  "_asSet" \<rightleftharpoons> "CONST Operation (CONST AsSetOp)"
  "_asOrderedSet" \<rightleftharpoons> "CONST Operation (CONST AsOrderedSetOp)"
  "_asBag" \<rightleftharpoons> "CONST Operation (CONST AsBagOp)"
  "_asSequence" \<rightleftharpoons> "CONST Operation (CONST AsSequenceOp)"
  "_flatten" \<rightleftharpoons> "CONST Operation (CONST FlattenOp)"
  "_first" \<rightleftharpoons> "CONST Operation (CONST FirstOp)"
  "_last" \<rightleftharpoons> "CONST Operation (CONST LastOp)"
  "_reverse" \<rightleftharpoons> "CONST Operation (CONST ReverseOp)"
  "_keys" \<rightleftharpoons> "CONST Operation (CONST KeysOp)"
  "_values" \<rightleftharpoons> "CONST Operation (CONST ValuesOp)"
  "_count" \<rightleftharpoons> "CONST Operation (CONST CountOp)"
  "_includes" \<rightleftharpoons> "CONST Operation (CONST IncludesOp)"
  "_excludes" \<rightleftharpoons> "CONST Operation (CONST ExcludesOp)"
  "_includesValue" \<rightleftharpoons> "CONST Operation (CONST IncludesValueOp)"
  "_excludesValue" \<rightleftharpoons> "CONST Operation (CONST ExcludesValueOp)"
  "_includesAll" \<rightleftharpoons> "CONST Operation (CONST IncludesAllOp)"
  "_excludesAll" \<rightleftharpoons> "CONST Operation (CONST ExcludesAllOp)"
  "_includesMap" \<rightleftharpoons> "CONST Operation (CONST IncludesMapOp)"
  "_excludesMap" \<rightleftharpoons> "CONST Operation (CONST ExcludesMapOp)"
  "_product" \<rightleftharpoons> "CONST Operation (CONST ProductOp)"
  "_union" \<rightleftharpoons> "CONST Operation (CONST UnionOp)"
  "_intersection" \<rightleftharpoons> "CONST Operation (CONST IntersectionOp)"
  "_setMinus" \<rightleftharpoons> "CONST Operation (CONST SetMinusOp)"
  "_symmetricDifference" \<rightleftharpoons>
      "CONST Operation (CONST SymmetricDifferenceOp)"
  "_including" \<rightleftharpoons> "CONST Operation (CONST IncludingOp)"
  "_excluding" \<rightleftharpoons> "CONST Operation (CONST ExcludingOp)"
  "_includingAll" \<rightleftharpoons> "CONST Operation (CONST IncludingAllOp)"
  "_excludingAll" \<rightleftharpoons> "CONST Operation (CONST ExcludingAllOp)"
  "_includingMap" \<rightleftharpoons> "CONST Operation (CONST IncludingMapOp)"
  "_excludingMap" \<rightleftharpoons> "CONST Operation (CONST ExcludingMapOp)"
  "_append" \<rightleftharpoons> "CONST Operation (CONST AppendOp)"
  "_prepend" \<rightleftharpoons> "CONST Operation (CONST PrependOp)"
  "_appendAll" \<rightleftharpoons> "CONST Operation (CONST AppendAllOp)"
  "_prependAll" \<rightleftharpoons> "CONST Operation (CONST PrependAllOp)"
  "_at" \<rightleftharpoons> "CONST Operation (CONST AtOp)"
  "_indexOf" \<rightleftharpoons> "CONST Operation (CONST IndexOfOp)"
  "_insertAt" \<rightleftharpoons> "CONST Operation (CONST InsertAtOp)"
  "_subOrderedSet" \<rightleftharpoons> "CONST Operation (CONST SubOrderedSetOp)"
  "_subSequence" \<rightleftharpoons> "CONST Operation (CONST SubSequenceOp)"
  "_includesPair" \<rightleftharpoons> "CONST Operation (CONST IncludesPairOp)"
  "_excludesPair" \<rightleftharpoons> "CONST Operation (CONST ExcludesPairOp)"
  "_includingPair" \<rightleftharpoons> "CONST Operation (CONST IncludingPairOp)"
  "_excludingPair" \<rightleftharpoons> "CONST Operation (CONST ExcludingPairOp)"

subsection \<open>Iterators\<close>

(* TODO: Нужно использовать эти типы выше в AST *)

datatype ('a, 'b) iterators = Iterators
  (iterator_names: "'a list")
  (iterator_type: "'b option")

datatype ('a, 'b) coiterators = CoIterators
  "('a, 'b) iterators"
  "('a, 'b) iterators option"

primrec coiterator_names where
  "coiterator_names (CoIterators xs ys) = (case ys
      of None \<Rightarrow> map (\<lambda>it. (it, None)) (iterator_names xs)
       | Some zs \<Rightarrow> zip (iterator_names xs) (map Some (iterator_names zs)))"

primrec coiterator_types where
  "coiterator_types (CoIterators xs ys) = (case ys
      of None \<Rightarrow> (iterator_type xs, None)
       | Some zs \<Rightarrow> (iterator_type xs, iterator_type zs))"

datatype ('a, 'b, 'c) lambda_spec =
  NoIteratorsLambda
    (lambda_body: 'c)
| IterateLambda
    (lambda_coiterators: "('a, 'b) coiterators")
    (lambda_acc: 'a) (lambda_acc_type: "'b option") (lambda_acc_init: 'c)
    (lambda_body: 'c)
| IterationLambda
    (lambda_coiterators: "('a, 'b) coiterators")
    (lambda_body: 'c)

definition "mk_iterate lambda \<equiv> Iterate
  (coiterator_names (lambda_coiterators lambda))
  (coiterator_types (lambda_coiterators lambda))
  (lambda_acc lambda) (lambda_acc_type lambda) (lambda_acc_init lambda)
  (lambda_body lambda)"

definition "mk_iterator iter lambda \<equiv> Iterator iter
  (coiterator_names (lambda_coiterators lambda))
  (coiterator_types (lambda_coiterators lambda))
  (lambda_body lambda)"

nonterminal iterator_list and typed_iterators and lambda_iterators
nonterminal iteration_lambda and iterate_lambda

syntax
  "_iterate" :: "iterate_lambda \<Rightarrow> loop_call" ("iterate('(_'))")

  "_anyIter" :: "iteration_lambda \<Rightarrow> loop_call" ("any('(_'))")
  "_closureIter" :: "iteration_lambda \<Rightarrow> loop_call" ("closure('(_'))")
  "_collectIter" :: "iteration_lambda \<Rightarrow> loop_call" ("collect('(_'))")
  "_collectByIter" :: "iteration_lambda \<Rightarrow> loop_call" ("collectBy('(_'))")
  "_collectNestedIter" :: "iteration_lambda \<Rightarrow> loop_call" ("collectNested('(_'))")
  "_existsIter" :: "iteration_lambda \<Rightarrow> loop_call" ("exists('(_'))")
  "_forAllIter" :: "iteration_lambda \<Rightarrow> loop_call" ("forAll('(_'))")
  "_oneIter" :: "iteration_lambda \<Rightarrow> loop_call" ("one('(_'))")
  "_isUniqueIter" :: "iteration_lambda \<Rightarrow> loop_call" ("isUnique('(_'))")
  "_selectIter" :: "iteration_lambda \<Rightarrow> loop_call" ("select('(_'))")
  "_rejectIter" :: "iteration_lambda \<Rightarrow> loop_call" ("reject('(_'))")
  "_sortedByIter" :: "iteration_lambda \<Rightarrow> loop_call" ("'sortedBy('(_'))")

  "_iterate_lambda1" ::
      "vname \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda"
      ("_ = _ | _" [1000,1000,100] 100)
  "_iterate_lambda2" ::
      "vname \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda"
      ("_ : _ = _ | _" [1000,1000,100,100] 100)
  "_iterate_lambda3" ::
      "lambda_iterators \<Rightarrow> vname \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda"
      ("_; _ = _ | _" [100,1000,100,100] 100)
  "_iterate_lambda4" ::
      "lambda_iterators \<Rightarrow> vname \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow>
            iterate_lambda"
      ("_; _ : _ = _ | _" [100,1000,1000,100,100] 100)

  "_iteration_lambda1" ::
      "'a expr \<Rightarrow> iteration_lambda" ("_" [200] 200)
  "_iteration_lambda2" ::
      "lambda_iterators \<Rightarrow> 'a expr \<Rightarrow> iteration_lambda" ("_ | _" [200, 200] 200)

  "_col_iterators" :: "typed_iterators \<Rightarrow> lambda_iterators" ("_")
  "_map_iterators" :: "typed_iterators \<Rightarrow> typed_iterators \<Rightarrow> lambda_iterators"
      ("_ <- _")

  "_imp_typed_iterators" :: "iterator_list \<Rightarrow> typed_iterators" ("_")
  "_exp_typed_iterators" :: "iterator_list \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> typed_iterators" ("_ : _")

  "_iterators" :: "vname \<Rightarrow> iterator_list \<Rightarrow> iterator_list" ("_, _")
  "_iterator" :: "vname \<Rightarrow> iterator_list" ("_" [1000] 100)

translations
  "_iterate lambda" \<rightleftharpoons> "CONST mk_iterate lambda"

  "_anyIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST AnyIter) lambda"
  "_closureIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST ClosureIter) lambda"
  "_collectIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST CollectIter) lambda"
  "_collectByIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST CollectByIter) lambda"
  "_collectNestedIter lambda" \<rightleftharpoons>
      "CONST mk_iterator (CONST CollectNestedIter) lambda"
  "_existsIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST ExistsIter) lambda"
  "_forAllIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST ForAllIter) lambda"
  "_oneIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST OneIter) lambda"
  "_isUniqueIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST IsUniqueIter) lambda"
  "_selectIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST SelectIter) lambda"
  "_rejectIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST RejectIter) lambda"
  "_sortedByIter lambda" \<rightleftharpoons> "CONST mk_iterator (CONST SortedByIter) lambda"

  "_iterate_lambda1 acc init body" \<rightleftharpoons>
      "CONST IterateLambda
          (CONST CoIterators (CONST Iterators [] CONST None) CONST None)
          acc CONST None init body"
  "_iterate_lambda2 acc ty init body" \<rightleftharpoons>
      "CONST IterateLambda
          (CONST CoIterators (CONST Iterators [] CONST None) CONST None)
          acc (CONST Some ty) init body"
  "_iterate_lambda3 iters acc init body" \<rightleftharpoons>
      "CONST IterateLambda iters acc CONST None init body"
  "_iterate_lambda4 iters acc ty init body" \<rightleftharpoons>
      "CONST IterateLambda iters acc (CONST Some ty) init body"

  "_iteration_lambda1 body" \<rightleftharpoons> "CONST NoIteratorsLambda body"
  "_iteration_lambda2 k body" \<rightleftharpoons> "CONST IterationLambda k body"

  "_col_iterators xs" \<rightleftharpoons> "CONST CoIterators xs CONST None"
  "_map_iterators xs ys" \<rightleftharpoons> "CONST CoIterators xs (CONST Some ys)"

  "_imp_typed_iterators xs" \<rightleftharpoons> "CONST Iterators xs CONST None"
  "_exp_typed_iterators xs t" \<rightleftharpoons> "CONST Iterators xs (CONST Some t)"

  "_iterators x (y # xs)" \<rightharpoonup> "x # y # xs"
  "_iterator x" \<rightharpoonup> "[x]"

lemmas ocl_syntax_simps =
  mk_iterate_def
  mk_iterator_def

end

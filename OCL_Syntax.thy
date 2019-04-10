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

type_synonym binop = "any_binop + boolean_binop + numeric_binop + string_binop + collection_binop"

declare [[coercion "Inl :: any_binop \<Rightarrow> binop"]]
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

declare [[coercion "Inr \<circ> Inl \<circ> Inl :: any_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inl :: boolean_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inl :: numeric_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inl :: string_binop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inl \<circ> Inr \<circ> Inr \<circ> Inr \<circ> Inr :: collection_binop \<Rightarrow> op"]]

declare [[coercion "Inr \<circ> Inr \<circ> Inl \<circ> Inl :: string_ternop \<Rightarrow> op"]]
declare [[coercion "Inr \<circ> Inr \<circ> Inl \<circ> Inr :: collection_ternop \<Rightarrow> op"]]

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
| EnumLiteral (enum_type : "'a enum") (enum_literal : elit)
| CollectionLiteral (collection_kind : collection_kind)
    (collection_parts : "'a collection_literal_part_expr list")
| MapLiteral (map_elements : "('a expr \<times> 'a expr) list")
| TupleLiteral (tuple_elements : "(telem \<times> 'a type\<^sub>N\<^sub>E option \<times> 'a expr) list")
and 'a collection_literal_part_expr =
  CollectionItem (item : "'a expr")
| CollectionRange (first : "'a expr") (last : "'a expr")
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
abbreviation "AttributeCall src k attr \<equiv>
  Call src k (Attribute attr)"
abbreviation "AssociationEndCall src k from role \<equiv>
  Call src k (AssociationEnd from role)"
abbreviation "AssociationClassCall src k from cls \<equiv>
  Call src k (AssociationClass from cls)"
abbreviation "AssociationClassEndCall src k role \<equiv>
  Call src k (AssociationClassEnd role)"
abbreviation "OperationCall src k op as \<equiv>
  Call src k (Operation op as)"
abbreviation "TupleElementCall src k elem \<equiv>
  Call src k (TupleElement elem)"
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

syntax
  "_null" :: "'a expr" ("\<^bold>n\<^bold>u\<^bold>l\<^bold>l")
  "_true" :: "'a expr" ("\<^bold>t\<^bold>r\<^bold>u\<^bold>e")
  "_false" :: "'a expr" ("\<^bold>f\<^bold>a\<^bold>l\<^bold>s\<^bold>e")
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
  "\<^bold>n\<^bold>u\<^bold>l\<^bold>l" == "CONST Literal CONST NullLiteral"
  "\<^bold>t\<^bold>r\<^bold>u\<^bold>e" == "CONST Literal (CONST BooleanLiteral CONST True)"
  "\<^bold>f\<^bold>a\<^bold>l\<^bold>s\<^bold>e" == "CONST Literal (CONST BooleanLiteral CONST False)"
  "\<^bold>0" == "CONST Literal (CONST IntegerLiteral 0)"
  "\<^bold>1" == "CONST Literal (CONST IntegerLiteral 1)"
  "\<^bold>2" == "CONST Literal (CONST IntegerLiteral 2)"
  "\<^bold>3" == "CONST Literal (CONST IntegerLiteral 3)"
  "\<^bold>4" == "CONST Literal (CONST IntegerLiteral 4)"
  "\<^bold>5" == "CONST Literal (CONST IntegerLiteral 5)"
  "\<^bold>6" == "CONST Literal (CONST IntegerLiteral 6)"
  "\<^bold>7" == "CONST Literal (CONST IntegerLiteral 7)"
  "\<^bold>8" == "CONST Literal (CONST IntegerLiteral 8)"
  "\<^bold>9" == "CONST Literal (CONST IntegerLiteral 9)"

nonterminal collection_part and collection_parts

syntax
  "_collection_item" :: "'a expr \<Rightarrow> collection_part" ("_")
  "_collection_range" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> collection_part" ("_ \<^bold>.\<^bold>. _")

  "_collection_part" :: "collection_part \<Rightarrow> collection_parts" ("_")
  "_collection_parts" ::
      "collection_part \<Rightarrow> collection_parts \<Rightarrow> collection_parts" ("_\<^bold>, _")

  "_set" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Set{}")
  "_set" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Set{_}")
  "_ordered_set" :: "collection_parts \<Rightarrow> 'a literal_expr" ("OrderedSet{}")
  "_ordered_set" :: "collection_parts \<Rightarrow> 'a literal_expr" ("OrderedSet{_}")
  "_bag" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Bag{}")
  "_bag" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Bag{_}")
  "_sequence" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Sequence{}")
  "_sequence" :: "collection_parts \<Rightarrow> 'a literal_expr" ("Sequence{_}")

translations
  "_collection_item x" == "CONST CollectionItem x"
  "_collection_range x y" == "CONST CollectionRange x y"

  "_collection_part x" == "[x]"
  "_collection_parts x (y # xs)" == "x # y # xs"

  "_set" == "CONST CollectionLiteral CONST SetKind []"
  "_set xs" == "CONST CollectionLiteral CONST SetKind xs"
  "_ordered_set" == "CONST CollectionLiteral CONST OrderedSetKind []"
  "_ordered_set xs" == "CONST CollectionLiteral CONST OrderedSetKind xs"
  "_bag" == "CONST CollectionLiteral CONST BagKind []"
  "_bag xs" == "CONST CollectionLiteral CONST BagKind xs"
  "_sequence" == "CONST CollectionLiteral CONST SequenceKind []"
  "_sequence xs" == "CONST CollectionLiteral CONST SequenceKind xs"

subsection \<open>Types\<close>

nonterminal tuple_type_element and tuple_type_elements

syntax
  "_tuple_type_element" :: "vname \<Rightarrow> 'a type\<^sub>N \<Rightarrow> tuple_type_element" ("_ \<^bold>: _")

  "_tuple_type_element" :: "tuple_type_element \<Rightarrow> tuple_type_elements" ("_")
  "_tuple_type_elements" ::
      "tuple_type_element \<Rightarrow> tuple_type_elements \<Rightarrow> tuple_type_elements" ("_\<^bold>, _")

  "_tuple_type" :: "'a type" ("Tuple'(')")
  "_tuple_type" :: "tuple_type_elements \<Rightarrow> 'a type" ("Tuple'(_')")

translations
  "_tuple_type_element elem \<tau>" == "(elem, \<tau>)"

  "_tuple_type_element x" == "[x]"
  "_tuple_type_elements x (y # xs)" == "x # y # xs"

  "_tuple_type" == "CONST Tuple CONST fmempty"
  "_tuple_type \<pi>" == "CONST Tuple (CONST fmap_of_list \<pi>)"

subsection \<open>Misc Expressions\<close>

notation Var ("\<lparr>_\<rparr>")

syntax
  "_let" :: "vname \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr"
                ("\<^bold>l\<^bold>e\<^bold>t _ \<^bold>= _ \<^bold>i\<^bold>n _" [101,101,101] 100)
  "_typed_let" :: "vname \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr"
                ("\<^bold>l\<^bold>e\<^bold>t _ \<^bold>: _ \<^bold>= _ \<^bold>i\<^bold>n _" [101,101,101,101] 100)
  "_if" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr"
                ("\<^bold>i\<^bold>f _ \<^bold>t\<^bold>h\<^bold>e\<^bold>n _ \<^bold>e\<^bold>l\<^bold>s\<^bold>e _ \<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>f")

translations
  "\<^bold>l\<^bold>e\<^bold>t v \<^bold>= init \<^bold>i\<^bold>n body" == "CONST Let v CONST None init body"
  "\<^bold>l\<^bold>e\<^bold>t v \<^bold>: \<tau> \<^bold>= init \<^bold>i\<^bold>n body" == "CONST Let v (CONST Some \<tau>) init body"
  "\<^bold>i\<^bold>f cnd \<^bold>t\<^bold>h\<^bold>e\<^bold>n thn \<^bold>e\<^bold>l\<^bold>s\<^bold>e els \<^bold>e\<^bold>n\<^bold>d\<^bold>i\<^bold>f" == "CONST If cnd thn els"

subsection \<open>Call Expressions\<close>

nonterminal op_args

syntax
  "_op_empty_args" :: "op_args" ("")
  "_op_single_arg" :: "'a expr \<Rightarrow> op_args" ("_")
  "_op_args" :: "'a expr \<Rightarrow> op_args \<Rightarrow> op_args" ("_\<^bold>, _")

  "_staticOpCall" :: "'a expr \<Rightarrow> oper \<Rightarrow> op_args \<Rightarrow> 'a expr" ("_\<^bold>:\<^bold>:_'(_')" [501,501,501] 500)
  "_dotCall" :: "'a expr \<Rightarrow> 'a call_expr \<Rightarrow> 'a expr" (infixl "\<^bold>." 500)
  "_safeDotCall" :: "'a expr \<Rightarrow> 'a call_expr \<Rightarrow> 'a expr" (infixl "\<^bold>?\<^bold>." 500)
  "_arrowCall" :: "'a expr \<Rightarrow> 'a call_expr \<Rightarrow> 'a expr" (infixl "\<^bold>-\<^bold>>" 500)
  "_safeArrowCall" :: "'a expr \<Rightarrow> 'a call_expr \<Rightarrow> 'a expr" (infixl "\<^bold>?\<^bold>-\<^bold>>" 500)

translations
  "_op_empty_args" == "[]"
  "_op_single_arg x" == "[x]"
  "_op_args x (y # xs)" == "x # y # xs"

  "_staticOpCall src op args" == "CONST StaticOperationCall src op args"
  "src\<^bold>.call" == "CONST Call src (CONST DotCall) call"
  "src\<^bold>?\<^bold>.call" == "CONST Call src (CONST SafeDotCall) call"
  "src\<^bold>-\<^bold>>call" == "CONST Call src (CONST ArrowCall) call"
  "src\<^bold>?\<^bold>-\<^bold>>call" == "CONST Call src (CONST SafeArrowCall) call"

subsection \<open>Operations\<close>

\<comment> \<open>Meta Operations\<close>
syntax
  "_allInstances" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a call_expr" ("_\<^bold>. allInstances'(')")

translations
  "\<tau>\<^bold>.allInstances()" == "CONST MetaOperationCall \<tau> (CONST AllInstancesOp)"

\<comment> \<open>Type Operations\<close>
syntax
  "_oclAsType" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a call_expr" ("oclAsType'(_')")
  "_oclIsTypeOf" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a call_expr" ("oclIsTypeOf'(_')")
  "_oclIsKindOf" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a call_expr" ("oclIsKindOf'(_')")
  "_selectByType" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a call_expr" ("selectByType'(_')")
  "_selectByKind" :: "'a type\<^sub>N\<^sub>E \<Rightarrow> 'a call_expr" ("selectByKind'(_')")

translations
  "oclAsType(\<tau>)" == "CONST TypeOperation (CONST OclAsTypeOp) \<tau>"
  "oclIsTypeOf(\<tau>)" == "CONST TypeOperation (CONST OclIsTypeOfOp) \<tau>"
  "oclIsKindOf(\<tau>)" == "CONST TypeOperation (CONST OclIsKindOfOp) \<tau>"
  "selectByType(\<tau>)" == "CONST TypeOperation (CONST SelectByTypeOp) \<tau>"
  "selectByKind(\<tau>)" == "CONST TypeOperation (CONST SelectByKindOp) \<tau>"

syntax
  \<comment> \<open>OclAny Operations\<close>
  "_oclAsSet" :: "'a call_expr" ("oclAsSet'(')")
  "_oclIsNew" :: "'a call_expr" ("oclIsNew'(')")
  "_oclIsUndefined" :: "'a call_expr" ("oclIsUndefined'(')")
  "_oclIsInvalid" :: "'a call_expr" ("oclIsInvalid'(')")
  "_toString" :: "'a call_expr" ("toString'(')")

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
  "_absOp" :: "'a call_expr" ("abs'(')") (* Should not be named _abs. It could cause strange exceptions *)
  "_floor" :: "'a call_expr" ("floor'(')")
  "_round" :: "'a call_expr" ("round'(')")
  "_toInteger" :: "'a call_expr" ("toInteger'(')")

  "_plus" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>+" 265)
  "_minus" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>-" 265)
  "_mult" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>*" 270)
  "_divide" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infixl "\<^bold>/" 270)
  "_div" :: "'a expr \<Rightarrow> 'a call_expr" ("div'(_')")
  "_mod" :: "'a expr \<Rightarrow> 'a call_expr" ("mod'(_')")
  "_max" :: "'a expr \<Rightarrow> 'a call_expr" ("max\<^sub>N'(_')")
  "_min" :: "'a expr \<Rightarrow> 'a call_expr" ("min\<^sub>N'(_')")
  "_less" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold><" 250)
  "_lessEq" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold><=" 250)
  "_greater" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold>>" 250)
  "_greaterEq" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr" (infix "\<^bold>>=" 250)

  \<comment> \<open>String Operations\<close>
  "_size" :: "'a call_expr" ("size\<^sub>S'(')")
  "_toUpperCase" :: "'a call_expr" ("toUpperCase'(')")
  "_toLowerCase" :: "'a call_expr" ("toLowerCase'(')")
  "_characters" :: "'a call_expr" ("characters'(')")
  "_toBoolean" :: "'a call_expr" ("toBoolean'(')")
  "_toInteger" :: "'a call_expr" ("toInteger'(')")
  "_toReal" :: "'a call_expr" ("toReal'(')")

  "_concat" :: "'a expr \<Rightarrow> 'a call_expr" ("concat'(_')")
  "_indexOf" :: "'a expr \<Rightarrow> 'a call_expr" ("indexOf\<^sub>S'(_')")
  "_equalsIgnoreCase" :: "'a expr \<Rightarrow> 'a call_expr" ("equalsIgnoreCase'(_')")
  "_at" :: "'a expr \<Rightarrow> 'a call_expr" ("at\<^sub>S'(_')")

  "_substring" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a call_expr" ("substring'(_, _')")

  \<comment> \<open>Collection Operations\<close>
  "_collectionSize" :: "'a call_expr" ("size'(')")
  "_isEmpty" :: "'a call_expr" ("isEmpty'(')")
  "_notEmpty" :: "'a call_expr" ("notEmpty'(')")
  "_collectionMax" :: "'a call_expr" ("max'(')")
  "_collectionMin" :: "'a call_expr" ("min'(')")
  "_sum" :: "'a call_expr" ("sum'(')")
  "_asSet" :: "'a call_expr" ("asSet'(')")
  "_asOrderdSet" :: "'a call_expr" ("asOrderedSet'(')")
  "_asBag" :: "'a call_expr" ("asBag'(')")
  "_asSequence" :: "'a call_expr" ("asSequence'(')")
  "_flatten" :: "'a call_expr" ("flatten'(')")
  "_first" :: "'a call_expr" ("first'(')")
  "_last" :: "'a call_expr" ("last'(')")
  "_reverse" :: "'a call_expr" ("reverse'(')")

  "_includes" :: "'a expr \<Rightarrow> 'a call_expr" ("includes'(_')")
  "_excludes" :: "'a expr \<Rightarrow> 'a call_expr" ("excludes'(_')")
  "_count" :: "'a expr \<Rightarrow> 'a call_expr" ("count'(_')")
  "_includesAll" :: "'a expr \<Rightarrow> 'a call_expr" ("includesAll'(_')")
  "_excludesAll" :: "'a expr \<Rightarrow> 'a call_expr" ("excludesAll'(_')")
  "_product" :: "'a expr \<Rightarrow> 'a call_expr" ("product'(_')")
  "_union" :: "'a expr \<Rightarrow> 'a call_expr" ("union'(_')")
  "_intersection" :: "'a expr \<Rightarrow> 'a call_expr" ("intersection'(_')")
  "_setMinus" :: "'a expr \<Rightarrow> 'a call_expr" ("setMinus'(_')")
  "_symmetricDifference" :: "'a expr \<Rightarrow> 'a call_expr" ("symmetricDifference'(_')")
  "_including" :: "'a expr \<Rightarrow> 'a call_expr" ("including'(_')")
  "_excluding" :: "'a expr \<Rightarrow> 'a call_expr" ("excluding'(_')")
  "_append" :: "'a expr \<Rightarrow> 'a call_expr" ("append'(_')")
  "_prepend" :: "'a expr \<Rightarrow> 'a call_expr" ("prepend'(_')")
  "_collectionAt" :: "'a expr \<Rightarrow> 'a call_expr" ("at'(_')")
  "_collectionIndexOf" :: "'a expr \<Rightarrow> 'a call_expr" ("indexOf'(_')")

  "_insertAt" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a call_expr" ("insertAt'(_, _')")
  "_subOrderedSet" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a call_expr" ("subOrderedSet'(_, _')")
  "_subSequence" :: "'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a call_expr" ("subSequence'(_, _')")

translations
  \<comment> \<open>OclAny Operations\<close>
  "oclAsSet()" == "CONST Operation (CONST OclAsSetOp) []"
  "oclIsNew()" == "CONST Operation (CONST OclIsNewOp) []"
  "oclIsUndefined()" == "CONST Operation (CONST OclIsUndefinedOp) []"
  "oclIsInvalid()" == "CONST Operation (CONST OclIsInvalidOp) []"
  "toString()" == "CONST Operation (CONST ToStringOp) []"

  "x \<^bold>= y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST EqualOp) [y])"
  "x <> y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST NotEqualOp) [y])"

  \<comment> \<open>Boolean Operations\<close>
  "not x" == "CONST Call x (CONST DotCall) (CONST Operation (CONST NotOp) [])"

  "x and y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST AndOp) [y])"
  "x or y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST OrOp) [y])"
  "x xor y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST XorOp) [y])"
  "x implies y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST ImpliesOp) [y])"

  \<comment> \<open>Numeric Operations\<close>
  "\<^bold>- x" == "CONST Call x (CONST DotCall) (CONST Operation (CONST UMinusOp) [])"
  "abs()" == "CONST Operation (CONST AbsOp) []"
  "floor()" == "CONST Operation (CONST FloorOp) []"
  "round()" == "CONST Operation (CONST RoundOp) []"
  "toInteger()" == "CONST Operation (CONST ToIntegerOp) []"

  "x \<^bold>+ y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST PlusOp) [y])"
  "x \<^bold>- y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST MinusOp) [y])"
  "x \<^bold>* y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST MultOp) [y])"
  "x / y" == "CONST Call x (CONST DotCall) (CONST Operation (CONST DivideOp) [y])"

  \<comment> \<open>String Operations\<close>
  "size\<^sub>S()" == "CONST Operation (CONST SizeOp) []"
  "toUpperCase()" == "CONST Operation (CONST ToUpperCaseOp) []"
  "toLowerCase()" == "CONST Operation (CONST ToLowerCaseOp) []"
  "characters()" == "CONST Operation (CONST CharactersOp) []"
  "toBoolean()" == "CONST Operation (CONST ToBooleanOp) []"
  "toInteger()" == "CONST Operation (CONST ToIntegerOp) []"
  "toReal()" == "CONST Operation (CONST ToRealOp) []"

  "concat(x)" == "CONST Operation (CONST ConcatOp) [x]"
  "indexOf\<^sub>S(x)" == "CONST Operation (CONST IndexOfOp) [x]"
  "equalsIgnoreCase(x)" == "CONST Operation (CONST EqualsIgnoreCaseOp) [x]"
  "at\<^sub>S(x)" == "CONST Operation (CONST AtOp) [x]"

  "substring(x, y)" == "CONST Operation (CONST SubstringOp) [x, y]"

  \<comment> \<open>Collection Operations\<close>
  "size()" == "CONST Operation (CONST CollectionSizeOp) []"
  "isEmpty()" == "CONST Operation (CONST IsEmptyOp) []"
  "notEmpty()" == "CONST Operation (CONST NotEmptyOp) []"
  "max()" == "CONST Operation (CONST CollectionMaxOp) []"
  "min()" == "CONST Operation (CONST CollectionMinOp) []"
  "sum()" == "CONST Operation (CONST SumOp) []"
  "asSet()" == "CONST Operation (CONST AsSetOp) []"
  "asOrderedSet()" == "CONST Operation (CONST AsOrderedSetOp) []"
  "asBag()" == "CONST Operation (CONST AsBagOp) []"
  "asSequence()" == "CONST Operation (CONST AsSequenceOp) []"
  "flatten()" == "CONST Operation (CONST FlattenOp) []"
  "first()" == "CONST Operation (CONST FirstOp) []"
  "last()" == "CONST Operation (CONST LastOp) []"
  "reverse()" == "CONST Operation (CONST ReverseOp) []"

  "includes(x)" == "CONST Operation (CONST IncludesOp) [x]"
  "excludes(x)" == "CONST Operation (CONST ExcludesOp) [x]"
  "count(x)" == "CONST Operation (CONST CountOp) [x]"
  "includesAll(x)" == "CONST Operation (CONST IncludesAllOp) [x]"
  "excludesAll(x)" == "CONST Operation (CONST ExcludesAllOp) [x]"
  "product(x)" == "CONST Operation (CONST ProductOp) [x]"
  "union(x)" == "CONST Operation (CONST UnionOp) [x]"
  "intersection(x)" == "CONST Operation (CONST IntersectionOp) [x]"
  "setMinus(x)" == "CONST Operation (CONST SetMinusOp) [x]"
  "symmetricDifference(x)" == "CONST Operation (CONST SymmetricDifferenceOp) [x]"
  "including(x)" == "CONST Operation (CONST IncludingOp) [x]"
  "excluding(x)" == "CONST Operation (CONST ExcludingOp) [x]"
  "append(x)" == "CONST Operation (CONST AppendOp) [x]"
  "prepend(x)" == "CONST Operation (CONST PrependOp) [x]"
  "at(x)" == "CONST Operation (CONST CollectionAtOp) [x]"
  "indexOf(x)" == "CONST Operation (CONST CollectionIndexOfOp) [x]"

  "insertAt(x, y)" == "CONST Operation (CONST InsertAtOp) [x, y]"
  "subOrderedSet(x, y)" == "CONST Operation (CONST SubOrderedSetOp) [x, y]"
  "subSequence(x, y)" == "CONST Operation (CONST SubSequenceOp) [x, y]"

subsection \<open>Iterators\<close>

datatype ('a, 'b) iterators = Iterators
  (iterator_names: "'a list")
  (iterator_types: "'b option")

datatype ('a, 'b) coiterators = CoIterators
  "('a, 'b) iterators"
  "('a, 'b) iterators option"

primrec coiterator_names where
  "coiterator_names (CoIterators xs ys) = (case ys
      of None \<Rightarrow> map (\<lambda>it. (it, None)) (iterator_names xs)
       | Some zs \<Rightarrow> zip (iterator_names xs) (map Some (iterator_names zs)))"

primrec coiterator_types where
  "coiterator_types (CoIterators xs ys) = (case ys
      of None \<Rightarrow> (iterator_types xs, None)
       | Some zs \<Rightarrow> (iterator_types xs, iterator_types zs))"

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
  "_iterator" :: "vname \<Rightarrow> iterator_list" ("_")
  "_iterators" :: "vname \<Rightarrow> iterator_list \<Rightarrow> iterator_list" ("_\<^bold>, _")
  "_imp_typed_iterators" :: "iterator_list \<Rightarrow> typed_iterators" ("_")
  "_exp_typed_iterators" :: "iterator_list \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> typed_iterators" ("_ \<^bold>: _")
  "_col_iterators" :: "typed_iterators \<Rightarrow> lambda_iterators" ("_")
  "_map_iterators" :: "typed_iterators \<Rightarrow> typed_iterators \<Rightarrow> lambda_iterators" ("_ <- _")

  "_iterate_lambda1" :: "vname \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda" ("_ \<^bold>= _ \<^bold>| _")
  "_iterate_lambda2" :: "vname \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda" ("_ \<^bold>: _ \<^bold>= _ \<^bold>| _")
  "_iterate_lambda3" :: "lambda_iterators \<Rightarrow> vname \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda" ("_\<^bold>; _ \<^bold>= _ \<^bold>| _")
  "_iterate_lambda4" :: "lambda_iterators \<Rightarrow> vname \<Rightarrow> 'a type\<^sub>N\<^sub>E \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> iterate_lambda" ("_\<^bold>; _ \<^bold>: _ \<^bold>= _ \<^bold>| _")
  "_iteration_lambda1" :: "'a expr \<Rightarrow> iteration_lambda" ("_")
  "_iteration_lambda2" :: "lambda_iterators \<Rightarrow> 'a expr \<Rightarrow> iteration_lambda" ("_ \<^bold>| _")

  "_iterate" :: "iterate_lambda \<Rightarrow> 'a call_expr" ("iterate'(_')")

  "_anyIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("any'(_')")
  "_closureIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("closure'(_')")
  "_collectIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("collect'(_')")
  "_collectByIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("collectBy'(_')")
  "_collectNestedIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("collectNested'(_')")
  "_existsIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("exists'(_')")
  "_forAllIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("forAll'(_')")
  "_oneIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("one'(_')")
  "_isUniqueIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("isUnique'(_')")
  "_selectIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("select'(_')")
  "_rejectIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("reject'(_')")
  "_sortedByIter" :: "iteration_lambda \<Rightarrow> 'a call_expr" ("'sortedBy'(_')")

translations
  "_iterator x" == "[x]"
  "_iterators x (y # xs)" == "x # y # xs"
  "_imp_typed_iterators xs" == "CONST Iterators xs CONST None"
  "_exp_typed_iterators xs t" == "CONST Iterators xs (CONST Some t)"
  "_col_iterators xs" == "CONST CoIterators xs CONST None"
  "_map_iterators xs ys" == "CONST CoIterators xs (CONST Some ys)"

  "_iterate_lambda1 acc init body" == "CONST IterateLambda (CONST CoIterators (CONST Iterators [] CONST None) CONST None) acc CONST None init body"
  "_iterate_lambda2 acc ty init body" == "CONST IterateLambda (CONST CoIterators (CONST Iterators [] CONST None) CONST None) acc (CONST Some ty) init body"
  "_iterate_lambda3 iters acc init body" == "CONST IterateLambda iters acc CONST None init body"
  "_iterate_lambda4 iters acc ty init body" == "CONST IterateLambda iters acc (CONST Some ty) init body"
  "_iteration_lambda1 body" == "CONST NoIteratorsLambda body"
  "_iteration_lambda2 k body" == "CONST IterationLambda k body"

  "_iterate lambda" == "CONST mk_iterate lambda"

  "_anyIter lambda" == "CONST mk_iterator (CONST AnyIter) lambda"
  "_closureIter lambda" == "CONST mk_iterator (CONST ClosureIter) lambda"
  "_collectIter lambda" == "CONST mk_iterator (CONST CollectIter) lambda"
  "_collectByIter lambda" == "CONST mk_iterator (CONST CollectByIter) lambda"
  "_collectNestedIter lambda" == "CONST mk_iterator (CONST CollectNestedIter) lambda"
  "_existsIter lambda" == "CONST mk_iterator (CONST ExistsIter) lambda"
  "_forAllIter lambda" == "CONST mk_iterator (CONST ForAllIter) lambda"
  "_oneIter lambda" == "CONST mk_iterator (CONST OneIter) lambda"
  "_isUniqueIter lambda" == "CONST mk_iterator (CONST IsUniqueIter) lambda"
  "_selectIter lambda" == "CONST mk_iterator (CONST SelectIter) lambda"
  "_rejectIter lambda" == "CONST mk_iterator (CONST RejectIter) lambda"
  "_sortedByIter lambda" == "CONST mk_iterator (CONST SortedByIter) lambda"

term "src\<^bold>-\<^bold>>any(x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y'' \<^bold>: Real[1] \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y''\<^bold>, STR ''z'' \<^bold>: Real[1] \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y'' <- STR ''z''\<^bold>, STR ''w'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y'' <- STR ''z'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y'' \<^bold>: Real[1] <- STR ''z'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x''\<^bold>, STR ''y'' \<^bold>: Real[1] <- STR ''z''\<^bold>: Boolean[1] \<^bold>| x \<^bold>= y)"

term "src\<^bold>-\<^bold>>iterate(STR ''acc'' \<^bold>= z \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>iterate(STR ''acc'' \<^bold>: Real[1] \<^bold>= z \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>iterate(STR ''x''\<^bold>; STR ''acc'' \<^bold>= z \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>iterate(STR ''x''\<^bold>; STR ''acc'' \<^bold>: Real[1] \<^bold>= z \<^bold>| x \<^bold>= y)"

term "src\<^bold>-\<^bold>>any(x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x'' \<^bold>: Boolean[1] \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x'' <- STR ''y'' \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>any(STR ''x'' <- STR ''y'' \<^bold>: Boolean[1] \<^bold>| x \<^bold>= y)"
term "src\<^bold>-\<^bold>>closure(STR ''x'' <- STR ''y'' \<^bold>| x \<^bold>= y)"


term "x \<^bold>- a / IntegerLiteral 1 \<^bold>+ z"

term "\<tau>\<^bold>.allInstances()"
term "src\<^bold>.oclAsSet()"
term "x \<^bold>= y"
term "src\<^bold>.abs()"
term "\<^bold>- (src\<^bold>.abs())"

term "TypeOperationCall src ArrowCall SelectByKindOp \<tau>"
term "Call src k (TypeOperation op ty)"
term "Call src k (Iterator SelectIter its its_ty body)"
term "src\<^bold>-\<^bold>>selectByKind(\<tau>)"
term "src\<^bold>.selectByKind(\<tau>)"

end

theory ValTest2
  imports Complex_Main
begin

class opt = bot +
  fixes null :: "'a" ("\<epsilon>")

(* Nullable bool *)

typedef obool = "UNIV :: bool option set" ..

definition obool :: "bool \<Rightarrow> obool" where
  "obool b = Abs_obool (Some b)"

instantiation obool :: opt
begin
definition "\<epsilon> = Abs_obool None"
instance ..
end

free_constructors case_obool for
  obool
| "\<epsilon> :: obool"
  apply (metis Rep_obool_inverse null_obool_def obool_def not_Some_eq)
  apply (smt Abs_obool_inverse obool_def iso_tuple_UNIV_I option.inject)
  by (simp add: Abs_obool_inject null_obool_def obool_def)

ML \<open>Ctr_Sugar.ctr_sugar_of @{context} @{type_name obool} |> Option.map #ctrs\<close>

(* Nullable nat *)

typedef onat = "UNIV :: nat option set" ..

definition onat :: "nat \<Rightarrow> onat" where
  "onat b = Abs_onat (Some b)"

instantiation onat :: opt
begin
definition "\<epsilon> = Abs_onat None"
instance ..
end

free_constructors case_onat for
  onat
| "\<epsilon> :: onat"
  apply (metis Rep_onat_inverse null_onat_def onat_def not_Some_eq)
  apply (smt Abs_onat_inverse onat_def iso_tuple_UNIV_I option.inject)
  by (simp add: Abs_onat_inject null_onat_def onat_def)

(* Nullable real *)

typedef oreal = "UNIV :: real option set" ..

definition oreal :: "real \<Rightarrow> oreal" where
  "oreal b = Abs_oreal (Some b)"

instantiation oreal :: opt
begin
definition "\<epsilon> = Abs_oreal None"
instance ..
end

free_constructors case_oreal for
  oreal
| "\<epsilon> :: oreal"
  apply (metis Rep_oreal_inverse null_oreal_def oreal_def not_Some_eq)
  apply (smt Abs_oreal_inverse oreal_def iso_tuple_UNIV_I option.inject)
  by (simp add: Abs_oreal_inject null_oreal_def oreal_def)

(* Void *)

typedef void = "UNIV :: unit set" ..
instantiation void :: opt
begin
definition "\<epsilon> = Abs_void ()"
instance ..
end

(* Any *)

datatype val = BoolVal bool | NatVal nat | RealVal real

datatype oval = NullVal | BoolVal obool | NatVal onat | RealVal oreal


(* All value kinds *)

fun to_string :: "oval \<Rightarrow> string" where
  "to_string (NullVal) = ''null''"
| "to_string (BoolVal (obool x)) = ''bool(''@(if x then ''True'' else ''False'')@'')''"
| "to_string (BoolVal \<epsilon>) = ''bool(null)''"
| "to_string (NatVal x) = ''nat''"
| "to_string (RealVal x) = ''real''"

value "to_string (BoolVal (obool True))"

inductive cast :: "oval \<Rightarrow> oval \<Rightarrow> bool" (infix "as!" 55) where
  "NullVal as! (BoolVal \<epsilon>)"
| "(NatVal (onat x)) as! (RealVal (oreal x))"
| "(NatVal \<epsilon>) as! (RealVal \<epsilon>)"
| "NullVal as! (NatVal \<epsilon>)"

code_pred [show_modes] cast .

inductive_cases cast_strict_elim: "x as! y"

lemma q:
  "(NatVal (onat 1)) as! (RealVal (oreal 1.0))"
  apply (metis cast.intros(2) divide_self_if of_nat_1 zero_neq_numeral)
  done

declare [[coercion "obool :: bool \<Rightarrow> obool"]]

fun obool_and :: "obool \<Rightarrow> obool \<Rightarrow> obool" where
  "obool_and a b = (a \<and> b)"
| "obool_and \<epsilon> _ = \<epsilon>"
| "obool_and _ \<epsilon> = \<epsilon>"

value "obool_and False True"
value "obool_and False \<epsilon>"

(*
datatype val = VoidVal | BoolVal bool | NatVal nat | AnyVal any

term "BoolVal (obool True)"
term "BoolVal \<epsilon>"
term "VoidVal"

fun q :: "val \<Rightarrow> obool option" where
  "q (BoolVal (obool b)) = Some (obool (\<not> b))"
| "q _ = None"

value "q (BoolVal (obool True))"
value "q (BoolVal \<epsilon>)"

value "''1''@''2''"

fun to_string :: "val \<Rightarrow> string" where
  "to_string (VoidVal) = ''null''"
| "to_string (BoolVal (obool x)) = ''bool(''@(if x then ''True'' else ''False'')@'')''"
| "to_string (BoolVal \<epsilon>) = ''bool(null)''"
| "to_string (NatVal (onat x)) = ''nat''"
| "to_string (NatVal \<epsilon>) = ''nat(null)''"
| "to_string (AnyVal) = ''any''"

value "to_string (BoolVal (obool True))"
*)

end

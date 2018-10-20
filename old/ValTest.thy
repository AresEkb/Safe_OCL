theory ValTest
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

typedef any = "UNIV :: (bool + nat + real) set" ..

definition bool_any :: "bool \<Rightarrow> any" where
  "bool_any x = Abs_any (Inl x)"

definition nat_any :: "nat \<Rightarrow> any" where
  "nat_any x = Abs_any (Inr (Inl x))"

definition real_any :: "real \<Rightarrow> any" where
  "real_any x = Abs_any (Inr (Inr x))"

free_constructors case_any for
  bool_any
| nat_any
| real_any
  apply (metis Abs_any_cases bool_any_def nat_any_def old.sum.exhaust real_any_def)
  apply (smt Abs_any_inverse bool_any_def iso_tuple_UNIV_I old.sum.inject(1))
  apply (metis Abs_any_inverse Inl_inject UNIV_I nat_any_def sum.inject(2))
  apply (metis Abs_any_inverse Inr_inject UNIV_I real_any_def)
  apply (metis Abs_any_inverse Inl_Inr_False bool_any_def iso_tuple_UNIV_I nat_any_def)
  apply (simp add: Abs_any_inject bool_any_def real_any_def)
  by (simp add: Abs_any_inject nat_any_def real_any_def)

(* Nullable any *)

typedef oany = "UNIV :: (bool + nat + real) option set" ..

instantiation oany :: opt
begin
definition "\<epsilon> = Abs_oany None"
instance ..
end

definition bool_oany :: "bool \<Rightarrow> oany" where
  "bool_oany x = Abs_oany (Some (Inl x))"

fun obool_oany :: "obool \<Rightarrow> oany" where
  "obool_oany (obool x) = Abs_oany (Some (Inl x))"
| "obool_oany \<epsilon> = \<epsilon>"

definition nat_oany :: "nat \<Rightarrow> oany" where
  "nat_oany x = Abs_oany (Some (Inr (Inl x)))"

fun onat_oany :: "onat \<Rightarrow> oany" where
  "onat_oany (onat x) = Abs_oany (Some (Inr (Inl x)))"
| "onat_oany \<epsilon> = \<epsilon>"

definition real_oany :: "real \<Rightarrow> oany" where
  "real_oany x = Abs_oany (Some (Inr (Inr x)))"

fun oreal_oany :: "oreal \<Rightarrow> oany" where
  "oreal_oany (oreal x) = Abs_oany (Some (Inr (Inr x)))"
| "oreal_oany \<epsilon> = \<epsilon>"

fun any_oany :: "any \<Rightarrow> oany" where
  "any_oany (bool_any x) = Abs_oany (Some (Inl x))"
| "any_oany (nat_any x) = Abs_oany (Some (Inr (Inl x)))"
| "any_oany (real_any x) = Abs_oany (Some (Inr (Inr x)))"

free_constructors case_oany for
  bool_oany
| nat_oany
| real_oany
| "\<epsilon> :: oany"
  apply (metis Rep_oany_inverse bool_oany_def nat_oany_def not_Some_eq null_oany_def real_oany_def sumE)
  apply (smt Abs_oany_inverse UNIV_I bool_oany_def option.inject sum.inject(1))
  using Abs_oany_inject nat_oany_def apply auto[1]
  using Abs_oany_inject real_oany_def apply auto[1]
  apply (simp add: Abs_oany_inject bool_oany_def nat_oany_def)
  apply (simp add: Abs_oany_inject bool_oany_def real_oany_def)
  apply (simp add: Abs_oany_inject bool_oany_def null_oany_def)
  apply (simp add: Abs_oany_inject nat_oany_def real_oany_def)
  apply (simp add: Abs_oany_inject nat_oany_def null_oany_def)
  apply (simp add: Abs_oany_inject real_oany_def null_oany_def)
  done

(* All value kinds *)

fun to_string :: "oany \<Rightarrow> string" where
  "to_string (\<epsilon>) = ''null''"
| "to_string (bool_oany x) = ''bool(''@(if x then ''True'' else ''False'')@'')''"
| "to_string (nat_oany x) = ''nat''"
| "to_string (real_oany x) = ''real''"

value "to_string (bool_oany True)"

inductive cast :: "oany \<Rightarrow> oany \<Rightarrow> bool" (infix "as!" 55) where
  "\<epsilon> as! (obool_oany \<epsilon>)"
| "(nat_oany x) as! (real_oany x)"

code_pred [show_modes] cast .

inductive_cases cast_strict_elim: "x as! y"

lemma q:
  "(nat_oany 1) as! (real_oany 1.0)"
  apply (smt cast.intros(2) div_self of_nat_1)
  done

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

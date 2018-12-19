(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter{* OCL Common *}
theory OCL_Common
  imports
    Main "HOL-Library.Extended_Nat"
begin

(*** Kinds ******************************************************************)

(*type_synonym cls = "string"*)
type_synonym attr = "string"
type_synonym assoc = "string"
type_synonym role = "string"
type_synonym oid = "string"


type_synonym vname = "string"
type_synonym 'a env = "vname \<rightharpoonup> 'a"


(* Для бесконечности правила указаны явно, хотя можно было бы упростить.
   Но просто это не очень тривиально, обычно результат бесконечность, а не ошибка.
   Чтобы было явно видно *)
(*
class infinity =
  fixes infinity :: "'a"  ("\<infinity>")
*)
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


notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65)


end

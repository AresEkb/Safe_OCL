(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>OCL Common\<close>
theory OCL_Common
  imports Main "HOL-Library.Extended_Nat"
begin

type_synonym vname = "String.literal"
type_synonym 'a env = "vname \<rightharpoonup> 'a"

type_synonym attr = "String.literal"
type_synonym assoc = "String.literal"
type_synonym role = "String.literal"
type_synonym oper = "String.literal"

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

notation
  sup (infixl "\<squnion>" 65)

end

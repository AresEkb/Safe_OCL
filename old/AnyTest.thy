theory AnyTest
  imports Main
begin

datatype any = InvalidAny | BoolVal | UnlimNatVal | RealVal

datatype oany = NullAny | OInvalidAny | OBoolVal | OUnlimNatVal | ORealVal

inductive any_oany :: "any \<Rightarrow> oany \<Rightarrow> bool" where
  "any_oany InvalidAny OInvalidAny"
| "any_oany BoolVal OBoolVal"
| "any_oany UnlimNatVal OUnlimNatVal"
| "any_oany RealVal ORealVal"

fun any_to_oany :: "any \<Rightarrow> oany" where
  "any_to_oany InvalidAny = OInvalidAny"
| "any_to_oany BoolVal = OBoolVal"
| "any_to_oany UnlimNatVal = OUnlimNatVal"
| "any_to_oany RealVal = ORealVal"

declare [[coercion any_to_oany]]

lemma any_oany_eq_any_to_oany:
  "any_oany x y \<longleftrightarrow> any_to_oany x = y"
  by (cases x; cases y; simp add: any_oany.simps)



end

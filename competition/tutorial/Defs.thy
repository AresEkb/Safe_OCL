theory Defs imports Main
begin

definition hello :: "bool => bool" where [simp]:
  "hello x == x"
definition [simp]: "world == True"          

end
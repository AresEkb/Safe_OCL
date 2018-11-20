theory Defs
  imports Main
begin
  
fun sumupto :: "nat \<Rightarrow> nat" where
 "sumupto 0 = 0"
| "sumupto (Suc n) = (Suc n) + sumupto n"

print_theorems

end
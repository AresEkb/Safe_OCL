theory Defs imports Main
begin

fun sum where "sum 0 = 0" | "sum (Suc n) = Suc n + sum n"

end
theory Submission
  imports Defs
begin
(*
abbreviation "list_mod xs \<equiv>
  let m = fold max xs (0::nat) in
  m + 3 - m mod 3"

value "list_mod [1::nat,5,7,4,8,9]"
value "list_mod [1::nat,5,7,4,8]"
value "list_mod [1::nat,5,7,4]"
value "list_mod [1::nat,5,7,4,10]"
value "list_mod [1::nat,5,4]"
value "list_mod [1::nat,4]"
value "list_mod [1::nat,2]"
value "list_mod [3::nat, 2]"
*)

fun map' where
  "map' P f [] found = []"
| "map' P f (x # xs) found = (if P x \<and> \<not> found
    then x # (map' P f xs True)
    else (f x) # (map' P f xs found))"
(*
abbreviation "shift xs \<equiv>
  let m = fold max xs (0::nat) in
  let n = m + 3 - m mod 3 in
  let ys = map' (\<lambda>x. x = m) (\<lambda>x. (x + n div 3) mod n) xs False in
  ys"
*)

abbreviation "shift xs \<equiv>
  let m = fold max xs (0::nat) in
  let n = m + 3 - m mod 3 in
  let ys = map (\<lambda>x. (x + n div 3) mod n) xs in
  ys"

value "shift [3::nat,2]"
value "shift (shift [3::nat,2])"
value "shift (shift (shift [3::nat,2]))"

value "shift [1::nat,5,7,4,8,9]"
value "shift (shift [1::nat,5,7,4,8,9])"
value "shift (shift (shift [1::nat,5,7,4,8,9]))"

lemma q:
  "shift (shift (shift xs)) = xs"




lemma showmewhatyougot:
  "\<exists>f::(nat list \<Rightarrow> nat list). (\<forall> xs. (length xs \<ge> 2 \<longrightarrow> f xs \<noteq> xs))
           \<and> (\<forall> xs. (f (f (f xs))) = xs)"
  apply auto



end
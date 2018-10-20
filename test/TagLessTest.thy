theory TagLessTest
  imports Main
begin

term fst
definition "varZ env \<equiv> fst env"
definition "varS vp env \<equiv> vp (snd env)"
definition "b (bv :: bool) env \<equiv> bv"
definition "lam e env \<equiv> \<lambda>x. e (x, env)"
definition "app e1 e2 env \<equiv> (e1 env) (e2 env)"

definition "testf1 \<equiv> app (lam varZ) (b True)"
definition "testf3 \<equiv> app (lam (varS varZ)) (b True)"

value "testf1 ()"
value "testf3 ()"

typedecl ('c, 'dv) repr

locale lang =
  fixes int' :: "int \<Rightarrow> ('c, int) repr"
    and bool' :: "bool \<Rightarrow> ('c, bool) repr"
    and lam' :: "(('c, 'da) repr \<Rightarrow> ('c, 'db) repr) \<Rightarrow> ('c, 'da \<Rightarrow> 'db) repr"
    and app' :: "('c, 'da \<Rightarrow> 'db) repr \<Rightarrow> ('c, 'da) repr \<Rightarrow> ('c, 'db) repr"
    and fix' :: "('x \<Rightarrow> 'x) \<Rightarrow> (('c, 'da \<Rightarrow> 'db) repr)"
    and add' :: "('c, int) repr \<Rightarrow> ('c, int) repr \<Rightarrow> ('c, int) repr"
    and mul' :: "('c, int) repr \<Rightarrow> ('c, int) repr \<Rightarrow> ('c, int) repr"
    and leq' :: "('c, int) repr \<Rightarrow> ('c, int) repr \<Rightarrow> ('c, bool) repr"
    and if' :: "('c, bool) repr \<Rightarrow> (unit \<Rightarrow> 'x) \<Rightarrow> (unit \<Rightarrow> 'x) \<Rightarrow> (('c, 'da) repr)"

definition "int'' (x :: int) \<equiv> x"

interpretation lang 
  rewrites "int' y \<equiv> (y, y)"

term "app' (lam' (\<lambda>x. x)) (bool' True)"

end

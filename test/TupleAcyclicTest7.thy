theory TupleAcyclicTest7
  imports Main "../Transitive_Closure_Ext"
    "../Tuple"
begin

datatype (plugins del: "size") 'a t = A | B | C "(nat, 'a t) fmap"

abbreviation "tcf \<equiv> (\<lambda> v::(nat \<times> nat). (\<lambda> r::nat. snd v + r))"

interpretation tcf: comp_fun_commute tcf
proof 
  fix x y
  show "tcf y \<circ> tcf x = tcf x \<circ> tcf y"
  proof -
    fix z
    have "(tcf y \<circ> tcf x) z = snd y + snd x + z" by auto
    also have "(tcf x \<circ> tcf y) z = snd y + snd x + z" by auto
    ultimately have "(tcf y \<circ> tcf x) z = (tcf x \<circ> tcf y) z" by auto
    then show "(tcf y \<circ> tcf x) = (tcf x \<circ> tcf y)" by auto
  qed
qed

instantiation t :: (size) size 
begin

primrec t_size :: "'a t \<Rightarrow> nat" where
AR: "t_size A = 0" |
BR: "t_size B = 0" |
CR: "t_size (C x) =
  (Suc 0) + ffold tcf 0 (fset_of_fmap (fmmap t_size x))"
(*  (Suc 0) + ffold tcf 0 (fset_of_fmap (fmmap t_size x))"*)

definition size_t where
size_t_def: "size_t = t_size"

instance ..

end

(*
fun supc where
  "supc f xs ys =
    fmap_of_list (map
      (\<lambda>k. (k, f (the (fmlookup xs k)) (the (fmlookup ys k))))
      (sorted_list_of_fset (fmdom xs |\<inter>| fmdom ys)))"
*)

lemma ffold_rec_exp:
  assumes "k |\<in>| fmdom x"
    and "ky = (k, the (fmlookup (fmmap t_size x) k))"
  shows "ffold tcf 0 (fset_of_fmap (fmmap t_size x)) = 
        tcf ky (ffold tcf 0 ((fset_of_fmap (fmmap t_size x)) |-| {|ky|}))"
  using assms tcf.ffold_rec by auto

lemma elem_le_ffold:
  assumes "k |\<in>| fmdom x"
  shows "t_size (the (fmlookup x k)) < 
        (Suc 0) + ffold tcf 0 (fset_of_fmap (fmmap t_size x))"
  using ffold_rec_exp assms by auto

lemma measure_cond:
  assumes "k |\<in>| fmdom x"
  shows "size (the (fmlookup x k)) < size (C x)"
  using assms elem_le_ffold size_t_def by auto
(*
lemma q:
  "size (x::t) < size (C y)"
  apply (auto simp add: size_t_def)
  apply (induct x arbitrary: y)
  apply simp
  apply simp
*)
(*
abbreviation
  "suptuple f xs ys \<equiv>
    fmfilter (\<lambda>k. k |\<notin>| fmdom ys) xs ++\<^sub>f
    fmmap_keys (\<lambda>k x. f x (the (fmlookup ys k))) (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs) ++\<^sub>f
    fmfilter (\<lambda>k. k |\<notin>| fmdom xs) ys"

abbreviation
  "suptuple f xs ys \<equiv>
    fmmap (\<lambda>k x. f x (case (fmlookup ys k) of Some y \<Rightarrow> y | None \<Rightarrow> x)) xs"
*)


term fset_of_fmap
term fmap_of_list
term sorted_list_of_fmap

abbreviation
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
(*
abbreviation
  "supc f xs ys \<equiv>
    fmap_of_list (map
      (\<lambda>(k, x). (k, f x (the (fmlookup ys k))))
      (sorted_list_of_fmap (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)))"

term fmap_of_list
term "x \<circ> y"

fun supc where
  "supc f xs ys =
    (fmap_of_list \<circ> (map
      (\<lambda>k. (k, if k |\<in>| fmdom xs then f
        (the (fmlookup xs k))
        (the (fmlookup ys k)) else A))
      )) (sorted_list_of_fset (fmdom xs |\<inter>| fmdom ys))"
*)
(* (sorted_list_of_fset (fmdom xs |\<inter>| fmdom ys)) *)
(*
abbreviation
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"
*)
term fmfilter

function sup_t (infixl "\<squnion>" 65) where
  "A \<squnion> _ = A"
| "B \<squnion> x = (if x = B then B else A)"
| "C xs \<squnion> x = (case x of C ys \<Rightarrow> C (supc sup_t xs ys) | _ \<Rightarrow> A)"
| "D xs \<squnion> y = (case y of D ys \<Rightarrow> D (xs \<squnion> ys) | _ \<Rightarrow> A)"
| "E xs \<squnion> y = (case y of E ys \<Rightarrow> E (xs \<squnion> ys) | _ \<Rightarrow> A)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(xs, ys). size ys)")
  using measure_cond apply auto
  done

(*
function sup_t (infixl "\<squnion>" 65) where
  "A \<squnion> _ = A"
| "B \<squnion> x = (if x = B then B else A)"
| "C xs \<squnion> x = (case x of C ys \<Rightarrow> C (supc sup_t xs ys) | _ \<Rightarrow> A)"
  by pat_completeness auto
termination
  apply auto
*)


value "size (2::nat)"
value "\<Sum>x\<in>set [1::nat, 2::nat]. x"


definition "t3 \<equiv> fmupd (1::nat) (A::t) (fmupd (2::nat) (B::t) fmempty)"
definition "t4 \<equiv> fmupd (3::nat) (B::t) (fmupd (1::nat) (A::t) (fmupd (2::nat) (B::t) fmempty))"

(* Подумать над направлением этого символа, по идее должно быть наоборот *)
inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys \<Longrightarrow>
   C xs \<sqsubset> C ys"

code_pred [show_modes] subtype .

value "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) t3 t3"
value "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) t3 t4"
value "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) t4 t3"

lemma subtype_asym:
  "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  using subtype.cases apply blast
  apply (erule subtype.cases)
  apply auto[1]
  apply (rule_tac ?f="subtype" and ?xs="xs" and ?ys="ys" in strict_subtuple_antisym; simp)
  done

lemma trancl_subtype_x_A [elim]:
  "subtype\<^sup>+\<^sup>+ x A \<Longrightarrow> P"
  apply (induct rule: converse_tranclp_induct)
  using subtype.cases by auto

lemma trancl_subtype_B_x [elim]:
  "subtype\<^sup>+\<^sup>+ B x \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  using subtype.cases by auto

lemma C_functor:
  "functor_under_rel (strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)) subtype C"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  apply (metis rangeI subtype.simps t.distinct(5))
  apply (meson injI t.inject)
  using subtype_asym apply auto[1]
  using subtype.simps by blast

lemma trancl_subtype_C_C:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys"
  using C_functor tranclp_fun_preserve_gen_1a by fastforce

lemma trancl_subtype_C_C':
  "(strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in subtype (fmran' xs) \<Longrightarrow>
   strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis (mono_tags, lifting) strict_subtuple_mono tranclp.r_into_trancl)
  using strict_subtuple_trans3 by blast

lemma trancl_subtype_C_C'':
  "strict_subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   strict_subtuple subtype\<^sup>*\<^sup>* xs ys"
  unfolding tranclp_into_rtranclp2
  by simp

lemma trancl_subtype_C_C''':
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   acyclic_in subtype (fmran' xs) \<Longrightarrow>
   strict_subtuple subtype\<^sup>*\<^sup>* xs ys"
  using trancl_subtype_C_C trancl_subtype_C_C' trancl_subtype_C_C'' by blast

lemma trancl_subtype_C_x':
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   acyclic_in subtype (fmran' xs) \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> strict_subtuple subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis subtype.cases t.distinct(3) trancl_subtype_C_C''' tranclp.r_into_trancl)
  by (metis subtype.cases t.distinct(4) trancl_subtype_C_C''' tranclp.trancl_into_trancl)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct x arbitrary: y)
  apply auto[1]
  apply auto[1]
  by (meson trancl_subtype_C_C''' tranclp_trans)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> subtuple subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  using trancl_subtype_acyclic trancl_subtype_C_x' by blast


end

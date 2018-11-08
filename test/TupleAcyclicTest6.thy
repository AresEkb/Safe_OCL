theory TupleAcyclicTest6
  imports Main "../Transitive_Closure_Ext"
    "../Tuple"
begin

datatype t = A | B | C "(nat, t) fmap"

definition "t1 \<equiv> fmupd (1::nat) (A::t) (fmupd (2::nat) (B::t) fmempty)"
definition "t2 \<equiv> fmupd (3::nat) (B::t) (fmupd (1::nat) (A::t) (fmupd (2::nat) (B::t) fmempty))"

(* Подумать над направлением этого символа, по идее должно быть наоборот *)
inductive subtype ("_ \<sqsubset> _" [65, 65] 65) where
  "A \<sqsubset> B"
| "subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) xs ys \<Longrightarrow>
   C xs \<sqsubset> C ys"

code_pred [show_modes] subtype .

value "subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) t1 t1"
value "subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) t1 t2"
value "subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y) t2 t1"

lemma subtype_asym:
  "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
  apply (induct rule: subtype.induct)
  using subtype.cases apply blast
  apply (erule subtype.cases; auto simp add: subtuple_def)
  by (metis fmap_ext fmlookup_restrict_fset fmrestrict_fset_dom option.inject)

lemma trancl_subtype_x_A [elim]:
  "subtype\<^sup>+\<^sup>+ x A \<Longrightarrow> P"
  apply (induct rule: converse_tranclp_induct)
  using subtype.cases by auto

lemma trancl_subtype_B_x [elim]:
  "subtype\<^sup>+\<^sup>+ B x \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  using subtype.cases by auto

lemma C_functor:
  "functor_under_rel (subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)) subtype C"
  unfolding functor_under_rel_def rel_limited_under_def
  apply auto
  apply (metis rangeI subtype.simps t.distinct(5))
  apply (meson injI t.inject)
  using subtype.simps by blast

lemma trancl_subtype_C_C:
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   (subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys"
  using C_functor tranclp_fun_preserve_gen_1a by fastforce

lemma trancl_subtype_C_C':
  "(subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y))\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   acyclic_in subtype (fmran' xs) \<Longrightarrow>
   subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (metis (mono_tags, lifting) subtuple_mono tranclp.r_into_trancl)
  using subtuple_trans3 by blast

lemma trancl_subtype_C_C'':
  "subtuple (\<lambda>x y. x = y \<or> x \<sqsubset> y)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   subtuple subtype\<^sup>*\<^sup>* xs ys"
  unfolding tranclp_into_rtranclp2
  by simp

lemma trancl_subtype_C_C''':
  "subtype\<^sup>+\<^sup>+ (C xs) (C ys) \<Longrightarrow>
   acyclic_in subtype (fmran' xs) \<Longrightarrow>
   subtuple subtype\<^sup>*\<^sup>* xs ys"
  by (simp add: trancl_subtype_C_C trancl_subtype_C_C' trancl_subtype_C_C'')

lemma trancl_subtype_C_x':
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   acyclic_in subtype (fmran' xs) \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> subtuple subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  apply (induct rule: tranclp_induct)
  apply (metis subtype.cases t.distinct(3) trancl_subtype_C_C''' tranclp.r_into_trancl)
  by (metis subtype.cases t.distinct(4) trancl_subtype_C_C''' tranclp.trancl_into_trancl)

lemma trancl_subtype_acyclic:
  "subtype\<^sup>+\<^sup>+ x y \<Longrightarrow> subtype\<^sup>+\<^sup>+ y x \<Longrightarrow> False"
  apply (induct x arbitrary: y)
  apply auto[1]
  apply auto[1]
  by (metis subtuple_def trancl_subtype_C_C''' tranclp_trans)

lemma trancl_subtype_C_x [elim]:
  "subtype\<^sup>+\<^sup>+ (C xs) y \<Longrightarrow>
   (\<And>ys. y = C ys \<Longrightarrow> subtuple subtype\<^sup>*\<^sup>* xs ys \<Longrightarrow> P) \<Longrightarrow> P"
  using trancl_subtype_acyclic trancl_subtype_C_x' by blast

end

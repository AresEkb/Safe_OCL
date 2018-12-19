(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
theory List_Ext
  imports Main
begin

lemma rtrancl_to_list_all2:
  "(list_all2 P)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   list_all2 P\<^sup>*\<^sup>* xs ys"
  apply (induct rule: rtranclp_induct)
  apply (simp add: list.rel_refl)
  by (smt list_all2_trans rtranclp.rtrancl_into_rtrancl)

lemma trancl_to_list_all2:
  "(list_all2 P)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 P\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (simp add: list.rel_mono_strong)
  by (smt list_all2_trans tranclp.trancl_into_trancl)

text{* The proof was derived from the accepted answer on the website
 Stack Overflow that is available at
 https://stackoverflow.com/a/52970733/632199
 and provided with the permission of the author of the answer *}

lemma list_all2_to_rtrancl:
  assumes as_r: "(\<forall>x. P x x)" 
  shows "list_all2 P\<^sup>*\<^sup>* xs ys \<Longrightarrow> (list_all2 P)\<^sup>*\<^sup>* xs ys"
proof(induction rule: list_all2_induct)
  case Nil then show ?case by simp
next
  case (Cons x xs y ys) show ?case
  proof -
    from as_r obtain zs where 
      lp_xs_zs: "(list_all2 P) xs zs" and lp_pp_xs_zs: "(list_all2 P)\<^sup>+\<^sup>+ zs ys"
      by (metis Cons.IH Nitpick.rtranclp_unfold list_all2_refl 
         tranclp.r_into_trancl)
    from Cons.hyps(1) have x_xs_y_zs: "(list_all2 P)\<^sup>*\<^sup>* (x#xs) (y#zs)"
    proof(induction rule: rtranclp_induct)
      case base then show ?case using as_r lp_xs_zs by blast
    next
      case (step y z) then show ?case 
        using as_r by (metis list.simps(11) list_all2_same rtranclp.simps)
    qed
    from lp_pp_xs_zs have "(list_all2 P)\<^sup>*\<^sup>* (y#zs) (y#ys)"
    proof(induction rule: tranclp_induct)
      case (base y) then show ?case using as_r by blast
    next
      case (step y z) then show ?case 
        using as_r by (simp add: rtranclp.rtrancl_into_rtrancl)
    qed
    with x_xs_y_zs show ?thesis by force
  qed
qed

lemma list_all2_to_trancl:
  assumes as_r: "(\<forall>x. P x x)" 
  shows "list_all2 P\<^sup>+\<^sup>+ xs ys \<Longrightarrow> (list_all2 P)\<^sup>+\<^sup>+ xs ys"
  by (metis (mono_tags, lifting) assms list_all2_refl list_all2_to_rtrancl
            r_into_rtranclp reflclp_tranclp rtrancl_to_list_all2 rtranclpD
            rtranclp_idemp rtranclp_reflclp tranclp.r_into_trancl)

end

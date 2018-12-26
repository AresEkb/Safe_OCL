(*  Title:       Simple OCL Semantics
    Author:      Denis Nikiforov, December 2018
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
theory List_Ext
  imports Main
begin

lemma rtrancl_to_list_all2:
  "(list_all2 r)\<^sup>*\<^sup>* xs ys \<Longrightarrow>
   list_all2 r\<^sup>*\<^sup>* xs ys"
  apply (induct rule: rtranclp_induct)
  apply (simp add: list.rel_refl)
  by (rule list_all2_trans; auto)

lemma trancl_to_list_all2:
  "(list_all2 r)\<^sup>+\<^sup>+ xs ys \<Longrightarrow>
   list_all2 r\<^sup>+\<^sup>+ xs ys"
  apply (induct rule: tranclp_induct)
  apply (simp add: list.rel_mono_strong)
  by (rule list_all2_trans; auto)

text{* The following proofs were derived from the accepted answer
 on the website Stack Overflow that is available at
 https://stackoverflow.com/a/52970733/632199
 and provided with the permission of the author of the answer *}

lemma set_listrel_eq_list_all2: 
  "listrel {(x, y). r x y} = {(xs, ys). list_all2 r xs ys}"
  using list_all2_conv_all_nth listrel_iff_nth by fastforce

lemma listrel_tclosure_1: "(listrel r)\<^sup>* \<subseteq> listrel (r\<^sup>*)"
  by (simp add: listrel_rtrancl_eq_rtrancl_listrel1 
      listrel_subset_rtrancl_listrel1 rtrancl_subset_rtrancl)

lemma listrel_tclosure_2: "refl r \<Longrightarrow> listrel (r\<^sup>*) \<subseteq> (listrel r)\<^sup>*"
  by (simp add: listrel1_subset_listrel listrel_rtrancl_eq_rtrancl_listrel1 
      rtrancl_mono)

context includes lifting_syntax
begin

lemma listrel_list_all2_transfer [transfer_rule]:
  "((=) ===> (=) ===> (=) ===> (=)) 
  (\<lambda>r xs ys. (xs, ys) \<in> listrel {(x, y). r x y}) list_all2"
  unfolding rel_fun_def using set_listrel_eq_list_all2 listrel_iff_nth by blast

end

lemma list_all2_to_rtrancl:
  "reflp r \<Longrightarrow> list_all2 r\<^sup>*\<^sup>* xs ys \<Longrightarrow> (list_all2 r)\<^sup>*\<^sup>* xs ys"
proof (transfer)
  fix r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fix xs :: "'a list"
  fix ys :: "'a list"
  assume as_reflp: "reflp r" 
  assume p_in_lr: "(xs, ys) \<in> listrel {(x, y). r\<^sup>*\<^sup>* x y}"
  from as_reflp have refl: "refl {(x, y). r x y}" 
    using reflp_refl_eq by fastforce
  from p_in_lr have "(xs, ys) \<in> listrel ({(x, y). r x y}\<^sup>*)"
    unfolding rtranclp_def rtrancl_def by auto
  with refl have "(xs, ys) \<in> (listrel {(x, y). r x y})\<^sup>*"
    using listrel_tclosure_2 by auto
  then show "(\<lambda>xs ys. (xs, ys) \<in> listrel {(x, y). r x y})\<^sup>*\<^sup>* xs ys" 
    unfolding rtranclp_def rtrancl_def by auto
qed

lemma list_all2_to_trancl:
  "reflp r \<Longrightarrow> list_all2 r\<^sup>+\<^sup>+ xs ys \<Longrightarrow> (list_all2 r)\<^sup>+\<^sup>+ xs ys"
  by (metis list.rel_reflp list_all2_to_rtrancl r_into_rtranclp
            reflclp_tranclp reflpD rtrancl_to_list_all2 rtranclpD
            rtranclp_idemp rtranclp_reflclp tranclp.r_into_trancl)

end

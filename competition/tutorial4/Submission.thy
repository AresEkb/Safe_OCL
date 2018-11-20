theory Submission 
imports Defs
begin

lemma q:
  "sum n \<le> sum m \<Longrightarrow>
   sum n \<le> Suc (m + sum m)"
  by auto

lemma goal1: "n \<le> m \<Longrightarrow> sum n \<le> sum m"
  apply (induct m arbitrary: n)
  apply simp
  apply (erule le_SucE; simp add: q)
  done

lemma goal2: "n <= sum n"
  by (induct n; simp)

lemma goal3: "\<And>M. (\<exists>N. \<forall>n\<ge>N. sum n \<ge> M)"
  using goal2 le_trans by blast

end
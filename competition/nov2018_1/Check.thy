theory Check
  imports Submission
begin

lemma  "\<exists>f::(nat list \<Rightarrow> nat list). (\<forall> xs. (length xs \<ge> 2 \<longrightarrow> f xs \<noteq> xs))
           \<and> (\<forall> xs. (f (f (f xs))) = xs)"
by (rule Submission.showmewhatyougot)


end
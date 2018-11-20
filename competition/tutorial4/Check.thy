theory Check imports Submission begin 


lemma "n \<le> m \<Longrightarrow> sum n \<le> sum m" by(rule Submission.goal1)

lemma "n <= sum n" by(rule Submission.goal2)

lemma "\<And>M. (\<exists>N. \<forall>n\<ge>N. sum n \<ge> M)" by(rule Submission.goal3) 

end
theory Check
  imports Submission
begin
 
lemma "sumupto n = n * (n+1) div 2"
by (rule Submission.kleiner_gauss)

end
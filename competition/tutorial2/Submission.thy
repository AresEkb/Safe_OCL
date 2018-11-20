theory Submission
  imports Defs
begin

lemma kleiner_gauss: "sumupto n = n * (n+1) div 2"
  by (induct n; simp)

end
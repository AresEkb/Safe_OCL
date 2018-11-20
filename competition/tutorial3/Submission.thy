theory Submission
  imports Defs
begin
 
  
lemma rev_append: "rev (xs @ ys) = rev ys @ rev xs"
  by (induct xs; auto)
  
lemma doublerev: "rev (rev xs) = xs"
  by (induct xs; auto simp add: Submission.rev_append)


end
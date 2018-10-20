theory RelFSetTest
  imports
    Main
    "~~/src/HOL/Library/FSet"
begin

lemma q:
  "rel_fset
        (\<lambda>x1 x2.
            cast_val x1 x2 \<and>
            (cast_val x2 x1 \<longrightarrow> x1 = x2))
        xs ys \<Longrightarrow>
       xs \<noteq> {||} \<Longrightarrow>
       ys \<noteq> {||} \<Longrightarrow>
       rel_fset cast_val ys xs \<Longrightarrow>
       xs = ys"

lemma q:
  "rel_fset
        (\<lambda>x1 x2.
            cast_val x1 x2 \<and> \<not> cast_val x2 x1)
        xs ys \<Longrightarrow>
       xs \<noteq> {||} \<Longrightarrow>
       ys \<noteq> {||} \<Longrightarrow>
       \<not> rel_fset cast_val ys xs"
  
  
  nitpick


lemma antisym_rel_fset_cast_val2:
  "rel_fset (\<lambda>x y. R x y \<and> \<not> R y x) xs ys \<Longrightarrow>
   xs \<noteq> {||} \<Longrightarrow>
   ys \<noteq> {||} \<Longrightarrow>
   \<not> rel_fset R ys xs"
  apply (induct)


end
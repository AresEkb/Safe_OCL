theory MeasureTest
  imports Main "~~/src/HOL/Library/Finite_Map"
begin

datatype (plugins del: "size") 'a t = A | B | C "(nat, 'a t) fmap"

abbreviation "tcf \<equiv> (\<lambda> v::(nat \<times> nat). (\<lambda> r::nat. snd v + r))"

interpretation tcf: comp_fun_commute tcf
proof 
  fix x y
  show "tcf y \<circ> tcf x = tcf x \<circ> tcf y"
  proof -
    fix z
    have "(tcf y \<circ> tcf x) z = snd y + snd x + z" by auto
    also have "(tcf x \<circ> tcf y) z = snd y + snd x + z" by auto
    ultimately have "(tcf y \<circ> tcf x) z = (tcf x \<circ> tcf y) z" by auto
    then show "(tcf y \<circ> tcf x) = (tcf x \<circ> tcf y)" by auto
  qed
qed

instantiation t :: (type) size 
begin

primrec t_size :: "'a t \<Rightarrow> nat" where
AR: "t_size A = 0" |
BR: "t_size B = 0" |
CR: "t_size (C x) = 
  (Suc 0) + ffold tcf 0 (fset_of_fmap (fmmap t_size x))"

definition size_t where
size_t_def: "size_t = t_size"

instance ..

end

lemma ffold_rec_exp:
  assumes "k |\<in>| fmdom x"
    and "ky = (k, the (fmlookup (fmmap t_size x) k))"
  shows "ffold tcf 0 (fset_of_fmap (fmmap t_size x)) = 
        tcf ky (ffold tcf 0 ((fset_of_fmap (fmmap t_size x)) |-| {|ky|}))"
  using assms tcf.ffold_rec by auto

lemma elem_le_ffold:
  assumes "k |\<in>| fmdom x"
  shows "t_size (the (fmlookup x k)) < 
        (Suc 0) + ffold tcf 0 (fset_of_fmap (fmmap t_size x))"
  using ffold_rec_exp assms by auto

lemma measure_cond:
  assumes "k |\<in>| fmdom x"
  shows "size (the (fmlookup x k)) < size (C x)"
  using assms elem_le_ffold size_t_def by auto

abbreviation
  "supc f xs ys \<equiv>
    fmmap_keys
      (\<lambda>k x. if (k |\<in>| fmdom ys) then (f x (the (fmlookup ys k))) else A)
      (fmfilter (\<lambda>k. k |\<in>| fmdom ys) xs)"

function sup_t (infixl "\<squnion>" 65) where
  "A \<squnion> _ = A"
| "B \<squnion> x = (if x = B then B else A)"
| "C xs \<squnion> x = (case x of C ys \<Rightarrow> C (supc sup_t xs ys) | _ \<Rightarrow> A)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(xs, ys). size ys)")
  using measure_cond apply auto
  done

value "size (2::nat)"
value "\<Sum>x\<in>set [1::nat, 2::nat]. x"

end

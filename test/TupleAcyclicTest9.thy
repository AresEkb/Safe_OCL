theory TupleAcyclicTest9
  imports Main "../Transitive_Closure_Ext"
    "../Tuple"
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

primrec size_t :: "'a t \<Rightarrow> nat" where
AR: "size_t A = 0" |
BR: "size_t B = 0" |
CR: "size_t (C x) =
  Suc (ffold tcf 0 (fset_of_fmap (fmmap size_t x)))"
(*  (Suc 0) + ffold tcf 0 (fset_of_fmap (fmmap t_size x))"*)

instance ..

end

lemma ffold_rec_exp:
  assumes "k |\<in>| fmdom x"
    and "ky = (k, the (fmlookup (fmmap f x) k))"
  shows "ffold tcf 0 (fset_of_fmap (fmmap f x)) = 
        tcf ky (ffold tcf 0 ((fset_of_fmap (fmmap f x)) |-| {|ky|}))"
  using assms tcf.ffold_rec by auto

lemma elem_le_ffold:
  "k |\<in>| fmdom x \<Longrightarrow>
   f (the (fmlookup x k)) < Suc (ffold tcf 0 (fset_of_fmap (fmmap f x)))"
  by (subst ffold_rec_exp, auto)

lemma measure_cond:
  "k |\<in>| fmdom x \<Longrightarrow>
   size (the (fmlookup x k)) < size (C x)"
  using elem_le_ffold by auto

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

end

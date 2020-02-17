theory Inductive_proof_example
  imports Main
begin

inductive subseq where
 "subseq [] l"
| "subseq l1 l2 \<Longrightarrow> subseq (x # l1) (x # l2)"
| "subseq l1 l2 \<Longrightarrow> subseq l1 (x # l2)"

lemma 
  assumes "subseq l1' l2"
  assumes "l1' = (x # l1)"
  shows "subseq l1 l2"
  using assms
  apply(induction rule: subseq.induct)
    apply simp
   apply(intro subseq.intros(3),simp)
  by (simp add: subseq.intros(3))

lemma 
  assumes "subseq (x # l1) l2"
  shows "subseq l1 l2"
  using assms
  apply(induction "x # l1" "l2" rule: subseq.induct)
    apply simp
   apply(intro subseq.intros(3),simp)
  by (intro subseq.intros(3))


end
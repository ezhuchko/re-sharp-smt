import Regex.RESharp.RESharp
import Regex.EREa.Metrics

/-!
# Metrics

Collection of all the various metrics used in the formalization
to ensure the well-foundedness of the algorithm.
-/

open RESharp EREa

/-- Size of metric function, counting the number of constructors. -/
@[simp]
def RESharp.sizeOf (r : RESharp α) : ℕ :=
  match r with
  | .Ere r    => r.sizeOf
  | Compl r   => 1 + sizeOf r
  | Inter l r => 1 + sizeOf l + sizeOf r
  | Alt l r   => 1 + sizeOf l + sizeOf r
  | Lookahead l r => 1 + sizeOf l + r.sizeOf
  | NLookahead l r => 1 + sizeOf l + r.sizeOf
  | Lookbehind l r => 1 + l.sizeOf + sizeOf r
  | NLookbehind l r => 1 + l.sizeOf + sizeOf r

/-- Lexicographic combination of star height and size of regexp. -/
def RESharp.star_metric (r : RESharp α) : ℕ ×ₗ ℕ :=
  match r with
  | .Ere r    => 1 + r.star_metric
  | Compl r   => ((star_metric r).1, 1 + (star_metric r).2)
  | Inter l r => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | Alt l r   => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | Lookahead l r => (max (star_metric l).1 (r.star_metric).1, 1 + (star_metric l).2 + (r.star_metric).2)
  | Lookbehind l r => (max (l.star_metric).1 (star_metric r).1, 1 + (l.star_metric).2 + (star_metric r).2)
  | NLookahead l r => (max (star_metric l).1 (r.star_metric).1, 1 + (star_metric l).2 + (r.star_metric).2)
  | NLookbehind l r => (max (l.star_metric).1 (star_metric r).1, 1 + (l.star_metric).2 + (star_metric r).2)

theorem EREa.star_metric_ere {r : EREa α}:
  r.star_metric < (RESharp.Ere r).star_metric := by
  simp[RESharp.star_metric]
  exact Prod.Lex.left _ _ (by simp_all only [Prod.fst_one, lt_add_iff_pos_left, zero_lt_one])

theorem RESharp.star_metric_lookbehind :
  r.star_metric < (Lookbehind l r).star_metric := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem RESharp.star_metric_lookahead :
  l.star_metric < (Lookahead l r).star_metric := by
  simp[RESharp.star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp
  split
  . by_cases h : ((star_metric l).fst = (r.star_metric).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)

theorem RESharp.star_metric_nlookbehind :
  r.star_metric < (NLookbehind l r).star_metric := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem RESharp.star_metric_nlookahead :
  l.star_metric < (NLookahead l r).star_metric := by
  simp[RESharp.star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp
  split
  . by_cases h : ((star_metric l).fst = (r.star_metric).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)


theorem RESharp.star_metric_altL :
  star_metric l < star_metric (l.Alt r) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp_rw [g]; simp only [ite_true]
    by_cases g1 : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←g1]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g g1)
  . simp_rw [g]; simp [ite_false]
    exact Prod.Lex.right _ (by linarith)

theorem RESharp.star_metric_altR :
  star_metric r < star_metric (Alt l r) := by
  simp only [star_metric, ge_iff_le];
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem RESharp.star_metric_neg :
  star_metric r < (star_metric (.Compl r)) := by
  simp only [star_metric]
  apply Prod.Lex.right _ (by simp [lt_add_iff_pos_left])

theorem RESharp.star_metric_interL :
  star_metric l < (star_metric (.Inter l r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . simp only at h
      exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)

theorem RESharp.star_metric_interR :
  star_metric r < (star_metric (.Inter l r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

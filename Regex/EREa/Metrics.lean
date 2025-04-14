import Regex.EREa.EREa
import Regex.EREwLookarounds.Definitions

/-!
# Metrics

Collection of all the various metrics for `EREa` used in the formalization
to ensure the well-foundedness of the algorithm.
-/

open EREa

/-- Size of metric function, counting the number of constructors. -/
@[simp]
def EREa.sizeOf (r : EREa α) : ℕ :=
  match r with
  | ε           => 0
  | EREa.Pred _ => 0
  | l ⋓⚓ r     => 1 + sizeOf l + sizeOf r
  | l ⋒⚓ r     => 1 + sizeOf l + sizeOf r
  | l ⬝⚓ r     => 1 + sizeOf l + sizeOf r
  | r *⚓       => 1 + sizeOf r
  | ~⚓ r       => 1 + sizeOf r
  | StartAnchor => 0
  | EndAnchor   => 0

/-- Lexicographic combination of star height and size of regexp. -/
def EREa.star_metric (r : EREa α) : ℕ ×ₗ ℕ :=
  match r with
  | ε           => (0, 0)
  | EREa.Pred _ => (0, 0)
  | l ⋓⚓ r     => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⋒⚓ r     => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | l ⬝⚓ r     => (max (star_metric l).1 (star_metric r).1, 1 + (star_metric l).2 + (star_metric r).2)
  | r *⚓       => (1 + (star_metric r).1, 1 + (star_metric r).2)
  | ~⚓ r       => ((star_metric r).1, 1 + (star_metric r).2)
  | StartAnchor => (0, 0)
  | EndAnchor   => (0, 0)

theorem star_metric_catL :
  star_metric l < (star_metric (l ⬝⚓ r)) := by
  simp only [star_metric]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)

theorem star_metric_catR :
  star_metric r < (star_metric (l ⬝⚓ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem star_metric_altL :
  star_metric l < (star_metric (l ⋓⚓ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  by_cases g : (star_metric l).fst ≤ (star_metric r).fst
  . simp_rw [g]; simp only [ite_true]
    by_cases g1 : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←g1]; exact Prod.Lex.right _ (by linarith)
    . exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne g g1)
  . simp_rw [g]
    exact Prod.Lex.right _ (by linarith)

theorem star_metric_altR :
  star_metric r < (star_metric (l ⋓⚓ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem EREa.star_metric_repeat_first :
  (star_metric (r ⁽ n ⁾⚓)).fst < 1 + (star_metric r).fst :=
  match n with
  | 0          => by
    simp only [star_metric, Prod.mk_zero_zero, Prod.fst_zero, add_pos_iff, zero_lt_one, true_or]
  | Nat.succ n => by
    simp only [star_metric, sup_lt_iff, lt_add_iff_pos_left, zero_lt_one, true_and]
    apply (@star_metric_repeat_first _ r n)

theorem EREa.star_metric_star :
  star_metric (repeat_cat r m) < star_metric (r *⚓) := by
   simp only [star_metric]; apply Prod.Lex.left
   apply star_metric_repeat_first

theorem star_metric_neg :
  star_metric r < (star_metric (~⚓ r)) := by
  simp only [star_metric]
  apply Prod.Lex.right _ (by simp [lt_add_iff_pos_left])

theorem star_metric_interL :
  star_metric l < (star_metric (l ⋒⚓ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . by_cases h : ((star_metric l).fst = (star_metric r).fst)
    . rewrite[←h]; exact Prod.Lex.right _ (by linarith)
    . simp only at h
      exact Prod.Lex.left _ _ (Nat.lt_of_le_of_ne (by linarith) h)
  . exact Prod.Lex.right _ (by linarith)

theorem star_metric_interR :
  star_metric r < (star_metric (l ⋒⚓ r)) := by
  simp only [star_metric, ge_iff_le]
  unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe; simp only
  split
  . exact Prod.Lex.right _ (by linarith)
  . exact Prod.Lex.left _ _ (by linarith)

theorem EREa.star_metric_Star :
  star_metric r < (star_metric (r *⚓)) := by
  simp only [star_metric]
  apply Prod.Lex.left _ _ (by simp_all only [lt_add_iff_pos_left, zero_lt_one])

@[simp]
theorem sizeOf_reverse_ERE (r : EREa α) :
  r.sizeOf = (r.reverse).sizeOf :=
  match r with
  | ε           => rfl
  | EREa.Pred _ => rfl
  | l ⋓⚓ r      => by
    simp only [EREa.sizeOf, sizeOf_reverse_ERE l, sizeOf_reverse_ERE r]
  | l ⋒⚓ r      => by
    simp only [EREa.sizeOf, sizeOf_reverse_ERE l, sizeOf_reverse_ERE r]
  | l ⬝⚓ r      => by
    simp only [EREa.sizeOf, sizeOf_reverse_ERE l, sizeOf_reverse_ERE r]
    linarith
  | r *⚓        => by
    simp only [EREa.sizeOf, sizeOf_reverse_ERE r]
  | ~⚓ r        => by simp only [EREa.sizeOf, sizeOf_reverse_ERE r]
  | StartAnchor => by rfl
  | EndAnchor   => by rfl

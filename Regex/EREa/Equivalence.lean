import Regex.EREa.Derivatives

/-!
# Main equivalence theorem

Contains the proof that the classical and symbolic definitions of derivative are equivalent.
-/

open EREa TTerm

variable {α σ : Type}

theorem null_nullable_empty (r : EREa α) :
  null r ([],([] : List σ)) ↔ nullable r .Empty :=
  match r with
  | ε       => by simp only [null, nullable, NullState.true]
  | Pred _  => by
    simp only [null, Bool.false_eq_true, nullable, NullState.false]
  | l ⋓⚓ r => by
    simp only [null, Bool.or_eq_true, nullable, NullState.or]
    rw[null_nullable_empty r, null_nullable_empty l]
  | l ⋒⚓ r => by
    simp only [null, Bool.and_eq_true, nullable, NullState.and]
    rw[null_nullable_empty r, null_nullable_empty l]
  | l ⬝⚓ r => by
    simp only [null, Bool.and_eq_true, nullable, NullState.and]
    rw[null_nullable_empty r, null_nullable_empty l]
  | r*⚓    => by simp only [null, nullable, NullState.true]
  | ~⚓ r   => by
    simp only [null, Bool.not_eq_eq_eq_not, Bool.not_true, nullable, NullState.not, Bool.coe_false_iff_false, Bool.not_not]
    exact Bool.coe_iff_coe.mp (null_nullable_empty r)
  | StartAnchor => by simp only [null, nullable, NullState.start_anchor]
  | EndAnchor   => by simp only [null, nullable, NullState.Final_anchor]

theorem null_nullable_init_loc (r : EREa α) {y : σ}:
  null r ([],y::ys) ↔ nullable r .Initial :=
  match r with
  | ε => by simp only [null, nullable, NullState.true]
  | Pred _ => by simp only [null, Bool.false_eq_true, nullable, NullState.false]
  | l ⋓⚓ r => by
    simp only [null, Bool.or_eq_true, null_nullable_init_loc l, null_nullable_init_loc r, nullable, NullState.or]
  | l ⋒⚓ r => by
    simp only [null, Bool.and_eq_true, null_nullable_init_loc l, null_nullable_init_loc r, nullable, NullState.and]
  | l ⬝⚓ r => by
    simp only [null, Bool.and_eq_true, null_nullable_init_loc l, null_nullable_init_loc r, nullable, NullState.and]
  | r*⚓ => by simp only [null, nullable, NullState.true]
  | ~⚓ r => by
    simp only [null, Bool.not_eq_eq_eq_not, Bool.not_true, nullable, NullState.not, Bool.coe_false_iff_false, Bool.not_not]
    have ih := null_nullable_init_loc r (ys:=ys) (y:=y)
    exact Bool.coe_iff_coe.mp ih
  | StartAnchor => by simp only [null, nullable, NullState.start_anchor]
  | EndAnchor => by simp only [null, Bool.false_eq_true, nullable, NullState.Final_anchor]

theorem null_helper1 [ne : Nonempty σ] (r : EREa α) :
  nullable r .Initial →
  ∃ (y : σ), ∃ (ys : List σ), null r ([],y::ys) := by
  have := fun (y : σ) ys => null_nullable_init_loc r (y:=y) (ys:=ys)
  intro h
  rw[h] at this; simp only [iff_true] at this
  simp_all only [exists_const]

theorem null_nullable_fin_loc (r : EREa α) :
  null r (x :: xs, []) = nullable r .Final :=
  match r with
  | ε => by simp only [null, nullable, NullState.true]
  | Pred _ => by simp only [null, nullable, NullState.false]
  | l ⋓⚓ r => by
    simp only [null, null_nullable_fin_loc l, null_nullable_fin_loc r, nullable, NullState.or]
  | l ⋒⚓ r => by
    simp only [null, null_nullable_fin_loc l, null_nullable_fin_loc r, nullable, NullState.and]
  | l ⬝⚓ r => by
    simp only [null, null_nullable_fin_loc l, null_nullable_fin_loc r, nullable, NullState.and]
  | r*⚓ => by simp only [null, nullable, NullState.true]
  | ~⚓ r => by simp only [null, null_nullable_fin_loc r, nullable, NullState.not]
  | StartAnchor => by simp only [null, nullable, NullState.start_anchor]
  | EndAnchor => by simp only [null, nullable, NullState.Final_anchor]

theorem null_nullable_noninit_loc (r : EREa α) :
  null r (x :: xs, y :: ys) = nullable r .Centre :=
  match r with
  | ε => by simp only [null, nullable, NullState.true]
  | Pred _ => by simp only [null, nullable, NullState.false]
  | l ⋓⚓ r => by
    simp only [null, null_nullable_noninit_loc l, null_nullable_noninit_loc r, nullable, NullState.or]
  | l ⋒⚓ r => by
    simp only [null, null_nullable_noninit_loc l, null_nullable_noninit_loc r, nullable, NullState.and]
  | l ⬝⚓ r => by
    simp only [null, null_nullable_noninit_loc l, null_nullable_noninit_loc r, nullable, NullState.and]
  | r*⚓ => by simp only [null, nullable, NullState.true]
  | ~⚓ r => by simp only [null, null_nullable_noninit_loc r, nullable, NullState.not]
  | StartAnchor => by simp only [null, nullable, NullState.start_anchor]
  | EndAnchor => by simp only [null, nullable, NullState.Final_anchor]

theorem null_helper2 [ne : Nonempty σ] (r : EREa α) :
  nullable r .Centre →
  ∃ (x y : σ) (xs ys : List σ), null r (x::xs,y::ys) := by
  have := fun (x y : σ) xs ys => null_nullable_noninit_loc r (x:=x) (y:=y) (ys:=ys) (xs:=xs)
  intro h
  rw[h] at this
  simp_all only [exists_const]

theorem null_helper3 [ne : Nonempty σ] (r : EREa α) :
  nullable r .Final →
  ∃ (x : σ) (xs : List σ), null r (x::xs,[]) := by
  have := fun (x : σ) xs => null_nullable_fin_loc r (x:=x) (xs:=xs)
  intro h
  rw[h] at this
  simp_all only [exists_const]

theorem derivative_der_equiv_beg [EffectiveBooleanAlgebra α σ] (r : EREa α) {u : List σ} :
  der r ([], a::u) = ((𝜕 r NullState.initial_beg) [a]) :=
  match r with
  | ε => by simp only [der, evaluation]
  | Pred _ => by simp only [der, evaluation]
  | l ⋓⚓ r => by
    simp only [der, derivative_der_equiv_beg l, derivative_der_equiv_beg r, derivative, liftB]
  | l ⋒⚓ r => by
    simp only [der, derivative_der_equiv_beg l, derivative_der_equiv_beg r, derivative, liftB]
  | l ⬝⚓ r => by
    simp only [der, derivative, NullState.any_nullable, NullState.and, NullState.initial_beg,
      Bool.and_true, Bool.and_false, Bool.or_false]
    by_cases g : null l ([], a::u)
    . simp only [g, ↓reduceIte]; rw[derivative_der_equiv_beg l]
      split
      . simp only [liftB, evaluation, Alternation.injEq, true_and]
        rw[derivative_der_equiv_beg r]
      . simp_all only [Bool.not_eq_true, liftB, evaluation]
        rw[null_nullable_init_loc] at g
        simp_all only [Bool.false_eq_true] -- contra
    . simp only [g, Bool.false_eq_true, ↓reduceIte]
      rw[derivative_der_equiv_beg l]
      split
      . simp only [liftB, evaluation, reduceCtorEq]
        rw[null_nullable_init_loc] at g; simp_all only [not_true_eq_false] -- contra
      . simp_all only [Bool.not_eq_true, liftB, evaluation]
  | r*⚓ => by
    simp only [der, derivative_der_equiv_beg r, derivative, liftB, evaluation]
  | ~⚓ r => by
    simp only [der, derivative_der_equiv_beg r, derivative, liftU]
  | StartAnchor => by simp only [der, evaluation]
  | EndAnchor => by simp only [der, evaluation]

theorem derivative_der_equiv_centre [EffectiveBooleanAlgebra α σ] (r : EREa α) {u xs : List σ} :
  der r (x::xs, a::u) = ((𝜕 r NullState.initial_centre) [a]) :=
  match r with
  | ε => by simp only [der, evaluation]
  | Pred _ => by simp only [der, evaluation]
  | l ⋓⚓ r => by
    simp only [der, derivative_der_equiv_centre l, derivative_der_equiv_centre r, derivative, liftB]
  | l ⋒⚓ r => by
    simp only [der, derivative_der_equiv_centre l, derivative_der_equiv_centre r, derivative, liftB]
  | l ⬝⚓ r => by
    simp only [der, derivative, NullState.any_nullable, NullState.and, NullState.initial_centre,
      Bool.and_false, Bool.and_true, Bool.false_or, Bool.or_false]
    by_cases g : null l (x::xs, a::u)
    . simp only [g, ↓reduceIte]; rw[derivative_der_equiv_centre l]
      split
      . simp only [liftB, evaluation, Alternation.injEq, true_and]
        rw[derivative_der_equiv_centre r]
      . simp_all only [Bool.not_eq_true, liftB, evaluation]
        rw[null_nullable_noninit_loc] at g
        simp_all only [Bool.false_eq_true] -- contra
    . simp only [g, Bool.false_eq_true, ↓reduceIte]
      rw[derivative_der_equiv_centre l]
      split
      . simp only [liftB, evaluation, reduceCtorEq]
        rw[null_nullable_noninit_loc] at g
        simp_all only [not_true_eq_false] -- contra
      . simp_all only [Bool.not_eq_true, liftB, evaluation]
  | r*⚓ => by
    simp only [der, derivative_der_equiv_centre r, derivative, liftB, evaluation]
  | ~⚓ r => by
    simp only [der, derivative_der_equiv_centre r, derivative, liftU]
  | StartAnchor => by simp only [der, evaluation]
  | EndAnchor => by simp only [der, evaluation]

theorem derives_equiv [EffectiveBooleanAlgebra α σ] (sp : Span σ) (r : EREa α) :
  derives sp r ↔ derives_symbolic sp r :=
  match sp with
  | ⟨s, [], v⟩ => by
    match s, v with
    | [], []       => simp only [derives, Span.beg, Span.left, Span.match, Span.right,
      List.append_nil, null_nullable_empty, derives_symbolic]
    | [], y::ys    => simp only [derives, Span.beg, Span.left, Span.match, Span.right,
      List.nil_append, null_nullable_init_loc, derives_symbolic]
    | x::xs, []    => simp only [derives, Span.beg, Span.left, Span.match, Span.right,
      List.append_nil, null_nullable_fin_loc, derives_symbolic]
    | x::xs, y::ys => simp only [derives, Span.beg, Span.left, Span.match, Span.right,
      List.nil_append, null_nullable_noninit_loc, derives_symbolic]
  | ⟨s, a::u, v⟩ =>
    match s with
    | [] => by
      simp only [derives, Span.beg, Span.left, Span.match, Span.right, List.cons_append,
        derives_symbolic, ← derivative_der_equiv_beg (u := u ++ v), Bool.coe_iff_coe]
      have ih := derives_equiv ⟨[a], u, v⟩ (der r ([], a :: (u ++ v)))
      simp only [Bool.coe_iff_coe] at ih; exact ih
    | y::ys => by
      simp only [derives, Span.beg, Span.left, Span.match, Span.right, List.cons_append,
        derives_symbolic, Bool.coe_iff_coe]
      have ih := derives_equiv ⟨a::y::ys, u, v⟩ (der r (y::ys, a :: (u ++ v)))
      rw[←derivative_der_equiv_centre (u:=u++v)]
      simp only [Bool.coe_iff_coe] at ih; exact ih
termination_by sp.2.1

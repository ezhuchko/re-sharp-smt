import Regex.EREa.Semantics
import Regex.EREa.Equivalence

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List TTerm EREa

/-!
# Main correctness theorem

Contains each lemma required to show that `models` and `derives` are equivalent,
along with the main correctness proof.
-/

theorem equivalenceNull (r : EREa α) {s v : List σ} :
  null r (s, v) = true ↔ (s, [], v) ⊫⚓ r :=
  match r with
  | ε => by
    simp only [null, models, Span.match, length_nil]
  | Pred p => by
    simp only [null, Bool.false_eq_true, models, Span.match, length_nil, zero_ne_one,
      Span.match_head?, Option.any_none, and_self]
  | l ⋓⚓ r => by
    simp only [null, Bool.or_eq_true, models]
    rw[←equivalenceNull r,←equivalenceNull l]
  | l ⋒⚓ r => by
    simp only [null, Bool.and_eq_true, models]
    rw[←equivalenceNull r,←equivalenceNull l]
  | l ⬝⚓ r => by
    simp only [null, Bool.and_eq_true, models, Span.left, Span.right, Span.match, append_eq_nil]
    apply Iff.intro
    . intro ⟨h1,h2⟩; rw[equivalenceNull l] at h1; rw[equivalenceNull r] at h2
      exact ⟨[],[],h1,h2,rfl,rfl⟩
    . intro ⟨xs,ys,h1,h2,eq1,eq2⟩; subst eq1 eq2
      rw[←equivalenceNull l] at h1; rw[←equivalenceNull r] at h2
      exact ⟨h1,h2⟩
  | r *⚓ => by
    simp only [null, models, true_iff]; exists 0
    simp only [repeat_cat, models, Span.match, length_nil]
  | ~⚓ r => by
    have ih := equivalenceNull r (s:=s) (v:=v)
    simp only [null, Bool.not_eq_eq_eq_not, Bool.not_true, models]
    erw[←ih]; exact Bool.eq_false_iff
  | StartAnchor => by
    match s with
    | [] => simp only [null, models, Span.match, length_nil, and_self]
    | .cons _ _ => simp only [null, Bool.false_eq_true, models, Span.match, length_nil, length_cons,
      AddLeftCancelMonoid.add_eq_zero, length_eq_zero, one_ne_zero, and_false]
  | EndAnchor => by
    match v with
    | [] => simp only [null, models, Span.match, length_nil, and_self]
    | .cons _ _ => simp only [null, Bool.false_eq_true, models, Span.match, length_nil, length_cons,
      AddLeftCancelMonoid.add_eq_zero, length_eq_zero, one_ne_zero, and_false]

theorem star_repeat_cat {r : EREa α} (h : (a :: s, xs, v) ⊫⚓ r⁽m⁾⚓.der (s, a :: (xs ++ v))) :
  (a :: s, xs, v) ⊫⚓ r*⚓.der (s, a :: (xs ++ v)) :=
  match m with
  | 0 => False.elim (bot_isFalse h)
  | .succ m => by
    by_cases g : r.null (s, a :: (xs ++ v)) = true
    . simp only [der, g, ↓reduceIte, models] at h
      match h with
      | Or.inl ⟨as,bs,h1,h2,eq⟩ =>
        simp only [der, models]
        exact ⟨as,bs,h1,⟨m,h2⟩,eq⟩
      | Or.inr h1 => apply star_repeat_cat h1
    . simp only [der, g, Bool.false_eq_true, ↓reduceIte, models] at h
      let ⟨as,bs,h1,h2,eq⟩ := h
      simp only [der, models]
      exact ⟨as,bs,h1,⟨⟨m,h2⟩,eq⟩⟩

theorem equivalenceDer {r : EREa α} :
  (s,a::xs,v) ⊫⚓ r ↔ (a::s,xs,v) ⊫⚓ (r.der (s,a::(xs++v))) :=
  match r with
  | ε => by
    simp only [models, Span.match, length_cons, AddLeftCancelMonoid.add_eq_zero, length_eq_zero,
      one_ne_zero, and_false, der, bot_isFalse]
  | Pred p => by
    simp only [models, Span.match, length_cons, add_left_eq_self, length_eq_zero, Span.match_head?,
      Option.any_some, der]
    by_cases h : denote p a
    . simp only [h, and_true, ↓reduceIte, models, Span.match, length_eq_zero]
    . simp only [h, Bool.false_eq_true, and_false, ↓reduceIte, bot_isFalse]
  | l ⋓⚓ r => by
    simp only [models,evaluation,derivative]
    have : star_metric l < star_metric (l ⋓⚓ r) := star_metric_altL
    have : star_metric r < star_metric (l ⋓⚓ r) := star_metric_altR
    rw[equivalenceDer (r:=l),equivalenceDer (r:=r)] -- inductive hypothesis
    simp only [der, models]
  | l ⋒⚓ r => by
    simp only [models,evaluation,derivative]
    have : star_metric l < star_metric (l ⋒⚓ r) := star_metric_interL
    have : star_metric r < star_metric (l ⋒⚓ r) := star_metric_interR
    rw[equivalenceDer (r:=l),equivalenceDer (r:=r)] -- inductive hypothesis
    simp only [der, models]
  | r *⚓ => by
    simp only [models]
    apply Iff.intro
    . intro ⟨m,g⟩
      have : r⁽m⁾⚓.star_metric < r*⚓.star_metric := star_metric_star
      apply star_repeat_cat (equivalenceDer.mp g) -- inductive hypothesis
    . simp only [der,models, Span.left, Span.right, Span.match]
      intro ⟨u1,u2,g1,⟨m,g2⟩,g3⟩
      exists m.succ
      have : r.star_metric < r*⚓.star_metric := star_metric_Star
      match u1 with
      | [] =>
        simp only [repeat_cat, models]
        simp only [nil_append] at g3; subst g3
        exists [a]; exists u2; rw[equivalenceDer (r:=r)] -- inductive hypothesis
        simp only [nil_append, reverse_cons, reverse_nil, singleton_append, and_true]
        exists g1
      | u::us =>
        simp; simp at g3; subst g3
        exists (a::u::us); exists u2; rw[equivalenceDer (r:=r)] -- inductive hypothesis
        simp only [cons_append, reverse_cons, append_assoc, singleton_append, and_true]
        simp_all
  | ~⚓ r => by
    simp [models,evaluation,derivative]
    have : (star_metric r) < (star_metric (~⚓ r)) := star_metric_neg
    rw[equivalenceDer] -- inductive hypothesis
  | l ⬝⚓ r => by
    have : (star_metric l) < (star_metric (l ⬝⚓ r)) := star_metric_catL
    have : (star_metric r) < (star_metric (l ⬝⚓ r)) := star_metric_catR
    by_cases g : null l (s, a :: (xs ++ v))
    . simp only [models, Span.left, Span.right, Span.match, der, g, ↓reduceIte]
      apply Iff.intro
      . intro ⟨u,hu,⟨x,hv,hv1⟩⟩
        match u with
        | [] =>
          simp only [←equivalenceDer (r := r)] -- inductive hypothesis
          subst hv1
          apply Or.inr hv
        | .cons rr rs =>
          simp only [cons_append, cons.injEq] at hv1
          let ⟨k1,k2⟩ := hv1; subst k1
          apply Or.inl
          simp only [true_and] at hv1; subst hv1; exists rs; exists hu
          simp only [append_assoc, ←equivalenceDer (r := l), and_true] -- inductive hypothesis
          exact ⟨x,by simp only [reverse_cons, append_assoc, singleton_append] at hv; exact hv⟩
      . intro h1
        match h1 with
        | Or.inl ⟨u,hu,⟨x,hv,hv1⟩⟩ =>
          subst hv1
          simp only [append_assoc] at x hv
          rw[←equivalenceDer (s:=s) (a:=a) (r:=l) (xs:=u) (v:=hu++v)] at x -- inductive hypothesis
          exact ⟨a::u,hu,⟨x,by simp; exact hv,rfl⟩⟩
        | Or.inr h3 =>
          exact ⟨[],a::xs,⟨by rw[equivalenceNull] at g; exact g,
                 by simp only [reverse_nil, nil_append]; rw[equivalenceDer (r:=r)]; exact h3,rfl⟩⟩ -- inductive hypothesis
    . simp[g,models]
      apply Iff.intro
      . intro ⟨h1,h2,⟨h3,h4,h5⟩⟩
        match h1 with
        | [] =>
          simp only [nil_append] at h5
          subst h5; rw[←equivalenceNull] at h3
          contradiction
        | .cons rr rs =>
          simp only [cons_append, cons.injEq] at h5
          let ⟨k1,k2⟩ := h5; subst k1 k2
          rw[equivalenceNull] at g
          exact ⟨rs,h2,by simp only [append_assoc, ←equivalenceDer (r := l)]; exact h3, -- inductive hypothesis
                 by simp only [and_true]; simp only [reverse_cons, append_assoc, singleton_append] at h4; exact h4⟩
      . intro ⟨h1,h2,⟨h3,h4,h5⟩⟩; subst h5
        simp[←equivalenceDer (r:=l)] at h3 -- inductive hypothesis
        exact ⟨a::h1,h2,⟨h3,by simp only [reverse_cons, append_assoc, singleton_append]; exact h4, rfl⟩⟩
  | StartAnchor => by
    simp; intro g
    match xs with
    | [] => simp only [length_nil, zero_ne_one] at g
    | x::xs => simp only [Option.any_some, EffectiveBooleanAlgebra.denote_bot]
  | EndAnchor => by
    simp; intro g
    match xs with
    | [] => simp only [length_nil, zero_ne_one] at g
    | x::xs => simp only [Option.any_some, EffectiveBooleanAlgebra.denote_bot]
termination_by star_metric r
decreasing_by
  repeat { assumption }

theorem EREa.correctness {r : EREa α} {sp : Span σ} :
  derives sp r ↔ sp ⊫⚓ r :=
  match sp with
  | (s,[],v) => by
    simp only [derives, nil_append]
    apply equivalenceNull r
  | (s,a::xs,v) => by
    simp only [derives, cons_append]
    rw[equivalenceDer]
    apply correctness -- inductive hypothesis
termination_by sp.2.1

import Regex.EREwLookarounds.Models
import Regex.RESharp.Semantics
import Regex.EREwLookarounds.Rewrites
import Regex.RESharp.Metrics

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Conversions between `EREa`, `RESharp` and `RE`

Contains the conversion functions between the different classes of regular expressions, as well as the proofs that the semantics are preserved when doing the conversions.
-/

open EREa RESharp RE List

/-- Converts an `EREa` regular expression into an `RE` regular expression.
    This function structurally translates each component, ensuring that anchors
    are mapped to the corresponding constructors in `RE`. -/
@[simp]
def EREa_to_RE (r : EREa α) : RE α :=
  match r with
  | .ε      => .ε
  | .Pred p => .Pred p
  | l ⋓⚓ r => EREa_to_RE l ⋓ EREa_to_RE r
  | l ⋒⚓ r => EREa_to_RE l ⋒ EREa_to_RE r
  | l ⬝⚓ r => EREa_to_RE l ⬝ EREa_to_RE r
  | r*⚓    => (EREa_to_RE r)*
  | ~⚓ r   => ~ (EREa_to_RE r)
  | EndAnchor   => endAnchor
  | StartAnchor => startAnchor

/-- Converts an `RESharp` regular expression into an `RE` regular expression.
    This extends `EREa_to_RE` by additionally translating lookaheads and lookbehinds.
    The translation ensures that restricted lookarounds in `RESharp` are properly
    represented in `RE`. -/
@[simp]
def RESharp_to_RE (r : RESharp α) : RE α :=
  match r with
  | .Ere r => EREa_to_RE r
  | .Lookbehind l r => (?<= (EREa_to_RE l)) ⬝ RESharp_to_RE r
  | .Lookahead l r  => RESharp_to_RE l ⬝ (?= (EREa_to_RE r))
  | NLookbehind l r => (?<! (EREa_to_RE l)) ⬝ RESharp_to_RE r
  | NLookahead l r  => RESharp_to_RE l ⬝ (?! (EREa_to_RE r))
  | Alt l r    => RESharp_to_RE l ⋓ RESharp_to_RE r
  | .Inter l r => RESharp_to_RE l ⋒ RESharp_to_RE r
  | Compl r    => ~ (RESharp_to_RE r)

/-- Relates the `repeat_cat` operator between `EREa` and `RE`. -/
theorem iterated_EREa_to_RE {r : EREa α} :
  EREa_to_RE (r⁽m⁾⚓) = EREa_to_RE r⁽m⁾ :=
  match m with
  | 0 => by simp only [EREa_to_RE, RE.repeat_cat]
  | .succ m => by
    simp only [EREa_to_RE, RE.repeat_cat, RE.Concatenation.injEq, true_and]
    exact iterated_EREa_to_RE

/-- Proves that an `EREa` expression, when translated into `RE`,
    preserves its semantics. -/
theorem EREa_in_RE {sp : Span σ} {r : EREa α}  :
  sp ⊫ EREa_to_RE r ↔ sp ⊫ᵣ r := by
  let ⟨s,u,v⟩ := sp
  match r with
  | .ε => simp only [EREa_to_RE, RE.models, Span.match, length_eq_zero, EREa.models]
  | .Pred p => simp only [EREa_to_RE, RE.models, Span.match, Span.match_head?, EREa.models]
  | l ⋓⚓ r =>
    have : star_metric l < star_metric (l ⋓⚓ r) := star_metric_altL
    have : star_metric r < star_metric (l ⋓⚓ r) := star_metric_altR
    simp only [EREa_to_RE, RE.models, EREa.models]
    apply or_congr EREa_in_RE EREa_in_RE
  | l ⋒⚓ r =>
    have : star_metric l < star_metric (l ⋒⚓ r) := star_metric_interL
    have : star_metric r < star_metric (l ⋒⚓ r) := star_metric_interR
    simp only [EREa_to_RE, RE.models, EREa.models]
    apply and_congr EREa_in_RE EREa_in_RE
  | l ⬝⚓ r =>
    have : (star_metric l) < (star_metric (l ⬝⚓ r)) := star_metric_catL
    have : (star_metric r) < (star_metric (l ⬝⚓ r)) := star_metric_catR
    simp only [EREa_to_RE, RE.models, Span.left, Span.right, Span.match, EREa.models]
    apply exists₂_congr (λ _ _ => and_congr EREa_in_RE (and_congr_left_iff.mpr (λ _ => EREa_in_RE)))
  | r *⚓ =>
    simp only [EREa_to_RE, RE.models, EREa.models]
    simp_rw [←iterated_EREa_to_RE]
    refine exists_congr fun m => ?_
    have : star_metric (r ⁽ m ⁾⚓) < star_metric (r *⚓) := star_metric_star
    simp_rw [EREa_in_RE (r:=(r⁽m⁾⚓))]
  | ~⚓ r =>
    simp only [EREa_to_RE, RE.models, EREa.models]
    have : (star_metric r) < (star_metric (~⚓ r)) := star_metric_neg
    simp_rw[EREa_in_RE (r:=r)]
  | EndAnchor =>
    simp only [EREa_to_RE, models_NegLookahead_Top, Span.match, length_eq_zero,
    Span.right, EREa.models]
  | StartAnchor =>
    simp only [EREa_to_RE, models_startAnchor, Span.match, length_eq_zero, Span.left, EREa.models]
  termination_by star_metric r
  decreasing_by
    repeat { assumption }

/-- Proves that an `RESharp α` expression, when translated into `RE α`,
    preserves its semantics. -/
theorem RESharp_in_RE {sp : Span σ} {r : RESharp α} :
  sp ⊫ RESharp_to_RE r ↔ sp ⊫ᵣ r :=
  match r with
  | .Ere r => by
    have : star_metric r < star_metric (.Ere r) := star_metric_ere
    simp only [RESharp_to_RE, RESharp.models]
    apply EREa_in_RE
  | .Lookbehind l r => by
    have : r.star_metric < (Lookbehind l r).star_metric := star_metric_lookbehind
    simp only [RESharp_to_RE, RE.models, Span.left, Span.right, Span.match, length_eq_zero,
      Span.reverse, Span.beg, Prod.mk.injEq, RESharp.models, reverse_nil, nil_append]
    simp_rw [RESharp_in_RE (r:=r), EREa_in_RE] -- inductive hypothesis
    exact ⟨λ ⟨u1,u2,⟨h1,h2,h3⟩,h4,h5⟩ =>
            by subst h1; simp only [reverse_nil, nil_append] at h4 h5
               subst h5; exact ⟨⟨h2,h3⟩,h4⟩,
           λ ⟨spM,h⟩ => ⟨[],sp.2.1,⟨rfl,spM⟩,h,rfl⟩⟩
  | .Lookahead l r  => by
    simp only [RESharp_to_RE, RE.models, Span.left, Span.right, Span.match, length_eq_zero,
      Span.beg, Prod.mk.injEq, RESharp.models, nil_append]
    have : l.star_metric < (Lookahead l r).star_metric := star_metric_lookahead
    simp_rw [RESharp_in_RE (r:=l), EREa_in_RE] -- inductive hypothesis
    exact ⟨λ ⟨u1,u2,h1,⟨h2,⟨spM,h3,h3a,h3b⟩⟩,h4⟩ =>
            by subst h2; simp at h4 h1; subst h4; exact ⟨h1,⟨spM,h3,h3a,h3b⟩⟩,
           λ ⟨spM,h⟩ => ⟨sp.2.1,[],spM,⟨rfl,h⟩,by simp⟩⟩
  | NLookbehind l r => by
    have : r.star_metric < (NLookbehind l r).star_metric := star_metric_nlookbehind
    simp only [RESharp_to_RE, RE.models, Span.left, Span.right, Span.match, length_eq_zero,
      Span.reverse, Span.beg, Prod.mk.injEq, not_exists, not_and, RESharp.models, reverse_nil,
      nil_append]
    simp_rw[RESharp_in_RE (r:=r), EREa_in_RE] -- inductive hypothesis
    exact ⟨λ ⟨u1,u2,⟨h1,h2⟩,h4,h5⟩ =>
            by subst h1; simp only [nil_append] at h5; subst h5
               simp only [reverse_nil, nil_append, Prod.mk.eta] at h4
               exact ⟨λ ⟨s,u,v⟩ h1 h2 h3 => by
                        simp only at h1 h2 h3; subst h2
                        have := h2 (Span.reverse (v, u.reverse, sp.2.1 ++ sp.2.2))
                        simp only [Span.reverse, reverse_reverse, reverse_nil, nil_append,
                          forall_const] at this
                        have t := this h1 h3
                        contradiction,h4⟩,
           λ ⟨spM,h⟩ => ⟨[],sp.2.1,⟨rfl,spM⟩,h,rfl⟩⟩
  | NLookahead l r  => by
    simp only [RESharp_to_RE, RE.models, Span.left, Span.right, Span.match, length_eq_zero,
      Span.beg, Prod.mk.injEq, not_exists, not_and, RESharp.models, nil_append]
    have : l.star_metric < (NLookahead l r).star_metric := star_metric_nlookahead
    simp_rw[RESharp_in_RE (r:=l), EREa_in_RE] -- inductive hypothesis
    exact ⟨λ ⟨u1,u2,h1,⟨h2,h3⟩,h4⟩ =>
            by subst h2; simp at h4 h1; subst h4
               exact ⟨h1,λ ⟨x1,x2,x3⟩ y z z1 => by
                           simp at z z1; subst z
                           have := h3 (sp.2.1.reverse ++ sp.1, x2, x3) y rfl
                           simp only [nil_append] at this
                           contradiction⟩,
           λ ⟨spM,h⟩ => ⟨sp.2.1,[],spM,
                         ⟨rfl,λ ⟨x1,x2,x3⟩ y z z1 => by
                           simp at z1; subst z
                           have := h (sp.2.1.reverse ++ sp.1, x2, x3) y rfl
                           simp only at this
                           contradiction⟩,
                         by simp⟩⟩
  | Alt l r    => by
    simp
    have : l.star_metric < (l.Alt r).star_metric := star_metric_altL
    have : r.star_metric < (l.Alt r).star_metric := star_metric_altR
    apply or_congr RESharp_in_RE RESharp_in_RE -- inductive hypothesis
  | .Inter l r => by
    simp
    have : l.star_metric < (l.Inter r).star_metric := star_metric_interL
    have : r.star_metric < (l.Inter r).star_metric := star_metric_interR
    apply and_congr RESharp_in_RE RESharp_in_RE -- inductive hypothesis
  | Compl r    => by
    simp only [RESharp_to_RE, RE.models, RESharp.models]
    have : r.star_metric < r.Compl.star_metric := star_metric_neg
    refine not_congr RESharp_in_RE -- inductive hypothesis
  termination_by star_metric r
  decreasing_by
    repeat { assumption }

import Regex.EREa.Derivatives
import Regex.EREa.Metrics

/-!
# Match semantics for EREa

Contains the specification of the matching relation, which follows the same approach
of language-based matching.
The semantics is provided directly as an inductive predicate, in Prop.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open List TTerm EREa

/-- The match semantics of `EREa` are formalised using the models relation. -/
@[simp]
def EREa.models (sp : Span σ) (R : EREa α) : Prop :=
  match R with
  | ε      => sp.match.length = 0
  | Pred φ => sp.match.length = 1 ∧ sp.match_head?.any (denote φ)
  | l ⬝⚓ r  =>
      ∃ u₁ u₂,
          have : (star_metric l) < (star_metric (l ⬝⚓ r)) := star_metric_catL
          have : (star_metric r) < (star_metric (l ⬝⚓ r)) := star_metric_catR
          models ⟨sp.left, u₁, u₂ ++ sp.right⟩ l
        ∧ models ⟨u₁.reverse ++ sp.left, u₂, sp.right⟩ r
        ∧ u₁ ++ u₂ = sp.match
  | l ⋓⚓ r  =>
      have : star_metric l < star_metric (l ⋓⚓ r) := star_metric_altL
      have : star_metric r < star_metric (l ⋓⚓ r) := star_metric_altR
      models sp l ∨ models sp r
  | l ⋒⚓ r  =>
      have : star_metric l < star_metric (l ⋒⚓ r) := star_metric_interL
      have : star_metric r < star_metric (l ⋒⚓ r) := star_metric_interR
    models sp l ∧ models sp r
  | r *⚓    =>
      ∃ (m : ℕ),
      have : star_metric (r ⁽ m ⁾⚓) < star_metric (r *⚓) := star_metric_star
      models sp (r ⁽ m ⁾⚓)
  | ~⚓ r    =>
      have : (star_metric r) < (star_metric (~⚓ r)) := star_metric_neg
      ¬ models sp r
  | StartAnchor   => sp.match.length = 0 ∧ sp.1.length = 0
  | EndAnchor     => sp.match.length = 0 ∧ sp.2.2.length = 0
termination_by
  star_metric R
decreasing_by
  repeat { assumption }
notation:52 lhs:53 " ⊫⚓ " rhs:53 => models lhs rhs

@[simp]
theorem EREa.bot_isFalse :
  ¬ sp ⊫⚓ Pred (⊥ : α) := by
  match sp with
  | (s,[],v) => simp_all
  | (s,u::us,v) => simp_all

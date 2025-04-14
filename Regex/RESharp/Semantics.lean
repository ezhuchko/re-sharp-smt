import Regex.RESharp.RESharp
import Regex.EREa.Semantics

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Match semantics for RESharp

Contains the specification of the matching relation, which follows the same approach
of language-based matching.
The semantics is provided directly as an inductive predicate, in Prop.
-/

open List EREa RESharp

/-- The match semantics of RESharp are formalised using the models relation. -/
@[simp]
def RESharp.models (sp : Span σ) (R : RESharp α) : Prop :=
  match R with
  | .Ere r         => sp ⊫⚓ r
  | Lookbehind l r =>
      (∃ (spM : Span σ), spM.reverse ⊫⚓ l ∧ spM.beg = (Span.reverse (sp.1, [], sp.2.1 ++ sp.2.2)).beg)
    ∧ models sp r
  | Lookahead l r  =>
      models sp l
    ∧ (∃ spM, spM ⊫⚓ r ∧ spM.beg = Span.beg (sp.2.1.reverse ++ sp.1, [], sp.2.2))
  | NLookbehind l r =>
      ¬ (∃ (spM : Span σ), spM.reverse ⊫⚓ l ∧ spM.beg = (Span.reverse (sp.1, [], sp.2.1 ++ sp.2.2)).beg)
    ∧ models sp r
  | NLookahead l r  =>
      models sp l
    ∧ ¬ (∃ spM, spM ⊫⚓ r ∧ spM.beg = Span.beg (sp.2.1.reverse ++ sp.1, [], sp.2.2))
  | Alt l r    => models sp l ∨ models sp r
  | .Inter l r => models sp l ∧ models sp r
  | Compl r    => ¬ models sp r
infix:30 " ⊫ᵣ " => models

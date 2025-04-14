import Regex.RESharp.LookaroundNormalForm

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

open BA EREa RESharp List

instance : ToString (BA Char) where
  toString c := toStringBA c
  where
    toStringBA : BA Char → String
    | atom a => a.repr
    | top => "⊤"
    | bot => "⊥"
    | BA.and a b => toStringBA a ++ " ∧ " ++ toStringBA b
    | BA.or a b => toStringBA a ++ " ∨ " ++ toStringBA b
    | BA.not a => "¬ " ++ toStringBA a

instance : ToString (EREa (BA Char)) where
  toString r := toStringRE r
  where
    toStringRE : EREa (BA Char) → String
    | StartAnchor => "StartAnchor"
    | EndAnchor => "EndAnchor"
    | ε       => "ε"
    | Pred a  => toString a
    | r1 ⋓⚓ r2 => "(" ++ toStringRE r1 ++ " + " ++ toStringRE r2 ++ ")"
    | r1 ⋒⚓ r2 => "(" ++ toStringRE r1 ++ " & " ++ toStringRE r2 ++ ")"
    | r1 ⬝⚓ r2 => "(" ++ toStringRE r1 ++  "⬝" ++ toStringRE r2 ++ ")"
    | ~⚓ r   => "~" ++ toStringRE r
    | r *⚓   => toStringRE r ++ "*"

instance : ToString (RESharp (BA Char)) where
  toString r := toStringRESharp r
  where
    toStringRESharp : RESharp (BA Char) → String
    | Ere r => toString r
    | .Alt l r => "(" ++ toStringRESharp l ++ " ⋓ " ++ toStringRESharp r ++ ")"
    | .Inter l r => "(" ++ toStringRESharp l ++ " ⋒ " ++ toStringRESharp r ++ ")"
    | .Compl r => "~ᵣ" ++ toStringRESharp r
    | .Lookbehind a r => "(" ++ toString a ++ " ⬝lb " ++ toStringRESharp r ++ ")"
    | .NLookbehind a r => "(" ++ toString a ++ " ⬝nlb " ++ toStringRESharp r ++ ")"
    | .Lookahead r a => "(" ++ toStringRESharp r ++ " ⬝la " ++ toString a ++ ")"
    | .NLookahead r a => "(" ++ toStringRESharp r ++ " ⬝nla " ++ toString a ++ ")"

instance : ToString (PiecePosRESharp (BA Char)) where
  toString r := toStringPiecePosRESharp r
  where
    toStringPiecePosRESharp : PiecePosRESharp (BA Char) → String
    | .Ere r => toString r
    | .Lookbehind a r => "(" ++ toString a ++ " ⬝lb_pos " ++ toStringPiecePosRESharp r ++ ")"
    | .Lookahead r a => "(" ++ toStringPiecePosRESharp r ++ " ⬝la_pos " ++ toString a ++ ")"
    | .Inter l r => "(" ++ toStringPiecePosRESharp l ++ " ⋒pos " ++ toStringPiecePosRESharp r ++ ")"

instance [ToString (EREa α)] : ToString (CoreRegex α) where
  toString c :=
    "(" ++ toString c.1 ++ ","
        ++ toString c.2 ++ ","
        ++ toString c.3 ++ ")"

def a : EREa (BA Char) := (Pred (atom 'a'))
def b : EREa (BA Char) := (Pred (atom 'b'))
def c : EREa (BA Char) := (Pred (atom 'c'))

def lhs : RESharp (BA Char) := a ⬝lb .Ere b -- (.Ere $ .pad ⬝⚓ b ⬝⚓ .pad)
def rhs : RESharp (BA Char) := .Ere c -- $ .pad ⬝⚓ c ⬝⚓ .pad

def example1 : RESharp (BA Char) := .Compl (.Ere a)

#eval LNF example1

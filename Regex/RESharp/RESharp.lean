import Regex.EREa.EREa

open EREa

/-- The class of regular expressions `RESharp` which subsumes the class `EREa` and extends it with restricted lookarounds
    of the form `(?<= L) ⬝ R` and `(?<! L) ⬝ R` for lookbehinds and `R ⬝ (?= L)` and `R ⬝ (?! L)` for lookaheads.
    `RESharp` is closed under Alternation, Intersection and Complement. -/
inductive RESharp (α : Type) : Type
 | Ere         : EREa α → RESharp α
 | Lookbehind  : EREa α → RESharp α → RESharp α
 | NLookbehind : EREa α → RESharp α → RESharp α
 | Lookahead   : RESharp α → EREa α → RESharp α
 | NLookahead  : RESharp α → EREa α → RESharp α
 | Alt         : RESharp α → RESharp α → RESharp α
 | Inter       : RESharp α → RESharp α → RESharp α
 | Compl       : RESharp α → RESharp α
open RESharp

/-- `PiecePosRESharp` is a subset of `RESharp` that excludes the complement and
    negated lookarounds. It represents the "positive fragment" of the regular expressions.
    This fragment includes only the basic expressions, positive lookarounds, and intersections. -/
inductive PiecePosRESharp (α : Type) : Type
 | Ere        : EREa α → PiecePosRESharp α
 | Lookbehind : EREa α → PiecePosRESharp α → PiecePosRESharp α
 | Lookahead  : PiecePosRESharp α → EREa α → PiecePosRESharp α
 | Inter      : PiecePosRESharp α → PiecePosRESharp α → PiecePosRESharp α
open PiecePosRESharp

/-- `conv` converts a `PiecePosRESharp` expression into a regular `RESharp` expression.
    This conversion removes the restriction of only positive expressions.
    It is used to map expressions from the positive fragment back to the general `RESharp` type. -/
def conv (r : PiecePosRESharp α) : RESharp α :=
  match r with
  | .Ere r => .Ere r
  | .Lookbehind a r => .Lookbehind a (conv r)
  | .Lookahead r a  => .Lookahead (conv r) a
  | .Inter a b      => .Inter (conv a) (conv b)

prefix:max "~ᵣ"    => RESharp.Compl
infixr:50 " ⬝lb "  => RESharp.Lookbehind
infixr:50 " ⬝la "  => RESharp.Lookahead
infixr:50 " ⬝nlb " => RESharp.NLookbehind
infixr:50 " ⬝nla " => RESharp.NLookahead

infixr:50 " ⬝lb_pos "  => PiecePosRESharp.Lookbehind
infixr:50 " ⬝la_pos "  => PiecePosRESharp.Lookahead

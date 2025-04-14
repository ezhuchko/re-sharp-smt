import Regex.EBA

/-- The class of extended regular expressions (ERE) which includes
    intersection, complement and start/end anchors. -/
inductive EREa (α : Type) where
  | ε                 : EREa α
  | Pred (e : α)      : EREa α
  | Alternation       : EREa α → EREa α → EREa α
  | Intersection      : EREa α → EREa α → EREa α
  | Concatenation     : EREa α → EREa α → EREa α
  | Star              : EREa α → EREa α
  | Negation          : EREa α → EREa α
  | StartAnchor       : EREa α
  | EndAnchor         : EREa α
  deriving Repr, DecidableEq
open EREa

infixr:35 " ⋓⚓ "  => Alternation
infixr:40 " ⋒⚓ "  => Intersection
infixr:50 " ⬝⚓ "  => Concatenation
postfix:max "*⚓"  => Star
prefix:max "~⚓"   => Negation

/-- The notation for ⊤* is pad. -/
def EREa.pad [Top α] : EREa α := (Pred (⊤ : α))*⚓

def nLookahead [Top α] (r : EREa α) : EREa α :=
  ~⚓ (r ⬝⚓ pad) ⬝⚓ EndAnchor

def nLookbehind [Top α] (r : EREa α) : EREa α :=
  StartAnchor ⬝⚓ ~⚓ (pad ⬝⚓ r)

/-- Encoding of Star using bounded loops. -/
@[simp]
def EREa.repeat_cat (R : EREa α) (n : ℕ) : EREa α :=
  match n with
  | 0          => ε
  | Nat.succ n => R ⬝⚓ (repeat_cat R n)

notation f "⁽" n "⁾⚓" => EREa.repeat_cat f n

/-- Reversal function for regular expressions in `EREa`. -/
@[simp]
def EREa.reverse (R : EREa α) : EREa α :=
  match R with
  | ε      => ε
  | Pred φ => Pred φ
  | l ⋓⚓ r  => l.reverse ⋓⚓ r.reverse
  | l ⋒⚓ r  => l.reverse ⋒⚓ r.reverse
  | l ⬝⚓ r  => r.reverse ⬝⚓ l.reverse
  | r *⚓    => r.reverse *⚓
  | ~⚓ r    => ~⚓ r.reverse
  | StartAnchor => EndAnchor
  | EndAnchor   => StartAnchor
open EREa.reverse

/-- Elementary denotation predicates for (Unicode) characters. -/
instance : Denotation Char Char where
  denote a b := a == b

/-- Helper function to convert strings into regexp literals (string as a sequence of characters) -/
def String.toRE (s : String) : EREa (BA Char) :=
  s.toList |>.map (Pred ∘ BA.atom) |>.foldr (· ⬝⚓ ·) ε

/-- Implicit coercion to convert strings to regexp to make them more readable. -/
instance : Coe String (EREa (BA Char)) where
  coe := String.toRE

/-- Helper function to obtain a string as character class. -/
def String.characterClass (s : String) : BA Char :=
  s.toList |>.map .atom |>.foldr .or .bot

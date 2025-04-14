import Regex.TTerm
import Regex.Span
import Regex.EREa.EREa

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Derivatives of EREa

The file contains definition of symbolic (`derivative`) and classical (`der`) derivatives of `EREa`, as well as the corresponding
derivation relations.
-/

open TTerm EREa List Function

/-- A flag to represent where the match occurs. -/
inductive StateKind : Type where
| Initial | Centre | Final | Empty
open StateKind

@[simp]
def NullState : Type := StateKind → Bool

@[simp]
def NullState.or (n1 n2 : NullState) : NullState := λ k => n1 k || n2 k

@[simp]
def NullState.and (n1 n2 : NullState) : NullState := λ k => n1 k && n2 k

@[simp]
def NullState.not (n : NullState) : NullState := λ k => !n k

@[simp]
def NullState.true : NullState := λ _ => Bool.true

@[simp]
def NullState.false : NullState := λ _ => Bool.false

@[simp]
def NullState.null_Initial : NullState :=
  λ k => match k with | Initial => Bool.true | _ => Bool.false

@[simp]
def NullState.null_centre : NullState :=
  λ k => match k with | Centre => Bool.true | _ => Bool.false

@[simp]
def NullState.start_anchor : NullState :=
  λ k => match k with | Initial => Bool.true | .Empty => Bool.true | _ => Bool.false

@[simp]
def NullState.Final_anchor : NullState :=
  λ k => match k with | Final => Bool.true | .Empty => Bool.true | _ => Bool.false

@[simp]
def NullState.any_nullable (n : NullState) : Bool :=
  n Initial || n Centre || n Final || n Empty

@[simp]
def NullState.initial_beg : NullState :=
  λ k => match k with | Initial => Bool.true | _ => Bool.false

@[simp]
def NullState.initial_centre : NullState :=
  λ k => match k with | Centre => Bool.true | _ => Bool.false

@[simp]
def EREa.nullable (r : EREa α) : NullState :=
  match r with
  | ε           => .true
  | EREa.Pred _ => .false
  | l ⋓⚓ r     => .or (nullable l) (nullable r)
  | l ⋒⚓ r     => .and (nullable l) (nullable r)
  | l ⬝⚓ r     => .and (nullable l) (nullable r)
  | _*⚓        => .true
  | ~⚓ r       => .not (nullable r)
  | StartAnchor => .start_anchor
  | EndAnchor   => .Final_anchor

/-- Symbolic definition of derivative which does not take an explicit location as argument. -/
@[simp]
def EREa.derivative (r : EREa α) (null_state : NullState) : TTerm α (EREa α) :=
  match r with
  | ε           => Leaf (Pred ⊥)
  | EREa.Pred b => Node b (Leaf ε) (Leaf (Pred ⊥))
  | l ⋓⚓ r      =>
    lift_binary (· ⋓⚓ ·) (derivative l null_state) (derivative r null_state)
  | l ⋒⚓ r  => lift_binary (· ⋒⚓ ·) (derivative l null_state) (derivative r null_state)
  | l ⬝⚓ r =>
    let s := NullState.and (nullable l) null_state
    if s.any_nullable then
      lift_binary (· ⋓⚓ ·) (lift_binary (· ⬝⚓ ·) (derivative l null_state) (Leaf r))
                          (derivative r null_state)
    else
      lift_binary (· ⬝⚓ ·) (derivative l null_state) (Leaf r)
  | r *⚓ => lift_binary (· ⬝⚓ ·) (derivative r null_state) (Leaf r*⚓)
  | ~⚓ r => lift_unary (~⚓ ·) (derivative r null_state)
  | StartAnchor => Leaf (Pred ⊥)
  | EndAnchor   => Leaf (Pred ⊥)
prefix:max " 𝜕 " => EREa.derivative

/-- Main derivation relation, by induction on the match length. -/
@[simp]
def derives_symbolic (sp : Span σ) (r : EREa α) : Bool :=
  -- the match is empty
  match sp with
  | (s, [], v) =>
    match s, v with
    | [], []     => nullable r Empty  -- the string encoded by sp is empty
    | [], _::_   => nullable r Initial  -- we are at index 0 in the string
    | _::_, []   => nullable r Final    -- we are at index |s| in the string
    | _::_, _::_ => nullable r Centre -- we are in the middle of the string
    -- the match is non-empty
  | ⟨s, a::u, v⟩ =>
    match s with
    | []    => derives_symbolic ⟨a::s, u, v⟩ ((𝜕 r .initial_beg) [a])
    | y::ys => derives_symbolic ⟨a::y::ys, u, v⟩ ((𝜕 r .initial_centre) [a])
termination_by sp.2.1

@[simp]
def EREa.null (r : EREa α) (x : Loc σ) : Bool :=
  match r with
  | ε           => true
  | EREa.Pred _ => false
  | l ⋓⚓ r       => null l x || null r x
  | l ⋒⚓ r       => null l x && null r x
  | l ⬝⚓ r       => null l x && null r x
  | _*⚓          => true
  | ~⚓ r         => !null r x
  | StartAnchor =>
    match x with
     | ([], _)   => true
     | (_::_, _) => false
  | EndAnchor   =>
    match x with
     | (_, [])   => true
     | (_, _::_) => false

/-- Classical definition of derivative which takes an explicit location as an argument. -/
@[simp]
def EREa.der (r : EREa α) (x : Loc σ) : EREa α :=
  match r with
  | ε          => Pred ⊥
  | EREa.Pred p =>
    match x with
     | (_ , [])   => Pred ⊥
     | (_ , a::_) => if denote p a then ε else Pred ⊥
  | l ⋓⚓ r      => der l x ⋓⚓ der r x
  | l ⋒⚓ r      => der l x ⋒⚓ der r x
  | l ⬝⚓ r      =>
    if null l x then der l x ⬝⚓ r ⋓⚓ der r x else der l x ⬝⚓ r
  | r*⚓         => der r x ⬝⚓ r*⚓
  | ~⚓ r        => ~⚓ (der r x)
  | StartAnchor => Pred ⊥
  | EndAnchor   => Pred ⊥

/-- Main derivation relation, by induction on the match length. -/
@[simp]
def EREa.derives (sp : Span σ) (r : EREa α) : Bool :=
  match sp with
  | ⟨_, [], _⟩   => null r sp.beg
  | ⟨s, a::u, v⟩ => derives ⟨a::s, u, v⟩ (der r sp.beg)
termination_by sp.2.1

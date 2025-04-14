import Regex.RESharp.Conversions

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

/-!
# Lookaround Normal Form

This file contains the main correctness theorem for the lookaround normal form.
-/

open EREa RESharp List

/-- The CoreRegex is of the form : `(?<= left) ⬝ regex ⬝ (?= right)`.
    The `left` and `right` are lookbehind and lookahead components, respectively.-/
structure CoreRegex (α : Type) : Type where
  left  : EREa α
  regex : EREa α
  right : EREa α
open CoreRegex

/-- Given an `R : EREa α`, this function lifts it to CoreRegex form i.e. `(?<= ε) ⬝ R ⬝ (?= ε)`. -/
@[simp]
def EREa_to_CoreRegex (R : EREa α) : CoreRegex α where
  -- (?<= ε)
  left := ε
  regex := R
  -- (?= ε)
  right := ε

/-- Each regex `R` is equivalent to the CoreRegex form `(?<=ε) ⬝ R ⬝ (?=ε)`. -/
theorem CoreRegex_equivalence {R : RESharp α} {sp : Span σ} :
  sp ⊫ᵣ R ↔ sp ⊫ᵣ (ε ⬝lb R ⬝la ε) :=
  Iff.trans
  (Iff.symm $ RESharp_in_RE)
  (Iff.trans nm1 (Iff.trans (RESharp_in_RE (r:=(ε ⬝lb R ⬝la ε))) (Eq.to_iff rfl)))

/-- This function computes the `la-join` of `R : EREa α` and `c : CoreRegex α`.
    The resulting regex is of the form `(?<= c.left) ⬝ c.regex ⬝ (?= (r ⬝ ⊤* ⋒ c.right ⬝ ⊤*))`. -/
@[simp]
def CoreRegex.la_join (r : EREa α) (c : CoreRegex α) : CoreRegex α where
  -- (?<= c.left)
  left := c.left
  regex := c.regex
  -- (?= (r ⬝ ⊤* ⋒ c.right ⬝ ⊤*))
  right := r ⬝⚓ pad ⋒⚓ c.right ⬝⚓ pad

/-- This function computes the `lb-join` of `R : EREa α` and `c : CoreRegex α`.
    The resulting regex is of the form `(?<= ?<= (⊤* ⬝ r ⋒ ⊤* ⬝ c.left)) ⬝ c.regex ⬝ (?= c.right)`. -/
@[simp]
def CoreRegex.lb_join (r : EREa α) (c : CoreRegex α) : CoreRegex α where
  -- (?<= (⊤* ⬝ r ⋒ ⊤* ⬝ c.left))
  left := pad ⬝⚓ r ⋒⚓ pad ⬝⚓ c.left
  regex := c.regex
  -- (?= c.right)
  right := c.right

/-- This function computes the intersection of `l : CoreRegex` and `r : CoreRegex`.
    The resulting regex is of the form `(?<= ⊤* ⬝ l.left ⋒ ⊤* ⬝ r.left) (l.regex ⋒ r.regex) (?= l.right ⬝ ⊤* ⋒ r.right ⬝ ⊤*)`. -/
@[simp]
def CoreRegex.intersection (l r : CoreRegex α) : CoreRegex α where
  -- (?<= ⊤* ⬝ l.left ⋒ ⊤* ⬝ r.left)
  left := pad ⬝⚓ l.left ⋒⚓ pad ⬝⚓ r.left
  -- l.regex ⋒ r.regex
  regex := l.regex ⋒⚓ r.regex
  -- (?= l.right ⬝ ⊤* ⋒ r.right ⬝ ⊤*)
  right := l.right ⬝⚓ pad ⋒⚓ r.right ⬝⚓ pad

/-- Given `r : EREa α`, lifts it to a `.Ere r : PiecePosRESharp α`. -/
@[simp]
def lift : EREa α → PiecePosRESharp α := .Ere

/-- The semantics of `c : CoreRegex α` is the following : `(?<= c.left) ⬝ c.regex ⬝ (?= c.right)`.-/
@[simp]
def sem (c : CoreRegex α) : PiecePosRESharp α :=
  c.left ⬝lb_pos lift c.regex ⬝la_pos c.right

/-- This function computes the negated normal form for a list of regexes where complement is
    propagated to the atomic expressions which are `EREa α` components. -/
@[simp]
def takeNegations (rs : List (CoreRegex α)) : List (CoreRegex α) :=
  match rs with
  | [] => [EREa_to_CoreRegex .pad]
  | c :: cs =>
    let cs' := takeNegations cs
    map (.lb_join (nLookbehind c.left)) cs' ++
    map (.la_join (nLookahead c.right)) cs' ++
    map (intersection (EREa_to_CoreRegex (~⚓ c.regex))) cs'

/-- Compute the Cartesian product of `xs` and `ys`, then apply `op` to each pair. -/
@[simp]
def List.productWith (op : α -> α -> α) (xs ys : List α) : List α :=
  map (Function.uncurry op) (product xs ys)

/-- This function computes the lookaround normal form of `r : RESharp α`.
    The resulting normal form is a list of `CoreRegex α`.-/
def lnf (r : RESharp α) : List (CoreRegex α) :=
  match r with
  | .Ere r           => [EREa_to_CoreRegex r]
  | Lookahead r la   => map (la_join la) (lnf r)
  | Lookbehind lb r  => map (lb_join lb) (lnf r)
  | NLookahead r la  => map (la_join (nLookahead la)) (lnf r)
  | NLookbehind lb r => map (lb_join (nLookbehind lb)) (lnf r)
  | .Alt l r         => lnf l ++ lnf r
  | .Inter l r       => productWith intersection (lnf l) (lnf r)
  | Compl r          => takeNegations (lnf r)

/-- This function computes the union (`Alt`) of regular expressions. -/
@[simp]
def re_sum (xs : List (RESharp α)) : RESharp α :=
  match xs with
  | []      => .Ere (Pred ⊥)
  | x :: xs => .Alt x (re_sum xs)

/-- Similar to `re_sum` but computes the union (`Alt`) of regexes which are in
    the positive fragment of `RESharp`. -/
@[simp]
def re_sum_pos (xs : List (PiecePosRESharp α)) : RESharp α :=
  re_sum (xs.map conv)

/-- The main normalization function first computes the list `lnf r` which consists of `CoreRegex`'s.
    Then, it converts all of the components into the positive fragment by eliminating negations and
    negated lookarounds. Finally, it folds the list of `PiecePosRESharp α` into a union. -/
@[simp]
def LNF (r : RESharp α) : RESharp α :=
  re_sum_pos ((lnf r).map sem)

@[simp]
theorem RESharp.bot_isFalse :
  ¬ RESharp.models sp (Ere (Pred (⊥ : α))) :=
  λ h => False.elim (EREa.bot_isFalse h)

theorem sum_append {xs : List (PiecePosRESharp α)} {sp : Span σ} :
  (sp ⊫ᵣ re_sum_pos (x :: xs)) ↔ sp ⊫ᵣ .Alt (conv x) (re_sum_pos xs) :=
  Eq.to_iff rfl

theorem concat_alt {xs ys : List (PiecePosRESharp α)} :
  sp ⊫ᵣ (re_sum_pos (xs ++ ys)) ↔ sp ⊫ᵣ (.Alt (re_sum_pos xs) (re_sum_pos ys) ):=
  match xs with
  | [] =>
    ⟨fun h => Or.inr h,
     fun h =>
     match h with
     | Or.inl h1 => False.elim $ EREa.bot_isFalse h1
     | Or.inr h1 => h1⟩
  | x :: xs =>
    match ys with
    | [] => by
      simp only [re_sum, RESharp.models, append_eq, append_nil]
      simp_rw [EREa.bot_isFalse]
      exact Iff.symm (or_iff_left id)
    | y :: ys => by
      simp only [append_eq, map_append, map_cons, re_sum_pos]
      have ih := concat_alt (xs:=xs) (ys:=y::ys) (sp:=sp)
      simp only [re_sum_pos, map_append, map_cons, RESharp.models] at ih
      simp only [RESharp.models, append_eq]
      rw[ih]
      exact Iff.symm or_assoc

theorem norm_nla_helper {A B C : RE α} :
  (?<=A ⬝ B ⬝ ?=C) ⬝ (?! la) ↔ᵣ
  (?<=A ⬝ B ⬝ ?=((~(la ⬝ .pad) ⬝ endAnchor) ⬝ .pad ⋒ C ⬝ .pad)) :=
  @fun sp => by
  apply equiv_trans equiv_cat_assoc
  apply equiv_concat_congr2
  apply equiv_trans equiv_cat_assoc
  apply equiv_concat_congr2
  apply equiv_trans (equiv_concat_congr2 nla_elim)
  apply equiv_trans concat_lookaheads_inter
  apply equiv_trans equiv_inter_comm
  apply equiv_trans (equiv_sym concat_lookaheads_inter)
  apply RE.la_join

theorem norm_nla {x : CoreRegex α} :
  sp ⊫ᵣ conv (sem x) ⬝nla la ↔
  sp ⊫ᵣ conv (sem (la_join (nLookahead la) x)) := by
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=conv (sem x) ⬝nla la))
  apply Iff.symm
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=conv (sem (la_join (nLookahead la) x))))
  erw[norm_nla_helper]
  rfl

theorem norm_nla_list {la : EREa α} {xs : List (CoreRegex α)} :
  (sp ⊫ᵣ (re_sum_pos (map sem xs)) ⬝nla la) ↔
  (sp ⊫ᵣ re_sum_pos (map sem (map (la_join (nLookahead la)) xs))) := by
  match xs with
  | [] => simp_rw [RESharp.models, EREa.bot_isFalse, false_and]
  | x::xs =>
    apply Iff.intro
    . intro ⟨g1,g2⟩
      match g1 with
      | Or.inl h1 => exact Or.inl (norm_nla.mp ⟨h1,g2⟩)
      | Or.inr h1 => exact Or.inr (norm_nla_list.mp ⟨h1,g2⟩)
    . intro g
      match g with
      | Or.inl h1 => exact ⟨Or.inl (norm_nla.mpr h1).1,(norm_nla.mpr h1).2⟩
      | Or.inr h1 => exact ⟨Or.inr (norm_nla_list.mpr h1).1,(norm_nla_list.mpr h1).2⟩

theorem norm_nlb_helper {A B C D : RE α} :
  ?<!A ⬝ ?<=B ⬝ C ⬝ ?=D ↔ᵣ
  ?<=(.pad ⬝ startAnchor ⬝ ~(.pad ⬝ A) ⋒ .pad ⬝ B) ⬝ C ⬝ ?=D :=
  λ {sp} => by
  apply equiv_trans (equiv_sym equiv_cat_assoc)
  apply equiv_concat_congr
  apply equiv_trans (equiv_concat_congr nlb_elim)
  apply RE.lb_join

theorem norm_nlb {x : CoreRegex α} {sp : Span σ} {nlb : EREa α} :
  sp ⊫ᵣ nlb ⬝nlb conv (sem x) ↔ sp ⊫ᵣ conv (sem (lb_join (nLookbehind nlb) x)) := by
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=nlb ⬝nlb conv (sem x)))
  apply Iff.symm
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=conv (sem (lb_join (nLookbehind nlb) x))))
  apply Iff.symm norm_nlb_helper

theorem norm_nlb_list {nlb : EREa α} {xs : List (CoreRegex α)} :
  (sp ⊫ᵣ nlb ⬝nlb (re_sum_pos (map sem xs))) ↔
  (sp ⊫ᵣ re_sum_pos (map sem (map (lb_join (nLookbehind nlb)) xs))) := by
  match xs with
  | [] =>
    simp only [RESharp.models]; simp_rw[EREa.bot_isFalse,and_false]
  | x::xs =>
    apply Iff.intro
    . intro ⟨g1,g2⟩
      match g2 with
      | Or.inl h1 => exact Or.inl (norm_nlb.mp ⟨g1,h1⟩)
      | Or.inr h1 => exact Or.inr (norm_nlb_list.mp ⟨g1,h1⟩)
    . intro g
      match g with
      | Or.inl h1 => exact ⟨(norm_nlb.mpr h1).1,Or.inl (norm_nlb.mpr h1).2⟩
      | Or.inr h1 => exact ⟨(norm_nlb_list.mpr h1).1,Or.inr (norm_nlb_list.mpr h1).2⟩

theorem norm_la_helper {X Y Z A : RE α} :
  (?<=X ⬝ Y ⬝ ?=Z) ⬝ ?=A ↔ᵣ ?<=X ⬝ Y ⬝ (?=(A ⬝ .pad ⋒ Z ⬝ .pad)) :=
  λ {sp} => by
  apply equiv_trans equiv_cat_assoc
  apply equiv_concat_congr2
  apply equiv_trans equiv_cat_assoc
  apply equiv_concat_congr2
  apply equiv_trans concat_lookaheads_inter
  apply equiv_trans equiv_inter_comm
  apply equiv_trans (equiv_sym concat_lookaheads_inter)
  apply RE.la_join

-- (x.left ⬝lb Ere x.regex ⬝la x.right) (?= la)
theorem norm_la {x : CoreRegex α} :
  sp ⊫ᵣ (conv (sem x)) ⬝la la ↔ sp ⊫ᵣ conv (sem (.la_join la x)) := by
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=(conv (sem x)) ⬝la la))
  apply Iff.symm
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=conv (sem (.la_join la x))))
  apply Iff.symm norm_la_helper

theorem norm_la_list {xs : List (CoreRegex α)} :
  sp ⊫ᵣ re_sum_pos (map sem xs) ⬝la la ↔
  sp ⊫ᵣ re_sum_pos (map sem (map (.la_join la) xs)) := by
  match xs with
  | [] => simp only [re_sum, RESharp.models, EREa.bot_isFalse, false_and]
  | x::xs =>
    apply Iff.intro
    . intro ⟨h1,h2⟩
      match h1 with
      | Or.inl g1 => exact Or.inl (norm_la.mp ⟨g1,h2⟩)
      | Or.inr g1 => exact Or.inr (norm_la_list.mp ⟨g1,h2⟩)
    . intro h
      match h with
      | Or.inl h1 => exact ⟨Or.inl (norm_la.mpr h1).1,(norm_la.mpr h1).2⟩
      | Or.inr h1 => exact ⟨Or.inr (norm_la_list.mpr h1).1,(norm_la_list.mpr h1).2⟩

theorem norm_lb {x : CoreRegex α} {sp : Span σ} {lb : EREa α} :
  sp ⊫ᵣ lb ⬝lb conv (sem x) ↔ sp ⊫ᵣ conv (sem (.lb_join lb x)) := by
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=lb ⬝lb conv (sem x)))
  apply Iff.symm
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=conv (sem (.lb_join lb x))))
  have :=
    equiv_concat_congr (q:=EREa_to_RE x.regex ⬝ ?=(EREa_to_RE x.right)) (sp:=sp)
    (RE.lb_join (X:=EREa_to_RE lb) (Y:= EREa_to_RE x.left))
  rw [equiv_cat_assoc] at this
  apply Iff.symm this

theorem norm_lb_list {xs : List (CoreRegex α)} {lb : EREa α} :
  sp ⊫ᵣ lb ⬝lb re_sum_pos (map sem xs) ↔
  sp ⊫ᵣ re_sum_pos (map sem (map (.lb_join lb) xs)) := by
  match xs with
  | [] => simp only [re_sum, RESharp.models, EREa.bot_isFalse, and_false]
  | x::xs =>
    apply Iff.intro
    . intro ⟨h1,h2⟩
      match h2 with
      | Or.inl g1 => exact Or.inl (norm_lb.mp ⟨h1,g1⟩)
      | Or.inr g1 => exact Or.inr (norm_lb_list.mp ⟨h1,g1⟩)
    . intro h
      match h with
      | Or.inl h1 => exact ⟨(norm_lb.mpr h1).1,Or.inl (norm_lb.mpr h1).2⟩
      | Or.inr h1 => exact ⟨(norm_lb_list.mpr h1).1,Or.inr (norm_lb_list.mpr h1).2⟩

theorem norm_intersection_helper {A : RE α} :
  ?<=A ⬝ B ⬝ ?=C ⋒ ?<=D ⬝ E ⬝ ?=F ↔ᵣ
  ?<=(.pad ⬝ A ⋒ .pad ⬝ D) ⬝ (B ⋒ E) ⬝ ?=(C ⬝ .pad ⋒ F ⬝ .pad) :=
  λ {sp} => by
  apply equiv_trans RE.and_elim
  apply equiv_trans (equiv_sym equiv_cat_assoc)
  apply equiv_trans (equiv_cat_cong RE.lb_join (equiv_concat_congr2 RE.la_join))
  apply equiv_concat_congr2
  apply equiv_concat_congr2
  apply equiv_refl

theorem norm_intersection {l r : CoreRegex α} :
  sp ⊫ᵣ .Inter (conv (sem l)) (conv (sem r)) ↔
  sp ⊫ᵣ conv (sem (l.intersection r)) := by
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=.Inter (conv (sem l)) (conv (sem r))))
  apply Iff.symm
  apply Iff.trans (Iff.symm $ RESharp_in_RE (r:=conv (sem (l.intersection r))))
  apply Iff.symm norm_intersection_helper

theorem models_sum' {rs : List (PiecePosRESharp α)} {sp : Span σ}  :
  sp ⊫ᵣ re_sum_pos rs ↔ ∃ u ∈ rs, sp ⊫ᵣ conv u := by
  match rs with
  | [] =>
    simp only [re_sum_pos, re_sum, RESharp.bot_isFalse, not_mem_nil, false_and, exists_false]
  | r::rs =>
    apply Iff.intro
    . intro h
      match h with
      | Or.inl h1 => exact ⟨r,mem_cons_self r rs,h1⟩
      | Or.inr h1 => let ⟨u,h2,h3⟩ := models_sum'.mp h1; exact ⟨u,mem_cons_of_mem r h2,h3⟩
    . intro ⟨us,h1,h2⟩
      match mem_cons.mp h1 with
      | Or.inl h2 => subst h2; exact Or.inl h2
      | Or.inr h1 => exact Or.inr (models_sum'.mpr ⟨us,h1,h2⟩)

theorem models_sum {rs : List (RESharp α)} {sp : Span σ}  :
  sp ⊫ᵣre_sum rs ↔ ∃ u ∈ rs, sp ⊫ᵣ u := by
  match rs with
  | [] => simp only [re_sum, RESharp.bot_isFalse, not_mem_nil, false_and, exists_false]
  | r::rs =>
    apply Iff.intro
    . intro h
      match h with
      | Or.inl h1 => exact ⟨r,mem_cons_self r rs,h1⟩
      | Or.inr h1 => let ⟨u,h2,h3⟩ := models_sum.mp h1; exact ⟨u,mem_cons_of_mem r h2,h3⟩
    . intro ⟨us,h1,h2⟩
      match mem_cons.mp h1 with
      | Or.inl h2 => subst h2; exact Or.inl h2
      | Or.inr h1 => exact Or.inr (models_sum.mpr ⟨us,h1,h2⟩)

theorem models_not_and_unfold {xs : List (CoreRegex α)} :
  ¬(sp ⊫ᵣ (re_sum_pos (map sem (x :: xs))))
  ↔ ¬(sp ⊫ᵣ (conv (sem x))) ∧ ¬(sp ⊫ᵣ(re_sum_pos (map sem xs))) := by
  simp only [RESharp.models, Span.reverse, Span.beg, Span.left, Span.match, Span.right, reverse_nil,
    nil_append, Prod.mk.injEq, map_map, not_or, not_and, not_exists, forall_exists_index, and_imp,
    re_sum_pos]

theorem models_compl_unfold {x : RESharp α} :
  ¬RESharp.models sp x ↔ RESharp.models sp x.Compl := by
  simp only [RESharp.models]

theorem norm_inter_xs {sp : Span σ} {x : CoreRegex α} :
    sp ⊫ᵣ (.Inter (re_sum_pos (map sem xs)) (Ere ~⚓ x.regex))
  ↔ sp ⊫ᵣ (re_sum_pos (map sem (map (EREa_to_CoreRegex ~⚓x.regex).intersection xs))) := by
  match xs with
  | [] =>
    simp only [re_sum_pos, re_sum, RESharp.bot_isFalse, iff_false]
    unfold RESharp.models
    simp_rw [RESharp.bot_isFalse, false_and, not_false_eq_true]
  | a::as =>
    apply Iff.intro
    . intro ⟨h1,h2⟩
      simp only [map_cons, intersection, map_map, sem]
      rw[sum_append]
      unfold RESharp.models
      have ih := norm_inter_xs (sp:=sp) (x:=x) (xs:=as)
      simp only [map_cons, intersection, map_map, sem] at ih
      rw[←ih]
      erw[sum_append] at h1
      match h1 with
      | Or.inl t1 =>
        rw[CoreRegex_equivalence] at h2
        simp_rw[←RESharp_in_RE, RESharp_to_RE, EREa_to_RE] at h2 t1
        simp_rw[←RESharp_in_RE, RESharp_to_RE, EREa_to_RE]
        erw[←norm_intersection_helper, RE.models]
        exact Or.inl ⟨h2,t1⟩
      | Or.inr t1 => apply Or.inr ⟨t1,h2⟩
    . intro h
      simp only [map_cons, intersection, map_map, sem] at h
      rw[sum_append] at h
      match h with
      | Or.inl h1 =>
        simp only [map_cons, intersection, map_map, sem]
        unfold RESharp.models
        simp_rw[sum_append,←RESharp_in_RE,RESharp_to_RE,EREa_to_RE]
        simp_rw[←RESharp_in_RE, RESharp_to_RE, EREa_to_RE] at h1
        erw[←norm_intersection_helper] at h1
        conv => lhs; unfold RE.models
        unfold RE.models at h1
        exact ⟨Or.inl h1.2,nm1.mpr h1.1⟩
      | Or.inr h1 =>
        simp only [map_cons, intersection, map_map, sem]
        unfold RESharp.models
        erw[sum_append]
        erw[←map_map, ←norm_inter_xs] at h1
        exact ⟨Or.inr h1.1,h1.2⟩

theorem RESharp.models_TopStar {sp : Span σ} :
  sp ⊫ᵣ RESharp.Ere (pad : EREa α) := RESharp_in_RE.mp (RE.models_TopStar)

theorem takeNegations_correctness {rs : List (CoreRegex α)} {sp : Span σ} :
  sp ⊫ᵣ re_sum_pos (map sem (takeNegations rs)) ↔
  ¬ (sp ⊫ᵣ (re_sum_pos (map sem rs))) := by
  match rs with
  | [] =>
    simp only [takeNegations, re_sum_pos, re_sum, conv, EREa_to_CoreRegex]
    simp only [RESharp.bot_isFalse, not_false_eq_true, iff_true]
    apply Or.inl (CoreRegex_equivalence.mp models_TopStar)
  | x::xs =>
    erw[map_append, concat_alt,map_append]
    rw[models_not_and_unfold, models_compl_unfold]
    conv => lhs; unfold RESharp.models
    erw[concat_alt]
    conv => lhs; simp only [RESharp.models]
    erw[←norm_nlb_list,←norm_nla_list,←norm_inter_xs]
    conv => lhs; simp only [RESharp.models]
    simp_rw[takeNegations_correctness,models_compl_unfold]
    apply Iff.intro
    . intro h
      match h with
      | Or.inl h1 =>
        match h1 with
        | Or.inl ⟨h2a,h2b⟩ =>
          exact ⟨not_and.mpr fun a a_1 ↦ h2a a,h2b⟩
        | Or.inr ⟨h2a,h2b⟩ =>
          simp only [RESharp.models]
          exact ⟨by rw[not_and]; intro g ⟨g1a,g1b⟩; contradiction,h2a⟩
      | Or.inr ⟨h1a,h1b⟩ =>
        simp only [RESharp.models]
        exact ⟨by rw[not_and]; intro g ⟨g1a,g1b⟩; simp only [EREa.models] at h1b
                  contradiction,h1a⟩
    . intro ⟨h1,h2⟩
      simp only [sem, lift, conv] at h1
      rw[←RESharp_in_RE] at h1 h2
      simp only [RESharp_to_RE] at h1 h2
      simp_rw[not_elim] at h1
      simp only [←RESharp_in_RE, RESharp_to_RE, h2]
      simp only [not_and, and_true, true_and, EREa.models]
      unfold RE.models at h1
      match h1 with
      | Or.inl p1 =>
        apply Or.inl; apply Or.inl
        unfold RE.models at p1; simp only at p1
        simp only [not_exists, not_and]
        intro ⟨s,u,v⟩ p2 p3
        let ⟨s1,u1,v1⟩ := sp
        simp at p2 p3
        let ⟨p3a,p3b⟩ := p3
        subst p3a
        simp only [RE.models, not_exists, not_and] at p1
        let ⟨a1,a2,⟨a3,a4⟩,a5,a6⟩ := p1
        simp at a3; subst a3; simp at a6; subst a6 p3b
        have := a4 (Span.reverse (v, u.reverse, a2 ++ v1))
                   (by simp only [Span.reverse, reverse_reverse, EREa_in_RE]; exact p2)
        simp at this
      | Or.inr p1 =>
        simp[EREa_in_RE] at p1
        match p1 with
        | Or.inl p2 => apply Or.inr p2
        | Or.inr p2 =>
          apply Or.inl; apply Or.inr
          let ⟨s1,u1,v1⟩ := sp
          simp; intro ⟨s,u,v⟩ p3 p4 p5
          simp only at p3 p4 p5
          let ⟨u1,u2,⟨u3,a4⟩,a5⟩ := p2
          subst u3; simp only [append_nil] at a5; subst a5; subst p4 p5
          exact a4 (u1.reverse ++ s1, u, v) p3 rfl rfl

/-- The main correctness theorem for the lookaround normal form. Any `r : RESharp α` is equivalent to
    a union of normalized `CoreRegex`'s.-/
theorem lnf_correct {R : RESharp α} {sp : Span σ} :
  sp ⊫ᵣ R ↔ sp ⊫ᵣ LNF R :=
  match R with
  | .Ere r =>
    ⟨λ h => Or.inl (CoreRegex_equivalence.mp h),
     λ h => by
     simp only [LNF, lnf, re_sum_pos, re_sum, sem, EREa_to_CoreRegex, lift, conv] at h
     unfold RESharp.models at h
     simp_rw [RESharp.bot_isFalse, or_false] at h
     apply CoreRegex_equivalence.mpr h⟩
  | Lookahead r la => by
    conv => lhs; unfold RESharp.models
    rw [lnf_correct (R:=r)] -- inductive hypothesis
    apply norm_la_list
  | Lookbehind lb r => by
    conv => lhs; unfold RESharp.models
    rw [lnf_correct (R:=r)] -- inductive hypothesis
    apply norm_lb_list
  | NLookahead r la => by
    conv => lhs; unfold RESharp.models
    rw [lnf_correct (R:=r)] -- inductive hypothesis
    apply norm_nla_list
  | NLookbehind lb r => by
    conv => lhs; unfold RESharp.models
    rw [lnf_correct (R:=r)] -- inductive hypothesis
    apply norm_nlb_list
  | .Alt l r => by
    conv => lhs; unfold RESharp.models
    rw [lnf_correct (R:=l),lnf_correct (R:=r)] -- inductive hypothesis
    simp only [LNF, lnf, map_append, map_map]
    apply Iff.symm concat_alt
  | .Inter l r => by
    simp only [RESharp.models, LNF]
    unfold lnf
    rw [lnf_correct (R:=l),lnf_correct (R:=r)] -- inductive hypothesis
    simp only [LNF]
    erw [models_sum, models_sum', models_sum']
    apply Iff.intro
    . intro ⟨⟨a1,a2,a3⟩,⟨b1,b2,b3⟩⟩
      simp only [map_map, mem_map, Function.comp_apply, sem, lift] at a2 b2
      let ⟨c1,c2,c3⟩ := a2; let ⟨d1,d2,d3⟩ := b2
      subst c3 d3
      exact ⟨sem (intersection c1 d1),
             by simp [product]; exists c1; exists c2; exists d1;,
             norm_intersection.mp ⟨a3,b3⟩⟩
    . intro ⟨a1,a2,a3⟩
      simp [product] at a2
      let ⟨b1,b2,b3,b4,b5⟩ := a2
      subst b5
      simp only [map_map, mem_map, Function.comp_apply, sem, lift, exists_exists_and_eq_and]
      exact ⟨⟨b1,b2,(norm_intersection.mpr a3).1⟩, ⟨b3,b4,(norm_intersection.mpr a3).2⟩⟩
  | Compl r => by
    simp only [RESharp.models, LNF, lnf]
    rw [lnf_correct (R:=r)] -- inductive hypothesis
    apply Iff.symm takeNegations_correctness

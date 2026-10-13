import SourceRuntime.Source.Named

/-! Selected scope, grammar, typing and reduction examples. General proofs live
in Syntax, Binding, Typing and Reduction; these examples illustrate specific cases. -/

namespace SourceRuntime.Source

open WSLN Adequacy

-- let x = x in x: the RHS x stays free, and only the body x is bound.
example (x : WSLN.Atom) :
    let_ x (var x) (var x) = letE (var x) i0 := by
  simp [let_, var, Trm.abs, i0]

-- let x = (let y = 21 in y) in x: the first step only reduces the RHS.
example :
    Step (letE (letE (integer 21) i0) i0) (letE (integer 21) i0) := by
  apply Step.search_let
  · simpa [i0] using Step.let_value (.integer 21) (.atom (.bound ⟨0, by omega⟩))
  · exact .atom (.bound ⟨0, by omega⟩)

-- A variable RHS has no step; Let does not substitute an arbitrary atom.
example (x : WSLN.Atom) (body : RawTerm 1) (next : RawTerm 0) :
    ¬ Step (letE (var x) body) next := by
  intro h
  cases h with
  | search_let h _ => cases h
  | let_value hv _ => cases hv

-- The inserted free y stays free beneath a binder for y.
example :
    ((0 ≔ var 1) : Sb signature) * let_ 1 (integer 0) (add (var 0) (var 1))
      = letE (integer 0) (add (var 1) i0) := rfl

-- Let accepts all values in this fragment, including an open constructor value.
example (x : WSLN.Atom) :
    Step (letE (pair (var x) nil) i0) (pair (var x) nil) := by
  simpa [i0] using Step.let_value (IsValue.pair (.free x) (.value .nil))
    (IsTerm.atom (.bound ⟨0, by omega⟩))

-- let x = 2 + 3 in x + 1 takes a search step, then Let, then Add.
example : Step (letE (add (integer 2) (integer 3)) (add i0 (integer 1)))
    (letE (integer 5) (add i0 (integer 1))) :=
  .search_let (.add 2 3) (.add (.bound ⟨0, by omega⟩) (.value (.integer 1)))

example : Step (letE (integer 5) (add i0 (integer 1))) (add (integer 5) (integer 1)) :=
  Step.let_value (.integer 5) (.add (.bound ⟨0, by omega⟩) (.value (.integer 1)))

example : Step (add (integer 5) (integer 1)) (integer 6) := .add 5 1

-- The outer RHS uses Γ; the inner let shadows x with a different type.
example (x : WSLN.Atom) :
    HasType [(x, .sexp)] (let_ x (var x) (let_ x (integer 21) (var x))) .int := by
  apply typing_let (A := .sexp) (.free (by simp))
  apply typing_let (.integer 21)
  exact .free (by simp)

-- This is a value according to the grammar, but Pair requires sexp fields.
example (Γ : Context) (A : Ty) : ¬ HasType Γ (pair (integer 21) nil) A := by
  intro ht
  cases ht with
  | pair _ _ hi _ => cases hi

-- Formation allows differently typed branches; typing checks them separately.
example : IsTerm (n := 0)
    (async (ifE (boolean true) (operation .lt (integer 1) (integer 2))
      (sexp_id (identifier "node")))) :=
  .async (.ifE (.value (.boolean true))
    (.operation .lt (.value (.integer 1)) (.value (.integer 2)))
    (.atom (.value (.sexp_id (.value (.identifier "node"))))))

-- A general computation cannot occupy the atom position of an if guard.
example (rhs : RawTerm 0) (body : RawTerm 1) (yes no : RawTerm 0) :
    ¬ IsTerm (ifE (letE rhs body) yes no) := by
  intro ht
  cases ht with
  | atom ha => cases ha with | value hv => cases hv
  | ifE hg _ _ => cases hg with | value hv => cases hv

-- Identifier literals are constants, even under an arbitrary substitution.
example (σ : Sb signature) (i : Id) :
    σ * (identifier i : RawTerm 0) = identifier i := rfl

-- Numeric names below are variable identities, not source integer literals.
-- The displayed order x, y becomes slots 0, 1.
example :
    fun_ (10, .int) [(11, .int)] .int (operation .sub (var 10) (var 11)) (by decide)
      = funE (n := 0) .int [.int] .int
        (operation (n := 2) .sub (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)) := rfl

-- For fix, self precedes all parameters: f, x, y becomes 0, 1, 2.
example :
    fix_ 9 (10, .int) [(11, .int)] .int
      (app (k := 1) (var 9) (var 10) (.cons (var 11) .nil)) (by decide)
      = fixE (n := 0) .int [.int] .int
        (app (n := 3) (k := 1) (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)
          (.cons (.var ⟨2, by decide⟩) .nil)) := rfl

-- The slot order matters for a noncommutative operation. This is instantiation,
-- not a function-reduction rule or an arithmetic evaluation.
example :
    instantiate [integer 21, integer 7]
      (closeMany [10, 11] (operation .sub (var 10) (var 11)))
      = operation .sub (integer 21) (integer 7) := rfl

-- Simultaneous replacement: y inserted for x must not later become 7.
example :
    instantiate [var 11, integer 7] (closeMany [10, 11] (pair (var 10) (var 11)))
      = pair (var 11) (integer 7) := rfl

-- Substitution beneath a function must leave the inserted x free.
example :
    ((11 ≔ var 10) : Sb signature) *
        fun_ (10, .int) [] .int (add (var 10) (var 11)) (by decide)
      = funE .int [] .int (add (.var ⟨0, by omega⟩) (var 10)) := rfl

-- Distinct names are required within one abstractor; nested shadowing is legal.
example :
    fun_ (10, .int) [] (.arrow .int [] .int)
        (fun_ (10, .int) [] .int (var 10) (by decide)) (by decide)
      = funE .int [] (.arrow .int [] .int)
        (funE .int [] .int (.var ⟨0, by omega⟩)) := rfl

-- A source application may use an open function variable and several atoms.
example : IsTerm (n := 0) (app (k := 1) (var 9) (integer 21) (.cons (integer 7) .nil)) :=
  .app (.free 9) (.value (.integer 21)) (.cons (.value (.integer 7)) .nil)

-- A general term cannot occupy either the function or an argument position.
example (rhs : RawTerm 0) (body : RawTerm 1) (a : RawTerm 0) :
    ¬ IsTerm (app (k := 0) (letE rhs body) a .nil) := by
  intro ht
  cases ht with
  | atom ha => cases ha with | value hv => cases hv
  | app hf _ _ => cases hf with | value hv => cases hv

example (rhs : RawTerm 0) (body : RawTerm 1) (fn a : RawTerm 0) :
    ¬ IsTerm (app (k := 1) fn a (.cons (letE rhs body) .nil)) := by
  intro ht
  cases ht with
  | atom ha => cases ha with | value hv => cases hv
  | app _ _ hs => cases hs with | cons ha _ => cases ha with | value hv => cases hv

-- Match has an atomic scrutinee and separately bound branch bodies.
example : IsTerm (n := 0) (matchE (k := 2) (var 9)
    (.cons (branch_ .pair [10, 11] (add (var 10) (var 11)) rfl (by decide))
      (.cons (branch_ .wildcard [] (integer 0) rfl (by decide)) .nil))) :=
  .matchE (.free 9)
    (.cons (IsBranch.branch_ _ _ (.add (.free 10) (.free 11)) _ _)
      (.cons (IsBranch.branch_ _ _ (.atom (.value (.integer 0))) _ _) .nil))
    (by unfold MatchPatterns; decide)

-- Pair fields bind in the same left-to-right order as function parameters.
example : branch_ .pair [10, 11] (operation .sub (var 10) (var 11)) rfl (by decide)
    = branch (n := 0) .pair
      (operation (n := 2) .sub (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩)) := rfl

-- Binding in the Int branch affects neither the scrutinee nor the wildcard body.
example : ((10 ≔ integer 21) : Sb signature) *
    matchE (k := 2) (var 10)
      (.cons (branch_ .int [10] (var 10) rfl (by decide))
        (.cons (branch_ .wildcard [] (var 10) rfl (by decide)) .nil))
    = matchE (n := 0) (k := 2) (integer 21)
      (.cons (branch .int i0) (.cons (branch .wildcard (integer 21)) .nil)) := rfl

-- A wildcard alone, a missing wildcard, an early wildcard, and duplicate heads
-- each violate §3.2. The same checks apply independently of branch-body typing.
example : ¬ MatchPatterns [.wildcard] ∧ ¬ MatchPatterns [.nil, .pair] ∧
    ¬ MatchPatterns [.wildcard, .nil] ∧ ¬ MatchPatterns [.pair, .pair, .wildcard] := by
  unfold MatchPatterns
  decide

-- A standalone branch is not a source term, even with a valid body.
example (body : RawTerm 2) : ¬ IsTerm (branch (n := 0) .pair body) := by
  intro h
  cases h with
  | atom ha => cases ha with | value hv => cases hv

-- T-App keeps the bool/int parameter order; the body also uses T-If and T-Async.
example : HasType []
    (app (k := 1) (funE .bool [.int] .int
      (async (ifE (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩) (integer 0))))
      (boolean true) (.cons (integer 7) .nil)) .int := by
  apply Typing.app
  · exact .value (.funE _ _ _ (.async (.ifE (.bound _) (.atom (.bound _)) (.atom (.value (.integer 0))))))
  · exact .value (.boolean true)
  · exact .funE (.async (.ifE (.bound _) (.bound _) (.bound _) (.integer 0)))
  · exact .boolean true
  · exact .cons (.value (.integer 7)) (.integer 7) .nil

-- Pair's two slots precede the surrounding fix's self and parameter slots.
example : HasType []
    (fixE .sexp [] .int
      (matchE (k := 3) (.var ⟨1, by decide⟩)
        (.cons (branch .int (.var ⟨0, by decide⟩))
          (.cons (branch .pair
            (app (k := 0) (.var ⟨2, by decide⟩) (.var ⟨0, by decide⟩) .nil))
            (.cons (branch .wildcard (integer 0)) .nil))))) (.arrow .sexp [] .int) := by
  apply Typing.fixE
  apply Typing.matchE (ps := [.int, .pair, .wildcard])
  · exact .bound _
  · exact .bound _
  · exact .cons (.int (.bound _))
      (.cons (.pair (.app (.bound _) (.bound _) (.bound _) (.bound _) .nil))
        (.cons (.wildcard (.integer 0)) .nil))
  · unfold MatchPatterns; decide

-- A function requiring two arguments cannot be applied to just the first one.
example : ¬ HasType []
    (app (k := 0) (funE .bool [.int] .int (.var ⟨1, by decide⟩)) (boolean true) .nil) .int := by
  intro ht
  cases ht with
  | app _ _ hf _ hs => cases hf; cases hs

-- The calculus has no Boolean equality rule.
example (Γ : Context) : ¬ HasType Γ (operation .eq (boolean true) (boolean false)) .bool := by
  intro ht
  cases ht with
  | eq hA _ _ ha _ => cases ha; simp at hA

-- Match formation alone does not ensure one common branch result type.
example (Γ : Context) (A : Ty) : ¬ HasType Γ
    (matchE (k := 2) nil (.cons (branch .nil unit) (.cons (branch .wildcard (integer 0)) .nil))) A := by
  intro ht
  cases ht with
  | matchE _ _ hs _ =>
      cases hs with
      | cons hb hs =>
          cases hb with
          | nil ht =>
              cases ht
              cases hs with
              | cons hb _ => cases hb with | wildcard ht => cases ht

-- The paper's mixed bool/int example: beta exposes the if; a second step selects 7.
example : Steps
    (app (k := 1) (funE .bool [.int] .int
      (ifE (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩) (integer 0)))
      (boolean true) (toArgs [integer 7])) (integer 7) := by
  apply Steps.step (u := ifE (boolean true) (integer 7) (integer 0))
  · exact Step.beta (A := .bool) (As := [.int]) (B := .int) (v := boolean true) (vs := [integer 7]) rfl
      (.ifE (.bound _) (.atom (.bound _)) (.atom (.value (.integer 0))))
      (.boolean true) (by intro a h; simp at h; subst a; exact .integer 7)
  · exact .step (.if_true (.atom (.value (.integer 7))) (.atom (.value (.integer 0)))) (.refl (.atom (.value (.integer 7))))

-- A recursive call reinstates self before its parameter; divergence is permitted.
example :
    let f := fixE .int [] .int (app (k := 0) (.var ⟨0, by decide⟩) (.var ⟨1, by decide⟩) .nil)
    Step (app (k := 0) f (integer 7) .nil) (app (k := 0) f (integer 7) .nil) := by
  exact Step.fix_beta (A := .int) (As := []) (B := .int) (v := integer 7) (vs := []) rfl
    (.app (k := 0) (.bound _) (.bound _) .nil) (.integer 7) (by simp)

-- Pair matching accepts open atom fields and respects their displayed order.
example (x y : WSLN.Atom) : Step
    (matchE (k := 2) (pair (var x) (var y))
      (.cons (branch .pair (pair (.var ⟨1, by decide⟩) (.var ⟨0, by decide⟩)))
        (.cons (branch .wildcard nil) .nil))) (pair (var y) (var x)) := by
  apply Step.match_constructor (ps := [.pair, .wildcard])
  · exact .cons (.branch (.atom (.value (.pair (.bound _) (.bound _)))))
      (.cons (.branch (.atom (.value .nil))) .nil)
  · unfold MatchPatterns; decide
  · exact .here
  · exact .pair (.free x) (.free y)

-- An absent constructor head selects the final wildcard.
example : Step
    (matchE (k := 2) nil
      (.cons (branch .int (integer 1)) (.cons (branch .wildcard (integer 2)) .nil))) (integer 2) := by
  apply Step.match_wildcard (ps := [.int, .wildcard]) (p := .nil)
  · exact .nil
  · rfl
  · decide
  · exact .cons (.branch (.atom (.value (.integer 1))))
      (.cons (.branch (.atom (.value (.integer 2)))) .nil)
  · unfold MatchPatterns; decide
  · exact .there .here

-- A literal cannot select the wildcard: the scrutinee must be a constructor value.
example {k} (bs : RawArgs 0 k) (result : RawTerm 0) :
    ¬ Step (matchE (integer 0) bs) result := by
  intro h
  cases h with
  | match_constructor _ _ _ hc => cases hc
  | match_wildcard _ hh _ _ _ _ => simp [constructorHead, integer] at hh

-- The named rule allows an existing same-spelled Γ binding to be shadowed.
example : HasType [(10, .sexp)]
    (fun_ (10, .bool) [(11, .int)] .int
      (ifE (var 10) (var 11) (integer 0)) (by decide)) (.arrow .bool [.int] .int) := by
  apply typing_fun_
  exact .ifE (.free 10) (.free rfl) (.free rfl) (.integer 0)

end SourceRuntime.Source

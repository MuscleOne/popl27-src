import SourceRuntime.Source.Syntax

/-!
Source §§3--5: named binding, alpha-equivalence and substitution correspondence.
The first name occupies index zero, followed by the remaining names in order.
For fix this sequence is self, then the parameters, as in OCaml Syntax.fix.
The named entry points compose WSLN's abstraction/concretion operations.
-/

namespace SourceRuntime.Source

open WSLN Adequacy

def namedLet (x : WSLN.Atom) (rhs body : NamedTerm) : NamedTerm :=
  .op .letE (.cons (.base rhs) (.cons (.abs x (.base body)) .nil))

theorem translate_let (x : WSLN.Atom) (rhs body : NamedTerm) :
    toWS (namedLet x rhs body) = let_ x (toWS rhs) (toWS body) := rfl

/-- Equality of translated terms corresponds to alpha-equivalence of names. -/
theorem alpha_iff (M N : NamedTerm) :
    AlphaEq M N ↔ toWS M = toWS N :=
  ⟨Adequacy.sound, Adequacy.injective M N⟩

/-- The named and locally nameless substitution operations agree. -/
theorem translate_substitution (x : WSLN.Atom) (a body : NamedTerm) :
    toWS ((x ≔ⁿ a) * body) = ((x ≔ toWS a) : Sb signature) * toWS body :=
  Adequacy.updateCorrect a x body

-- The binder name is irrelevant, including when that name occurs in the RHS.
theorem rename_bound (x y : WSLN.Atom) (rhs : NamedTerm) :
    AlphaEq (namedLet x rhs (.atom x)) (namedLet y rhs (.atom y)) := by
  apply (alpha_iff _ _).mpr
  simp [translate_let, let_, Trm.abs]

/-- Close a whole abstractor, in its displayed left-to-right order. -/
def closeMany (names : List WSLN.Atom) (body : RawTerm 0) : RawTerm names.length :=
  match names with
  | [] => body
  | x :: xs => x ． closeMany xs body

/-- Instantiate the same ordered slots. Inserted free names remain free. -/
def instantiate (args : List (RawTerm 0)) (body : RawTerm args.length) : RawTerm 0 :=
  match args with
  | [] => body
  | a :: rest => instantiate rest (body.conc a)

def fun_ (first : WSLN.Atom × Ty) (rest : List (WSLN.Atom × Ty))
    (result : Ty) (body : RawTerm 0)
    (_distinct : (first.1 :: rest.map Prod.fst).Nodup) : RawTerm 0 :=
  funE first.2 (rest.map Prod.snd) result
    ((closeMany (first.1 :: rest.map Prod.fst) body).castScope (by simp))

def fix_ (self : WSLN.Atom) (first : WSLN.Atom × Ty) (rest : List (WSLN.Atom × Ty))
    (result : Ty) (body : RawTerm 0)
    (_distinct : (self :: first.1 :: rest.map Prod.fst).Nodup) : RawTerm 0 :=
  fixE first.2 (rest.map Prod.snd) result
    ((closeMany (self :: first.1 :: rest.map Prod.fst) body).castScope (by simp))

theorem IsTerm.castScope {m n} {body : RawTerm m} (hb : IsTerm body) (e : m = n) :
    IsTerm (body.castScope e) := by
  cases e
  exact hb

theorem IsTerm.closeMany {body : RawTerm 0} (hb : IsTerm body) (names : List WSLN.Atom) :
    IsTerm (closeMany names body) := by
  induction names with
  | nil => exact hb
  | cons x xs ih => exact ih.close x ⟨0, by omega⟩ rfl

theorem IsTerm.instantiate (args : List (RawTerm 0)) {body : RawTerm args.length}
    (hb : IsTerm body) (ha : ∀ a ∈ args, IsAtom a) : IsTerm (instantiate args body) := by
  induction args with
  | nil => exact hb
  | cons a rest ih =>
      exact ih (hb.open (⟨0, Nat.succ_pos rest.length⟩ : Fin (rest.length + 1))
        (ha a (by simp)) rfl)
        (fun b h => ha b (by simp [h]))

theorem IsValue.fun_ (first : WSLN.Atom × Ty) (rest : List (WSLN.Atom × Ty))
    (result : Ty) {body : RawTerm 0} (hb : IsTerm body)
    (distinct : (first.1 :: rest.map Prod.fst).Nodup) :
    IsValue (fun_ first rest result body distinct) :=
  .funE _ _ _ ((hb.closeMany _).castScope _)

theorem IsValue.fix_ (self : WSLN.Atom) (first : WSLN.Atom × Ty)
    (rest : List (WSLN.Atom × Ty)) (result : Ty) {body : RawTerm 0} (hb : IsTerm body)
    (distinct : (self :: first.1 :: rest.map Prod.fst).Nodup) :
    IsValue (fix_ self first rest result body distinct) :=
  .fixE _ _ _ ((hb.closeMany _).castScope _)

/-- As in OCaml Syntax.branch, the pattern fixes the number of distinct binders. -/
def branch_ (p : Pattern) (names : List WSLN.Atom) (body : RawTerm 0)
    (arity : names.length = p.arity) (_distinct : names.Nodup) : RawTerm 0 :=
  branch p ((closeMany names body).castScope (by simpa using arity))

theorem IsBranch.branch_ (p : Pattern) (names : List WSLN.Atom) {body : RawTerm 0}
    (hb : IsTerm body) (arity : names.length = p.arity) (distinct : names.Nodup) :
    IsBranch p (branch_ p names body arity distinct) :=
  .branch ((hb.closeMany names).castScope _)

/-- The named abstractor used by WSLN's adequacy translation. -/
def namedBind (names : List WSLN.Atom) (body : NamedTerm) : NomBnd signature names.length :=
  match names with
  | [] => .base body
  | x :: xs => .abs x (namedBind xs body)

/-- Our closing order agrees with the library's translation for every binder length. -/
theorem translate_closeMany (names : List WSLN.Atom) (body : NamedTerm) :
    toWSBnd (namedBind names body) = closeMany names (toWS body) := by
  induction names with
  | nil => rfl
  | cons x xs ih => simp only [namedBind, toWSBnd, closeMany, ih]

/-- Encode the paper's ordered operand sequence in WSLN's argument spine. -/
def toArgs {n : Nat} (as : List (RawTerm n)) : RawArgs n as.length :=
  match as with
  | [] => .nil
  | a :: rest => .cons a (toArgs rest)

theorem IsAtoms.toArgs {n} {as : List (RawTerm n)} (ha : ∀ a ∈ as, IsAtom a) :
    IsAtoms (toArgs as) := by
  induction as with
  | nil => exact .nil
  | cons a rest ih => exact .cons (ha a (by simp)) (ih (fun b h => ha b (by simp [h])))

private theorem cast_conc {m n} (e : m = n) (body : RawTerm (m + 1)) (a : RawTerm 0) :
    (body.castScope (congrArg (· + 1) e)).conc a = (body.conc a).castScope e := by
  cases e; rfl

@[simp] theorem castScope_trans {m n k} (e : m = n) (f : n = k) (t : RawTerm m) :
    (t.castScope e).castScope f = t.castScope (e.trans f) := by
  cases e; cases f; rfl

theorem instantiate_subst (σ : Sb signature) (args : List (RawTerm 0)) (body : RawTerm args.length) :
    σ * instantiate args body =
      instantiate (args.map (fun a => σ * a)) ((σ * body).castScope (by simp)) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      simp only [instantiate, List.map_cons]
      rw [cast_conc (by simp : rest.length = (rest.map (fun a => σ * a)).length)]
      have hc : σ * (body.conc a) = (σ * body).conc (σ * a) := sb_conc σ body a
      rw [← hc]
      exact ih (body.conc a)

theorem instantiate_names (names : List WSLN.Atom) (body : RawTerm 0) :
    instantiate (names.map (var (n := 0))) ((closeMany names body).castScope (by simp)) = body := by
  induction names with
  | nil => rfl
  | cons x xs ih =>
      simp only [closeMany, List.map_cons, instantiate]
      rw [cast_conc, show (x ． closeMany xs body).conc (var x) = closeMany xs body from concAbs' x _]
      exact ih

private theorem fresh_closeMany (names : List WSLN.Atom) (body : RawTerm 0)
    {x} (hx : x ∈ names) : x # closeMany names body := by
  induction names with
  | nil => cases hx
  | cons y ys ih =>
      cases hx with
      | head => exact fresh_abs _ _
      | tail _ hx => exact fresh_abs' _ (ih hx)

private theorem instantiate_cast_eq {as bs : List (RawTerm 0)} (h : as = bs)
    {n} (body : RawTerm n) (ea : n = as.length) (eb : n = bs.length) :
    instantiate as (body.castScope ea) = instantiate bs (body.castScope eb) := by
  cases h; rfl

/-- Closing then instantiating agrees with one simultaneous substitution.
    Each supplied image σ x is inserted unchanged, even if it contains other names. -/
theorem instantiate_closeMany (names : List WSLN.Atom) (body : RawTerm 0) (σ : Sb signature)
    (outside : ∀ x, x ∉ names → σ x = var x)
    {args : List (RawTerm 0)} (images : args = names.map σ) :
    instantiate args ((closeMany names body).castScope (by rw [images]; simp)) = σ * body := by
  have hc : σ * closeMany names body = closeMany names body := by
    calc
      σ * closeMany names body = Sb.id * closeMany names body := by
        apply sbRespSupp
        intro x hx
        apply outside
        intro hn
        exact Fset.not_mem_of_notMem (fresh_closeMany names body hn) hx
      _ = closeMany names body := sbUnit _
  have h := instantiate_subst σ (names.map (var (n := 0)))
    ((closeMany names body).castScope (by simp))
  rw [instantiate_names] at h
  have hargs : (names.map (var (n := 0))).map (fun a => σ * a) = names.map σ := by
    simp [List.map_map, var]
  calc
    instantiate args ((closeMany names body).castScope _) =
      instantiate ((names.map (var (n := 0))).map (fun a => σ * a))
        ((closeMany names body).castScope (by simp)) :=
      instantiate_cast_eq (images.trans hargs.symm) _ _ _
    _ = σ * body := by simpa only [actSb_castScope, hc, castScope_trans] using h.symm

end SourceRuntime.Source

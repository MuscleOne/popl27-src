import SourceRuntime.Runtime.Syntax

/-!
Runtime-calculus.md §3: source-variable binding and atom substitution preserve
runtime phrase formation at the same U. The operations themselves come from WSLN.
The proofs follow the source category proofs, with the extra constant future case.
Scope weakening concerns bound source-variable indices; it does not enlarge U.
-/

namespace SourceRuntime.Runtime

open WSLN

mutual
theorem IsValue.weaken {U m n} {v : RawTerm m} (hv : IsValue U v) (h : m ≤ n) :
    IsValue U (v.weaken n h) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .future hp => exact .future hp
  | .funE first rest result hb =>
      exact .funE first rest result (hb.weaken (Nat.add_le_add_right h _))
  | .fixE first rest result hb =>
      exact .fixE first rest result (hb.weaken (Nat.add_le_add_right h _))
  | .sexp_int hp => exact .sexp_int (hp.weaken h)
  | .sexp_bool hp => exact .sexp_bool (hp.weaken h)
  | .sexp_id hp => exact .sexp_id (hp.weaken h)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.weaken h) (hb.weaken h)
termination_by structural hv

theorem IsAtom.weaken {U m n} {a : RawTerm m} (ha : IsAtom U a) (h : m ≤ n) :
    IsAtom U (a.weaken n h) := by
  match ha with
  | .bound i => exact .bound (Fin.castLE h i)
  | .free x => exact .free x
  | .value hv => exact .value (hv.weaken h)
termination_by structural ha

theorem IsTerm.weaken {U m n} {t : RawTerm m} (ht : IsTerm U t) (h : m ≤ n) :
    IsTerm U (t.weaken n h) := by
  match ht with
  | .atom ha => exact .atom (ha.weaken h)
  | .app hf ha hs => exact .app (hf.weaken h) (ha.weaken h) (hs.weaken h)
  | .operation op ha hb => exact .operation op (ha.weaken h) (hb.weaken h)
  | .ifE hg hy hn => exact .ifE (hg.weaken h) (hy.weaken h) (hn.weaken h)
  | .async hb => exact .async (hb.weaken h)
  | .letE hr hb => exact .letE (hr.weaken h) (hb.weaken (Nat.add_le_add_right h 1))
  | .matchE ha hs hf => exact .matchE (ha.weaken h) (hs.weaken h) hf
termination_by structural ht

theorem IsAtoms.weaken {U m n ms} {args : Arg signature m ms} (hs : IsAtoms U args) (h : m ≤ n) :
    IsAtoms U (args.weaken n h) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.weaken h) (hs.weaken h)
termination_by structural hs

theorem IsBranch.weaken {U m n p} {b : RawTerm m} (hb : IsBranch U p b) (h : m ≤ n) :
    IsBranch U p (b.weaken n h) := by
  match hb with
  | .branch ht => exact .branch (ht.weaken (Nat.add_le_add_right h _))
termination_by structural hb

theorem IsBranches.weaken {U m n ps ms} {bs : Arg signature m ms}
    (hs : IsBranches U ps bs) (h : m ≤ n) : IsBranches U ps (bs.weaken n h) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.weaken h) (hs.weaken h)
termination_by structural hs

end

mutual
theorem IsValue.subst {U n} {v : RawTerm n} (hv : IsValue U v)
    {σ : Sb signature} (hσ : ∀ x, IsAtom U (σ x)) : IsValue U (σ * v) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .future hp => exact .future hp
  | .funE first rest result hb => exact .funE first rest result (hb.subst hσ)
  | .fixE first rest result hb => exact .fixE first rest result (hb.subst hσ)
  | .sexp_int hp => exact .sexp_int (hp.subst hσ)
  | .sexp_bool hp => exact .sexp_bool (hp.subst hσ)
  | .sexp_id hp => exact .sexp_id (hp.subst hσ)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.subst hσ) (hb.subst hσ)
termination_by structural hv

theorem IsAtom.subst {U n} {a : RawTerm n} (ha : IsAtom U a)
    {σ : Sb signature} (hσ : ∀ x, IsAtom U (σ x)) : IsAtom U (σ * a) := by
  match ha with
  | .bound i => exact .bound i
  | .free x => exact (hσ x).weaken (Nat.zero_le n)
  | .value hv => exact .value (hv.subst hσ)
termination_by structural ha

theorem IsTerm.subst {U n} {t : RawTerm n} (ht : IsTerm U t)
    {σ : Sb signature} (hσ : ∀ x, IsAtom U (σ x)) : IsTerm U (σ * t) := by
  match ht with
  | .atom ha => exact .atom (ha.subst hσ)
  | .app hf ha hs => exact .app (hf.subst hσ) (ha.subst hσ) (hs.subst hσ)
  | .operation op ha hb => exact .operation op (ha.subst hσ) (hb.subst hσ)
  | .ifE hg hy hn => exact .ifE (hg.subst hσ) (hy.subst hσ) (hn.subst hσ)
  | .async hb => exact .async (hb.subst hσ)
  | .letE hr hb => exact .letE (hr.subst hσ) (hb.subst hσ)
  | .matchE ha hs hf => exact .matchE (ha.subst hσ) (hs.subst hσ) hf
termination_by structural ht

theorem IsAtoms.subst {U n ms} {args : Arg signature n ms} (hs : IsAtoms U args)
    {σ : Sb signature} (hσ : ∀ x, IsAtom U (σ x)) : IsAtoms U (σ * args) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.subst hσ) (hs.subst hσ)
termination_by structural hs

theorem IsBranch.subst {U n p} {b : RawTerm n} (hb : IsBranch U p b)
    {σ : Sb signature} (hσ : ∀ x, IsAtom U (σ x)) : IsBranch U p (σ * b) := by
  match hb with
  | .branch ht => exact .branch (ht.subst hσ)
termination_by structural hb

theorem IsBranches.subst {U n ps ms} {bs : Arg signature n ms} (hs : IsBranches U ps bs)
    {σ : Sb signature} (hσ : ∀ x, IsAtom U (σ x)) : IsBranches U ps (σ * bs) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.subst hσ) (hs.subst hσ)
termination_by structural hs

end

/-- A single atom replacement is an instance of the simultaneous operation. -/
theorem atom_substitution {U} (x : WSLN.Atom) {a : RawTerm 0} (ha : IsAtom U a) :
    ∀ y, IsAtom U (((x ≔ a) : Sb signature) y) := by
  intro y
  by_cases h : x = y
  · subst y; simpa using ha
  · rw [Sb.single_neq a h]; exact .free y

mutual
theorem IsValue.close {U m n} {v : RawTerm m} (hv : IsValue U v)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsValue U (cls x i v e) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .future hp => exact .future hp
  | .funE first rest result hb =>
      exact .funE first rest result (hb.close x (shiftIdx (rest.length + 1) i) (by omega))
  | .fixE first rest result hb =>
      exact .fixE first rest result (hb.close x (shiftIdx (rest.length + 2) i) (by omega))
  | .sexp_int hp => exact .sexp_int (hp.close x (shiftIdx 0 i) e)
  | .sexp_bool hp => exact .sexp_bool (hp.close x (shiftIdx 0 i) e)
  | .sexp_id hp => exact .sexp_id (hp.close x (shiftIdx 0 i) e)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.close x (shiftIdx 0 i) e) (hb.close x (shiftIdx 0 i) e)
termination_by structural hv

theorem IsAtom.close {U m n} {a : RawTerm m} (ha : IsAtom U a)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsAtom U (cls x i a e) := by
  match ha with
  | .bound j => exact .bound _
  | .free y =>
      change IsAtom U (if x = y then .var i else var y)
      split
      · exact .bound i
      · exact .free y
  | .value hv => exact .value (hv.close x i e)
termination_by structural ha

theorem IsTerm.close {U m n} {t : RawTerm m} (ht : IsTerm U t)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsTerm U (cls x i t e) := by
  match ht with
  | .atom ha => exact .atom (ha.close x i e)
  | .app hf ha hs =>
      exact .app (hf.close x (shiftIdx 0 i) e) (ha.close x (shiftIdx 0 i) e) (hs.close x i e)
  | .operation op ha hb => exact .operation op (ha.close x (shiftIdx 0 i) e) (hb.close x (shiftIdx 0 i) e)
  | .ifE hg hy hn =>
      exact .ifE (hg.close x (shiftIdx 0 i) e)
        (hy.close x (shiftIdx 0 i) e) (hn.close x (shiftIdx 0 i) e)
  | .async hb => exact .async (hb.close x (shiftIdx 0 i) e)
  | .letE hr hb => exact .letE (hr.close x (shiftIdx 0 i) e) (hb.close x (shiftIdx 1 i) (by omega))
  | .matchE ha hs hf => exact .matchE (ha.close x (shiftIdx 0 i) e) (hs.close x i e) hf
termination_by structural ht

theorem IsAtoms.close {U m n ms} {args : Arg signature m ms} (hs : IsAtoms U args)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsAtoms U (clsArg x i args e) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.close x (shiftIdx 0 i) e) (hs.close x i e)
termination_by structural hs

theorem IsBranch.close {U m n p} {b : RawTerm m} (hb : IsBranch U p b)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsBranch U p (cls x i b e) := by
  match hb with
  | .branch ht => exact .branch (ht.close x (shiftIdx p.arity i) (by omega))
termination_by structural hb

theorem IsBranches.close {U m n ps ms} {bs : Arg signature m ms} (hs : IsBranches U ps bs)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsBranches U ps (clsArg x i bs e) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.close x (shiftIdx 0 i) e) (hs.close x i e)
termination_by structural hs

end

theorem IsTerm.let_ {U} (x : WSLN.Atom) {rhs body : RawTerm 0}
    (hr : IsTerm U rhs) (hb : IsTerm U body) : IsTerm U (let_ x rhs body) :=
  .letE hr (hb.close x ⟨0, by omega⟩ rfl)

mutual
theorem IsValue.open {U m n} {v : RawTerm m} (hv : IsValue U v)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom U a) (e : m = n + 1) :
    IsValue U (opn i a v e) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .future hp => exact .future hp
  | .funE first rest result hb =>
      exact .funE first rest result (hb.open (shiftIdx (rest.length + 1) i) ha (by omega))
  | .fixE first rest result hb =>
      exact .fixE first rest result (hb.open (shiftIdx (rest.length + 2) i) ha (by omega))
  | .sexp_int hp => exact .sexp_int (hp.open (shiftIdx 0 i) ha e)
  | .sexp_bool hp => exact .sexp_bool (hp.open (shiftIdx 0 i) ha e)
  | .sexp_id hp => exact .sexp_id (hp.open (shiftIdx 0 i) ha e)
  | .nil => exact .nil
  | .pair hb hc => exact .pair (hb.open (shiftIdx 0 i) ha e) (hc.open (shiftIdx 0 i) ha e)
termination_by structural hv

theorem IsAtom.open {U m n} {b : RawTerm m} (hb : IsAtom U b)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom U a) (e : m = n + 1) :
    IsAtom U (opn i a b e) := by
  match hb with
  | .bound j =>
      rw [opn_var]
      split
      · exact ha.weaken (Nat.zero_le n)
      · exact .bound _
  | .free x => exact .free x
  | .value hv => exact .value (hv.open i ha e)
termination_by structural hb

theorem IsTerm.open {U m n} {t : RawTerm m} (ht : IsTerm U t)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom U a) (e : m = n + 1) :
    IsTerm U (opn i a t e) := by
  match ht with
  | .atom hb => exact .atom (hb.open i ha e)
  | .app hf hb hs =>
      exact .app (hf.open (shiftIdx 0 i) ha e) (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e)
  | .operation op hb hc => exact .operation op (hb.open (shiftIdx 0 i) ha e) (hc.open (shiftIdx 0 i) ha e)
  | .ifE hg hy hn =>
      exact .ifE (hg.open (shiftIdx 0 i) ha e)
        (hy.open (shiftIdx 0 i) ha e) (hn.open (shiftIdx 0 i) ha e)
  | .async hb => exact .async (hb.open (shiftIdx 0 i) ha e)
  | .letE hr hb => exact .letE (hr.open (shiftIdx 0 i) ha e) (hb.open (shiftIdx 1 i) ha (by omega))
  | .matchE hb hs hf => exact .matchE (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e) hf
termination_by structural ht

theorem IsAtoms.open {U m n ms} {args : Arg signature m ms} (hs : IsAtoms U args)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom U a) (e : m = n + 1) :
    IsAtoms U (opnArg i a args e) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e)
termination_by structural hs

theorem IsBranch.open {U m n p} {b : RawTerm m} (hb : IsBranch U p b)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom U a) (e : m = n + 1) :
    IsBranch U p (opn i a b e) := by
  match hb with
  | .branch ht => exact .branch (ht.open (shiftIdx p.arity i) ha (by omega))
termination_by structural hb

theorem IsBranches.open {U m n ps ms} {bs : Arg signature m ms} (hs : IsBranches U ps bs)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom U a) (e : m = n + 1) :
    IsBranches U ps (opnArg i a bs e) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e)
termination_by structural hs

end

theorem IsTerm.conc {U} {body : RawTerm 1} (hb : IsTerm U body)
    {a : RawTerm 0} (ha : IsAtom U a) : IsTerm U (body.conc a) :=
  hb.open ⟨0, by omega⟩ ha rfl

/-- Instantiate the same ordered slots. Inserted free names remain free. -/
def instantiate (args : List (RawTerm 0)) (body : RawTerm args.length) : RawTerm 0 :=
  match args with
  | [] => body
  | a :: rest => instantiate rest (body.conc a)

@[simp] theorem castScope_trans {m n k} (e : m = n) (f : n = k) (t : RawTerm m) :
    (t.castScope e).castScope f = t.castScope (e.trans f) := by
  cases e; cases f; rfl

/-- Transport formation across equal binder counts. -/
theorem IsTerm.castScope {U m n} {t : RawTerm m} (ht : IsTerm U t) (e : m = n) :
    IsTerm U (t.castScope e) := by cases e; exact ht

/-- Instantiating all binder slots with formed atoms preserves the term grammar. -/
theorem IsTerm.instantiate {U} (args : List (RawTerm 0)) {body : RawTerm args.length}
    (hb : IsTerm U body) (ha : ∀ a ∈ args, IsAtom U a) : IsTerm U (instantiate args body) := by
  induction args with
  | nil => exact hb
  | cons a rest ih =>
      exact ih (hb.open _ (ha a (by simp)) rfl) (fun v h => ha v (by simp [h]))

/-- Encode the paper's ordered operand sequence in WSLN's argument spine. -/
def toArgs {n : Nat} (as : List (RawTerm n)) : RawArgs n as.length :=
  match as with
  | [] => .nil
  | a :: rest => .cons a (toArgs rest)

end SourceRuntime.Runtime

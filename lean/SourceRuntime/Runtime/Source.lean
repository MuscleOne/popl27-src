import SourceRuntime.Runtime.Typing

/-!
Runtime-calculus.md §2.2 identifies the source carriers with the runtime carriers
at empty U. The two WSLN signatures require a structural conversion in Lean:
it only wraps operator labels and preserves every variable index and binder.
This conversion is not a runtime transition or an observation operation.
-/

namespace SourceRuntime.Runtime

open WSLN

mutual
def ofSource {n} (t : Source.RawTerm n) : RawTerm n :=
  match t with
  | .var i => .var i
  | .atom x => .atom x
  | .op o args => .op (.source o) (ofSourceArgs args)

def ofSourceArgs {n ms} (args : Arg Source.signature n ms) : Arg signature n ms :=
  match args with
  | .nil => .nil
  | .cons t rest => .cons (ofSource t) (ofSourceArgs rest)
end

mutual
/-- Distinct source trees remain distinct after conversion. -/
theorem ofSource_injective {n} (t u : Source.RawTerm n) (h : ofSource t = ofSource u) : t = u := by
  match t, u with
  | .var i, .var j => cases h; rfl
  | .atom x, .atom y => cases h; rfl
  | .op o args, .op o' args' =>
      have ⟨ho, hs⟩ := Trm.op.inj h
      cases Op.source.inj ho
      exact congrArg (Trm.op o) (ofSourceArgs_injective args args' (eq_of_heq hs))
  | .var _, .atom _ | .var _, .op _ _ | .atom _, .var _
  | .atom _, .op _ _ | .op _ _, .var _ | .op _ _, .atom _ => cases h
termination_by structural t

theorem ofSourceArgs_injective {n ms} (args rest : Arg Source.signature n ms)
    (h : ofSourceArgs args = ofSourceArgs rest) : args = rest := by
  match args, rest with
  | .nil, .nil => rfl
  | .cons t ts, .cons u us =>
      have ⟨ht, hs⟩ := Arg.cons.inj h
      rw [ofSource_injective t u ht, ofSourceArgs_injective ts us hs]
termination_by structural args
end

-- Converting a binder and then instantiating it gives the converted source result.
mutual
theorem ofSource_weaken {m n} (t : Source.RawTerm m) (h : m ≤ n) :
    ofSource (t.weaken n h) = (ofSource t).weaken n h := by
  match t with
  | .var _ | .atom _ => rfl
  | .op o args => exact congrArg (Trm.op (Sg := signature) (.source o)) (ofSourceArgs_weaken args h)
termination_by structural t

theorem ofSourceArgs_weaken {m n ms} (args : Arg Source.signature m ms) (h : m ≤ n) :
    ofSourceArgs (args.weaken n h) = (ofSourceArgs args).weaken n h := by
  match args with
  | .nil => rfl
  | .cons t rest =>
      change Arg.cons (ofSource (t.weaken _ _)) (ofSourceArgs (rest.weaken n h)) = _
      rw [ofSource_weaken, ofSourceArgs_weaken]
      rfl
termination_by structural args
end

mutual
theorem ofSource_open {m n} (t : Source.RawTerm m) (i : Fin m) (a : Source.RawTerm 0)
    (e : m = n + 1) : ofSource (opn i a t e) = opn i (ofSource a) (ofSource t) e := by
  match t with
  | .var j =>
      by_cases h : i = j
      · subst j; simp only [opn_var_eq, ofSource, ofSource_weaken]
      · simp only [opn_var_ne a e h, ofSource, opn_var_ne (ofSource a) e h]
  | .atom _ => rfl
  | .op o args => exact congrArg (Trm.op (Sg := signature) (.source o)) (ofSourceArgs_open args i a e)
termination_by structural t

theorem ofSourceArgs_open {m n ms} (args : Arg Source.signature m ms) (i : Fin m)
    (a : Source.RawTerm 0) (e : m = n + 1) :
    ofSourceArgs (opnArg i a args e) = opnArg i (ofSource a) (ofSourceArgs args) e := by
  match args with
  | .nil => rfl
  | .cons t rest =>
      change Arg.cons (ofSource (opn _ a t _)) (ofSourceArgs (opnArg i a rest e)) = _
      rw [ofSource_open, ofSourceArgs_open]
      rfl
termination_by structural args
end

@[simp] theorem ofSource_conc {n} (body : Source.RawTerm (n + 1)) (a : Source.RawTerm 0) :
    ofSource (body.conc a) = (ofSource body).conc (ofSource a) :=
  ofSource_open body _ a rfl

@[simp] theorem ofSource_castScope {m n} (body : Source.RawTerm m) (e : m = n) :
    ofSource (body.castScope e) = (ofSource body).castScope e := by cases e; rfl

theorem ofSource_instantiate (args : List (Source.RawTerm 0)) (body : Source.RawTerm args.length) :
    ofSource (Source.instantiate args body) =
      instantiate (args.map ofSource) ((ofSource body).castScope (by simp)) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      simp only [Source.instantiate, List.map_cons, instantiate]
      rw [ih, ofSource_conc]
      have hc {m n} (e : m = n) (b : RawTerm (m + 1)) (v : RawTerm 0) :
          (b.castScope (congrArg (· + 1) e)).conc v = (b.conc v).castScope e := by
        cases e; rfl
      rw [hc]

private theorem args_cons_heq {n m ms ns} (e : ms = ns) (t : RawTerm (n + m))
    (args : Arg signature n ms) (rest : Arg signature n ns) (h : HEq args rest) :
    HEq (Arg.cons t args) (Arg.cons t rest) := by
  cases e; cases h; rfl

private theorem ofSource_toArgs {n} (args : List (Source.RawTerm n)) :
    HEq (ofSourceArgs (Source.toArgs args)) (toArgs (args.map ofSource)) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      exact args_cons_heq (n := n) (m := 0) (by simp) (ofSource a) _ _ ih

theorem ofSource_app {n} (fn first : Source.RawTerm n) (rest : List (Source.RawTerm n)) :
    ofSource (Source.app fn first (Source.toArgs rest)) =
      app (ofSource fn) (ofSource first) (toArgs (rest.map ofSource)) := by
  have h := args_cons_heq (n := n) (m := 0) (by simp) (ofSource fn) _ _
    (args_cons_heq (n := n) (m := 0) (by simp) (ofSource first) _ _ (ofSource_toArgs rest))
  have op_eq {o o' : Op} (e : o = o') (args : Arg signature n (signature.ar o))
      (args' : Arg signature n (signature.ar o')) (he : HEq args args') :
      Trm.op (Sg := signature) o args = Trm.op (Sg := signature) o' args' := by cases e; cases he; rfl
  exact op_eq (by simp) _ _ h

-- Source phrases contain no futures, so they are formed at every active-name set.
mutual
theorem ofSource_value {U n v} (hv : Source.IsValue (n := n) v) :
    IsValue U (ofSource v) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE first rest result hb => exact .funE first rest result (ofSource_term hb)
  | .fixE first rest result hb => exact .fixE first rest result (ofSource_term hb)
  | .sexp_int ha => exact .sexp_int (ofSource_atom ha)
  | .sexp_bool ha => exact .sexp_bool (ofSource_atom ha)
  | .sexp_id ha => exact .sexp_id (ofSource_atom ha)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ofSource_atom ha) (ofSource_atom hb)
termination_by structural hv

theorem ofSource_atom {U n a} (ha : Source.IsAtom (n := n) a) : IsAtom U (ofSource a) := by
  match ha with
  | .bound i => exact .bound i
  | .free x => exact .free x
  | .value hv => exact .value (ofSource_value hv)
termination_by structural ha

theorem ofSource_term {U n t} (ht : Source.IsTerm (n := n) t) : IsTerm U (ofSource t) := by
  match ht with
  | .atom ha => exact .atom (ofSource_atom ha)
  | .app hf ha hs => exact .app (ofSource_atom hf) (ofSource_atom ha) (ofSource_atoms hs)
  | .operation op ha hb => exact .operation op (ofSource_atom ha) (ofSource_atom hb)
  | .ifE hg hy hn => exact .ifE (ofSource_atom hg) (ofSource_term hy) (ofSource_term hn)
  | .letE hr hb => exact .letE (ofSource_term hr) (ofSource_term hb)
  | .matchE ha hs hf => exact .matchE (ofSource_atom ha) (ofSource_branches hs) hf
  | .async hb => exact .async (ofSource_term hb)
termination_by structural ht

theorem ofSource_branch {U n p b} (hb : Source.IsBranch p (n := n) b) :
    IsBranch U p (ofSource b) := by
  match hb with
  | .branch ht => exact .branch (ofSource_term ht)
termination_by structural hb

theorem ofSource_branches {U n ps ms bs} (hs : Source.IsBranches ps (n := n) (ms := ms) bs) :
    IsBranches U ps (ofSourceArgs bs) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (ofSource_branch hb) (ofSource_branches hs)
termination_by structural hs

theorem ofSource_atoms {U n ms args} (hs : Source.IsAtoms (n := n) (ms := ms) args) :
    IsAtoms U (ofSourceArgs args) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ofSource_atom ha) (ofSource_atoms hs)
termination_by structural hs
end

-- Empty U excludes the future case even in function bodies, fields and branches.
mutual
theorem IsValue.source_of_empty {n v} (hv : IsValue ∅ (n := n) v) :
    ∃ s, Source.IsValue s ∧ ofSource s = v := by
  match hv with
  | .integer z => exact ⟨Source.integer z, .integer z, rfl⟩
  | .boolean b => exact ⟨Source.boolean b, .boolean b, rfl⟩
  | .unit => exact ⟨Source.unit, .unit, rfl⟩
  | .identifier i => exact ⟨Source.identifier i, .identifier i, rfl⟩
  | .future hp => exact False.elim (Std.ExtTreeSet.not_mem_empty hp)
  | .funE first rest result hb =>
      obtain ⟨body, hb', rfl⟩ := hb.source_of_empty
      exact ⟨Source.funE first rest result body, .funE first rest result hb', rfl⟩
  | .fixE first rest result hb =>
      obtain ⟨body, hb', rfl⟩ := hb.source_of_empty
      exact ⟨Source.fixE first rest result body, .fixE first rest result hb', rfl⟩
  | .sexp_int ha =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      exact ⟨Source.sexp_int a, .sexp_int ha', rfl⟩
  | .sexp_bool ha =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      exact ⟨Source.sexp_bool a, .sexp_bool ha', rfl⟩
  | .sexp_id ha =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      exact ⟨Source.sexp_id a, .sexp_id ha', rfl⟩
  | .nil => exact ⟨Source.nil, .nil, rfl⟩
  | .pair ha hb =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      obtain ⟨b, hb', rfl⟩ := hb.source_of_empty
      exact ⟨Source.pair a b, .pair ha' hb', rfl⟩
termination_by structural hv

theorem IsAtom.source_of_empty {n a} (ha : IsAtom ∅ (n := n) a) :
    ∃ s, Source.IsAtom s ∧ ofSource s = a := by
  match ha with
  | .bound i => exact ⟨.var i, .bound i, rfl⟩
  | .free x => exact ⟨Source.var x, .free x, rfl⟩
  | .value hv =>
      obtain ⟨v, hv', rfl⟩ := hv.source_of_empty
      exact ⟨v, .value hv', rfl⟩
termination_by structural ha

theorem IsTerm.source_of_empty {n t} (ht : IsTerm ∅ (n := n) t) :
    ∃ s, Source.IsTerm s ∧ ofSource s = t := by
  match ht with
  | .atom ha =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      exact ⟨a, .atom ha', rfl⟩
  | .app hf ha hs =>
      obtain ⟨fn, hf', rfl⟩ := hf.source_of_empty
      obtain ⟨first, ha', rfl⟩ := ha.source_of_empty
      obtain ⟨rest, hs', rfl⟩ := hs.source_of_empty
      exact ⟨Source.app fn first rest, .app hf' ha' hs', rfl⟩
  | .operation op ha hb =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      obtain ⟨b, hb', rfl⟩ := hb.source_of_empty
      exact ⟨Source.operation op a b, .operation op ha' hb', rfl⟩
  | .ifE hg hy hn =>
      obtain ⟨guard, hg', rfl⟩ := hg.source_of_empty
      obtain ⟨yes, hy', rfl⟩ := hy.source_of_empty
      obtain ⟨no, hn', rfl⟩ := hn.source_of_empty
      exact ⟨Source.ifE guard yes no, .ifE hg' hy' hn', rfl⟩
  | .letE hr hb =>
      obtain ⟨rhs, hr', rfl⟩ := hr.source_of_empty
      obtain ⟨body, hb', rfl⟩ := hb.source_of_empty
      exact ⟨Source.letE rhs body, .letE hr' hb', rfl⟩
  | .matchE ha hs hf =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      obtain ⟨branches, hs', rfl⟩ := hs.source_of_empty
      exact ⟨Source.matchE a branches, .matchE ha' hs' hf, rfl⟩
  | .async hb =>
      obtain ⟨body, hb', rfl⟩ := hb.source_of_empty
      exact ⟨Source.async body, .async hb', rfl⟩
termination_by structural ht

theorem IsBranch.source_of_empty {n p b} (hb : IsBranch ∅ p (n := n) b) :
    ∃ s, Source.IsBranch p s ∧ ofSource s = b := by
  match hb with
  | .branch ht =>
      obtain ⟨body, ht', rfl⟩ := ht.source_of_empty
      exact ⟨Source.branch p body, .branch ht', rfl⟩
termination_by structural hb

theorem IsBranches.source_of_empty {n ps ms bs} (hs : IsBranches ∅ ps (n := n) (ms := ms) bs) :
    ∃ ss, Source.IsBranches ps ss ∧ ofSourceArgs ss = bs := by
  match hs with
  | .nil => exact ⟨.nil, .nil, rfl⟩
  | .cons hb hs =>
      obtain ⟨b, hb', rfl⟩ := hb.source_of_empty
      obtain ⟨rest, hs', rfl⟩ := hs.source_of_empty
      exact ⟨.cons b rest, .cons hb' hs', rfl⟩
termination_by structural hs

theorem IsAtoms.source_of_empty {n ms args} (hs : IsAtoms ∅ (n := n) (ms := ms) args) :
    ∃ ss, Source.IsAtoms ss ∧ ofSourceArgs ss = args := by
  match hs with
  | .nil => exact ⟨.nil, .nil, rfl⟩
  | .cons ha hs =>
      obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
      obtain ⟨rest, hs', rfl⟩ := hs.source_of_empty
      exact ⟨.cons a rest, .cons ha' hs', rfl⟩
termination_by structural hs
end

-- R-Empty: preserve typing on entry and recover source typing at empty Σ.
mutual
theorem ofSource_typing {sig Γ n Δ t A} (h : Source.Typing Γ (n := n) Δ t A) :
    Typing sig Γ Δ (ofSource t) A := by
  match h with
  | .bound i => exact .bound i
  | .free hx => exact .free hx
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE hb => exact .funE (ofSource_typing hb)
  | .fixE hb => exact .fixE (ofSource_typing hb)
  | .sexp_int ha ht => exact .sexp_int (ofSource_atom ha) (ofSource_typing ht)
  | .sexp_bool ha ht => exact .sexp_bool (ofSource_atom ha) (ofSource_typing ht)
  | .sexp_id ha ht => exact .sexp_id (ofSource_atom ha) (ofSource_typing ht)
  | .nil => exact .nil
  | .pair ha hb ht hu => exact .pair (ofSource_atom ha) (ofSource_atom hb) (ofSource_typing ht) (ofSource_typing hu)
  | .app hf ha ht hu hs => exact .app (ofSource_atom hf) (ofSource_atom ha) (ofSource_typing ht) (ofSource_typing hu) (ofSource_args_typing hs)
  | .arith hop ha hb ht hu => exact .arith hop (ofSource_atom ha) (ofSource_atom hb) (ofSource_typing ht) (ofSource_typing hu)
  | .eq hA ha hb ht hu => exact .eq hA (ofSource_atom ha) (ofSource_atom hb) (ofSource_typing ht) (ofSource_typing hu)
  | .lt ha hb ht hu => exact .lt (ofSource_atom ha) (ofSource_atom hb) (ofSource_typing ht) (ofSource_typing hu)
  | .ifE hg ht hy hn => exact .ifE (ofSource_atom hg) (ofSource_typing ht) (ofSource_typing hy) (ofSource_typing hn)
  | .letE hr hb => exact .letE (ofSource_typing hr) (ofSource_typing hb)
  | .matchE ha ht hs hf => exact .matchE (ofSource_atom ha) (ofSource_typing ht) (ofSource_branches_typing hs) hf
  | .async hb => exact .async (ofSource_typing hb)
termination_by structural h

theorem ofSource_branch_typing {sig Γ n Δ p b A} (h : Source.BranchTyping Γ (n := n) Δ p b A) :
    BranchTyping sig Γ Δ p (ofSource b) A := by
  match h with
  | .int hb => exact .int (ofSource_typing hb)
  | .bool hb => exact .bool (ofSource_typing hb)
  | .id hb => exact .id (ofSource_typing hb)
  | .nil hb => exact .nil (ofSource_typing hb)
  | .pair hb => exact .pair (ofSource_typing hb)
  | .wildcard hb => exact .wildcard (ofSource_typing hb)
termination_by structural h

theorem ofSource_args_typing {sig Γ n Δ As ms args}
    (h : Source.ArgsTyping Γ (n := n) Δ As (ms := ms) args) :
    ArgsTyping sig Γ Δ As (ofSourceArgs args) := by
  match h with
  | .nil => exact .nil
  | .cons ha ht hs => exact .cons (ofSource_atom ha) (ofSource_typing ht) (ofSource_args_typing hs)
termination_by structural h

theorem ofSource_branches_typing {sig Γ n Δ ps ms bs A}
    (h : Source.BranchesTyping Γ (n := n) Δ ps (ms := ms) bs A) :
    BranchesTyping sig Γ Δ ps (ofSourceArgs bs) A := by
  match h with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (ofSource_branch_typing hb) (ofSource_branches_typing hs)
termination_by structural h
end

private theorem source_atom {n a} (h : IsAtom (domain (∅ : Signature)) (n := n) (ofSource a)) :
    Source.IsAtom a := by
  obtain ⟨s, hs, he⟩ := (show IsAtom ∅ (ofSource a) by simpa using h).source_of_empty
  cases ofSource_injective s a he
  exact hs

mutual
theorem Typing.source_of_empty {Γ n Δ t A} (h : Typing ∅ Γ (n := n) Δ t A) :
    ∃ s, Source.Typing Γ Δ s A ∧ ofSource s = t := by
  match h with
  | .bound i => exact ⟨.var i, .bound i, rfl⟩
  | .free hx => exact ⟨Source.var _, .free hx, rfl⟩
  | .future hp => simp at hp
  | .integer z => exact ⟨Source.integer z, .integer z, rfl⟩
  | .boolean b => exact ⟨Source.boolean b, .boolean b, rfl⟩
  | .unit => exact ⟨Source.unit, .unit, rfl⟩
  | .identifier i => exact ⟨Source.identifier i, .identifier i, rfl⟩
  | .funE hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.funE _ _ _ b, .funE hbs, rfl⟩
  | .fixE hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.fixE _ _ _ b, .fixE hbs, rfl⟩
  | .sexp_int ha ht =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      exact ⟨Source.sexp_int a, .sexp_int (source_atom ha) hts, rfl⟩
  | .sexp_bool ha ht =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      exact ⟨Source.sexp_bool a, .sexp_bool (source_atom ha) hts, rfl⟩
  | .sexp_id ha ht =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      exact ⟨Source.sexp_id a, .sexp_id (source_atom ha) hts, rfl⟩
  | .nil => exact ⟨Source.nil, .nil, rfl⟩
  | .pair ha hb ht hu =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨b, hus, rfl⟩ := hu.source_of_empty
      exact ⟨Source.pair a b, .pair (source_atom ha) (source_atom hb) hts hus, rfl⟩
  | .app hf ha ht hu hs =>
      obtain ⟨f, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨a, hus, rfl⟩ := hu.source_of_empty
      obtain ⟨args, hss, rfl⟩ := hs.source_of_empty
      exact ⟨Source.app f a args, .app (source_atom hf) (source_atom ha) hts hus hss, rfl⟩
  | .arith hop ha hb ht hu =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨b, hus, rfl⟩ := hu.source_of_empty
      exact ⟨Source.operation _ a b, .arith hop (source_atom ha) (source_atom hb) hts hus, rfl⟩
  | .eq hA ha hb ht hu =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨b, hus, rfl⟩ := hu.source_of_empty
      exact ⟨Source.operation .eq a b, .eq hA (source_atom ha) (source_atom hb) hts hus, rfl⟩
  | .lt ha hb ht hu =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨b, hus, rfl⟩ := hu.source_of_empty
      exact ⟨Source.operation .lt a b, .lt (source_atom ha) (source_atom hb) hts hus, rfl⟩
  | .ifE hg ht hy hn =>
      obtain ⟨g, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨y, hys, rfl⟩ := hy.source_of_empty
      obtain ⟨z, hns, rfl⟩ := hn.source_of_empty
      exact ⟨Source.ifE g y z, .ifE (source_atom hg) hts hys hns, rfl⟩
  | .letE hr hb =>
      obtain ⟨r, hrs, rfl⟩ := hr.source_of_empty
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.letE r b, .letE hrs hbs, rfl⟩
  | .matchE ha ht hs hf =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨bs, hss, rfl⟩ := hs.source_of_empty
      exact ⟨Source.matchE a bs, .matchE (source_atom ha) hts hss hf, rfl⟩
  | .async hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.async b, .async hbs, rfl⟩
termination_by structural h

theorem BranchTyping.source_of_empty {Γ n Δ p b A} (h : BranchTyping ∅ Γ (n := n) Δ p b A) :
    ∃ s, Source.BranchTyping Γ Δ p s A ∧ ofSource s = b := by
  match h with
  | .int hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.branch .int b, .int hbs, rfl⟩
  | .bool hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.branch .bool b, .bool hbs, rfl⟩
  | .id hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.branch .id b, .id hbs, rfl⟩
  | .nil hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.branch .nil b, .nil hbs, rfl⟩
  | .pair hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.branch .pair b, .pair hbs, rfl⟩
  | .wildcard hb =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      exact ⟨Source.branch .wildcard b, .wildcard hbs, rfl⟩
termination_by structural h

theorem ArgsTyping.source_of_empty {Γ n Δ As ms args}
    (h : ArgsTyping ∅ Γ (n := n) Δ As (ms := ms) args) :
    ∃ ss, Source.ArgsTyping Γ Δ As ss ∧ ofSourceArgs ss = args := by
  match h with
  | .nil => exact ⟨.nil, .nil, rfl⟩
  | .cons ha ht hs =>
      obtain ⟨a, hts, rfl⟩ := ht.source_of_empty
      obtain ⟨args, hss, rfl⟩ := hs.source_of_empty
      exact ⟨.cons a args, .cons (source_atom ha) hts hss, rfl⟩
termination_by structural h

theorem BranchesTyping.source_of_empty {Γ n Δ ps ms bs A}
    (h : BranchesTyping ∅ Γ (n := n) Δ ps (ms := ms) bs A) :
    ∃ ss, Source.BranchesTyping Γ Δ ps ss A ∧ ofSourceArgs ss = bs := by
  match h with
  | .nil => exact ⟨.nil, .nil, rfl⟩
  | .cons hb hs =>
      obtain ⟨b, hbs, rfl⟩ := hb.source_of_empty
      obtain ⟨bs, hss, rfl⟩ := hs.source_of_empty
      exact ⟨.cons b bs, .cons hbs hss, rfl⟩
termination_by structural h
end

theorem typing_empty_iff {Γ n Δ t A} :
    Typing ∅ Γ (n := n) Δ (ofSource t) A ↔ Source.Typing Γ Δ t A := by
  constructor
  · intro h
    obtain ⟨s, ht, he⟩ := h.source_of_empty
    cases ofSource_injective s t he
    exact ht
  · exact ofSource_typing

theorem branch_typing_empty_iff {Γ n Δ p b A} :
    BranchTyping ∅ Γ (n := n) Δ p (ofSource b) A ↔ Source.BranchTyping Γ Δ p b A := by
  constructor
  · intro h
    obtain ⟨s, ht, he⟩ := h.source_of_empty
    cases ofSource_injective s b he
    exact ht
  · exact ofSource_branch_typing

/-- S-Unique-Type, derived through empty-signature typing and runtime uniqueness. -/
theorem source_typing_unique {Γ n Δ t A B} (ha : Source.Typing Γ (n := n) Δ t A)
    (hb : Source.Typing Γ Δ t B) : A = B :=
  (ofSource_typing (sig := ∅) ha).unique (ofSource_typing hb)

/-- The branch clause of S-Unique-Type, using the same existing correspondence. -/
theorem source_branch_typing_unique {Γ n Δ p b A B} (ha : Source.BranchTyping Γ (n := n) Δ p b A)
    (hb : Source.BranchTyping Γ Δ p b B) : A = B :=
  (ofSource_branch_typing (sig := ∅) ha).unique (ofSource_branch_typing hb)

/-- The initial display; conversion only changes the internal operator signature. -/
def initialState (t : Source.RawTerm 0) (ht : Source.IsTerm t) : State where
  signature := ∅
  mapping := ∅
  focus := ofSource t
  domains := by simp
  focus_formed := ofSource_term ht
  entries_formed := by simp

/-- R-Initial-Ok follows from source typing at empty Σ. -/
theorem initial_ok {t A} (ht : Source.HasType [] t A) : (initialState t ht.formed).Ok :=
  ⟨rfl, ⟨A, ofSource_typing ht⟩, by simp [initialState]⟩

end SourceRuntime.Runtime

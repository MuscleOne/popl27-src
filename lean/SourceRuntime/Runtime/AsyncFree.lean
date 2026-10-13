import SourceRuntime.Runtime.Source
import SourceRuntime.Runtime.Reduction

/-!
C-Async-Free: source steps and runtime execution agree when the entire source tree
contains no async. The predicate traverses all WSLN children, including function
and branch bodies. No typing or source-variable closedness premise is used.
-/

namespace SourceRuntime.Runtime
open WSLN

mutual
/-- Absence of async in the whole tree; also used on embedded source terms. -/
def AsyncFree {n} : RawTerm n → Prop
  | .var _ | .atom _ => True
  | .op o args => o ≠ .source .async ∧ AsyncFreeArgs args

def AsyncFreeArgs {n ms} : Arg signature n ms → Prop
  | .nil => True
  | .cons t rest => AsyncFree t ∧ AsyncFreeArgs rest
end

mutual
private theorem asyncFree_weaken {m n} (t : RawTerm m) (h : m ≤ n)
    (ht : AsyncFree t) : AsyncFree (t.weaken n h) := by
  match t with
  | .var _ | .atom _ => trivial
  | .op _ args => exact ⟨ht.1, asyncFreeArgs_weaken args h ht.2⟩
termination_by structural t

private theorem asyncFreeArgs_weaken {m n ms} (args : Arg signature m ms) (h : m ≤ n)
    (hs : AsyncFreeArgs args) : AsyncFreeArgs (args.weaken n h) := by
  match args with
  | .nil => trivial
  | .cons t rest => exact ⟨asyncFree_weaken t _ hs.1, asyncFreeArgs_weaken rest h hs.2⟩
termination_by structural args
end

mutual
private theorem asyncFree_open {m n} (t : RawTerm m) (i : Fin m) (a : RawTerm 0)
    (e : m = n + 1) (ht : AsyncFree t) (ha : AsyncFree a) : AsyncFree (opn i a t e) := by
  match t with
  | .var j =>
      by_cases h : i = j
      · subst j; rw [opn_var_eq]; exact asyncFree_weaken a _ ha
      · rw [opn_var_ne a e h]; trivial
  | .atom _ => trivial
  | .op _ args => exact ⟨ht.1, asyncFreeArgs_open args i a e ht.2 ha⟩
termination_by structural t

private theorem asyncFreeArgs_open {m n ms} (args : Arg signature m ms) (i : Fin m)
    (a : RawTerm 0) (e : m = n + 1) (hs : AsyncFreeArgs args) (ha : AsyncFree a) :
    AsyncFreeArgs (opnArg i a args e) := by
  match args with
  | .nil => trivial
  | .cons t rest => exact ⟨asyncFree_open t _ a _ hs.1 ha, asyncFreeArgs_open rest i a e hs.2 ha⟩
termination_by structural args
end

private theorem asyncFree_conc {n} {body : RawTerm (n + 1)} {a : RawTerm 0}
    (hb : AsyncFree body) (ha : AsyncFree a) : AsyncFree (body.conc a) :=
  asyncFree_open body _ a rfl hb ha

private theorem asyncFree_castScope {m n} {t : RawTerm m} (e : m = n) (ht : AsyncFree t) :
    AsyncFree (t.castScope e) := by cases e; exact ht

private theorem asyncFree_instantiate (args : List (RawTerm 0)) {body : RawTerm args.length}
    (hb : AsyncFree body) (hs : ∀ a ∈ args, AsyncFree a) : AsyncFree (instantiate args body) := by
  induction args with
  | nil => exact hb
  | cons a rest ih =>
      exact ih (asyncFree_conc hb (hs a (by simp))) (fun b h => hs b (by simp [h]))

private theorem asyncFree_toArgs {n} (args : List (RawTerm n)) :
    AsyncFreeArgs (toArgs args) ↔ ∀ a ∈ args, AsyncFree a := by
  induction args with
  | nil => simp [toArgs, AsyncFreeArgs]
  | cons a rest ih => simp [toArgs, AsyncFreeArgs, ih]

private theorem ArgMember.asyncFree {a ms args} (h : ArgMember a (ms := ms) args)
    (hs : AsyncFreeArgs args) : AsyncFree a := by
  induction h with
  | here => exact hs.1
  | there _ ih => exact ih hs.2

private theorem MatchBranch.asyncFree {U v b result} (h : MatchBranch U v b result)
    (hv : AsyncFree v) (hb : AsyncFree b) : AsyncFree result := by
  cases h with
  | int | bool | id => exact asyncFree_conc hb.2.1 hv.2.1
  | nil => exact hb.2.1
  | pair => exact asyncFree_conc (asyncFree_conc hb.2.1 hv.2.1) hv.2.2.1

-- At empty μ, neither application spawning nor dereference can apply.
private theorem LocalStep.asyncFree_empty {sig mu t sig' mu' t'}
    (h : LocalStep sig mu t sig' mu' t') (hm : mu = ∅) (ha : AsyncFree t) : AsyncFree t' := by
  induction h with
  | search_let _ _ _ ih => exact ⟨ha.1, ih ha.2.1, ha.2.2⟩
  | beta arity hb hv hs =>
      exact asyncFree_instantiate _ (asyncFree_castScope _ ha.2.1.2.1) (by
        intro a h
        cases h with
        | head => exact ha.2.2.1
        | tail _ h => exact (asyncFree_toArgs _).mp ha.2.2.2 a h)
  | fix_beta arity hb hv hs =>
      exact asyncFree_instantiate _ (asyncFree_castScope _ ha.2.1.2.1) (by
        intro a h
        cases h with
        | head => exact ha.2.1
        | tail _ h => cases h with
          | head => exact ha.2.2.1
          | tail _ h => exact (asyncFree_toArgs _).mp ha.2.2.2 a h)
  | let_value => exact asyncFree_conc ha.2.2.1 ha.2.1
  | match_constructor hs hf hm hc => exact hc.asyncFree ha.2.1 (hm.asyncFree ha.2.2)
  | match_wildcard hv hc hn hs hf hm => exact (hm.asyncFree ha.2.2).2.1
  | if_true => exact ha.2.2.1
  | if_false => exact ha.2.2.2.1
  | spawn_async => exact False.elim (ha.1 rfl)
  | spawn_app hex _ _ _ =>
      obtain ⟨p, body, _, hp, _⟩ := hex
      simp [hm] at hp
  | deref_app hp _ | deref_op_left hp _ | deref_op_right hp _ | deref_if hp _ | deref_match hp _ => simp [hm] at hp
  | _ => exact ⟨(by intro e; cases e), trivial⟩

private theorem ofSource_member {b ms bs} (h : Source.BranchMember b (ms := ms) bs) :
    ArgMember (ofSource b) (ofSourceArgs bs) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

private theorem source_member {b ms} (bs : Arg Source.signature 0 ms)
    (h : ArgMember b (ofSourceArgs bs)) :
    ∃ a, Source.BranchMember a bs ∧ ofSource a = b := by
  match bs with
  | .nil => cases h
  | .cons a rest =>
      cases h with
      | here => exact ⟨a, .here, rfl⟩
      | there hr =>
          obtain ⟨a, ha, he⟩ := source_member rest hr
          exact ⟨a, .there ha, he⟩

private theorem ofSource_head {n} (v : Source.RawTerm n) :
    constructorHead (ofSource v) = Source.constructorHead v := by
  cases v with
  | var | atom => rfl
  | op o args => cases o <;> rfl

private theorem ofSource_match {v b r} (h : Source.MatchBranch v b r) :
    MatchBranch ∅ (ofSource v) (ofSource b) (ofSource r) := by
  cases h with
  | int ha => simpa only [ofSource_conc] using MatchBranch.int (ofSource_atom ha)
  | bool ha => simpa only [ofSource_conc] using MatchBranch.bool (ofSource_atom ha)
  | id ha => simpa only [ofSource_conc] using MatchBranch.id (ofSource_atom ha)
  | nil => exact .nil
  | pair ha hb => simpa only [ofSource_conc] using MatchBranch.pair (ofSource_atom ha) (ofSource_atom hb)

private theorem source_match {v p b r} (hb : Source.IsBranch p b)
    (h : MatchBranch ∅ v (ofSource b) r) :
    ∃ a result, Source.MatchBranch a b result ∧ ofSource a = v ∧ ofSource result = r := by
  cases hb with
  | branch ht =>
      cases h with
      | int ha =>
          obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
          exact ⟨_, _, .int ha', rfl, ofSource_conc _ _⟩
      | bool ha =>
          obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
          exact ⟨_, _, .bool ha', rfl, ofSource_conc _ _⟩
      | id ha =>
          obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
          exact ⟨_, _, .id ha', rfl, ofSource_conc _ _⟩
      | nil => exact ⟨_, _, .nil, rfl, rfl⟩
      | pair ha hb =>
          obtain ⟨a, ha', rfl⟩ := ha.source_of_empty
          obtain ⟨b, hb', rfl⟩ := hb.source_of_empty
          exact ⟨_, _, .pair ha' hb', rfl, by simp only [ofSource_conc]; rfl⟩

private theorem source_values (vs : List (RawTerm 0)) (hs : ∀ v ∈ vs, IsValue ∅ v) :
    ∃ args : List (Source.RawTerm 0), (∀ a ∈ args, Source.IsValue a) ∧ args.map ofSource = vs := by
  induction vs with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons v vs ih =>
      obtain ⟨a, ha, rfl⟩ := (hs v (by simp)).source_of_empty
      obtain ⟨args, hargs, rfl⟩ := ih (fun v h => hs v (by simp [h]))
      exact ⟨a :: args, by simpa using And.intro ha hargs, rfl⟩

/-- One source step in the fragment is the corresponding local step at empty maps. -/
theorem ofSource_step {t u} (h : Source.Step t u) (ha : AsyncFree (ofSource t)) :
    LocalStep ∅ ∅ (ofSource t) ∅ ∅ (ofSource u) := by
  induction h with
  | search_let h hb ih =>
      exact .search_let (by
        rintro ⟨k, fn, first, rest, p, body, _, _, hp, _⟩
        simp at hp) (ih ha.2.1) (ofSource_term hb)
  | @beta A As B body v vs arity hb hv hs =>
      simp only [ofSource_app, ofSource_instantiate, ofSource_castScope, List.map_cons, castScope_trans]
      exact .beta (vs := vs.map ofSource) (by simpa using arity) (ofSource_term hb) (ofSource_value hv) (by
        intro a h
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        exact ofSource_value (hs v hv))
  | @fix_beta A As B body v vs arity hb hv hs =>
      simp only [ofSource_app, ofSource_instantiate, ofSource_castScope, List.map_cons, castScope_trans]
      exact .fix_beta (vs := vs.map ofSource) (by simpa using arity) (ofSource_term hb) (ofSource_value hv) (by
        intro a h
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        exact ofSource_value (hs v hv))
  | let_value hv hb =>
      simpa only [ofSource_conc] using LocalStep.let_value (ofSource_value hv) (ofSource_term hb)
  | src_async => exact False.elim (ha.1 rfl)
  | match_constructor hs hf hm hc =>
      exact .match_constructor (ofSource_branches hs) hf (ofSource_member hm) (ofSource_match hc)
  | match_wildcard hv hc hn hs hf hm =>
      exact .match_wildcard (ofSource_value hv) ((ofSource_head _).trans hc) hn
        (ofSource_branches hs) hf (ofSource_member hm)
  | add m n => exact .add m n
  | sub m n => exact .sub m n
  | mul m n => exact .mul m n
  | eq_int_true h => exact .eq_int_true h
  | eq_int_false h => exact .eq_int_false h
  | eq_id_true h => exact .eq_id_true h
  | eq_id_false h => exact .eq_id_false h
  | lt_true h => exact .lt_true h
  | lt_false h => exact .lt_false h
  | if_true hy hn => exact .if_true (ofSource_term hy) (ofSource_term hn)
  | if_false hy hn => exact .if_false (ofSource_term hy) (ofSource_term hn)

/-- The converse allows arbitrary target maps and recovers their emptiness. -/
private theorem LocalStep.source_of_asyncFree {t sig' mu' u}
    (h : LocalStep ∅ ∅ t sig' mu' u) (ha : AsyncFree t) :
    sig' = ∅ ∧ mu' = ∅ ∧
      ∃ a b, Source.Step a b ∧ ofSource a = t ∧ ofSource b = u := by
  induction h with
  | search_let hn h hb ih =>
      obtain ⟨hs, hm, a, b, hab, rfl, rfl⟩ := ih ha.2.1
      obtain ⟨body, hb', rfl⟩ := (show IsTerm ∅ _ from by simpa using hb).source_of_empty
      exact ⟨hs, hm, _, _, .search_let hab hb', rfl, rfl⟩
  | @beta A As B body v vs arity hb hv hs =>
      simp only [domain_empty] at hb hv hs
      obtain ⟨body, hb', rfl⟩ := hb.source_of_empty
      obtain ⟨v, hv', rfl⟩ := hv.source_of_empty
      obtain ⟨vs, hs', rfl⟩ := source_values vs hs
      have har : vs.length = As.length := by simpa using arity
      refine ⟨rfl, rfl, _, _, Source.Step.beta (A := A) (B := B) har hb' hv' hs',
        ofSource_app _ _ _, ?_⟩
      simp only [ofSource_instantiate, ofSource_castScope, List.map_cons, castScope_trans]
  | @fix_beta A As B body v vs arity hb hv hs =>
      simp only [domain_empty] at hb hv hs
      obtain ⟨body, hb', rfl⟩ := hb.source_of_empty
      obtain ⟨v, hv', rfl⟩ := hv.source_of_empty
      obtain ⟨vs, hs', rfl⟩ := source_values vs hs
      have har : vs.length = As.length := by simpa using arity
      refine ⟨rfl, rfl, _, _, Source.Step.fix_beta (A := A) (B := B) har hb' hv' hs',
        ofSource_app _ _ _, ?_⟩
      simp only [ofSource_instantiate, ofSource_castScope, List.map_cons, castScope_trans]
      rfl
  | let_value hv hb =>
      obtain ⟨v, hv', rfl⟩ := (show IsValue ∅ _ from by simpa using hv).source_of_empty
      obtain ⟨body, hb', rfl⟩ := (show IsTerm ∅ _ from by simpa using hb).source_of_empty
      exact ⟨rfl, rfl, _, _, .let_value hv' hb', rfl, ofSource_conc _ _⟩
  | match_constructor hs hf hm hc =>
      obtain ⟨bs, hs', rfl⟩ := (show IsBranches ∅ _ _ from by simpa using hs).source_of_empty
      obtain ⟨b, hm', rfl⟩ := source_member bs hm
      obtain ⟨p, hb⟩ := hm'.formed hs'
      obtain ⟨a, r, hc', rfl, rfl⟩ := source_match hb (by simpa using hc)
      exact ⟨rfl, rfl, _, _, .match_constructor hs' hf hm' hc', rfl, rfl⟩
  | match_wildcard hv hc hn hs hf hm =>
      obtain ⟨v, hv', rfl⟩ := (show IsValue ∅ _ from by simpa using hv).source_of_empty
      obtain ⟨bs, hs', rfl⟩ := (show IsBranches ∅ _ _ from by simpa using hs).source_of_empty
      obtain ⟨b, hm', he⟩ := source_member bs hm
      obtain ⟨p, hb⟩ := hm'.formed hs'
      cases hb with
      | branch ht =>
          cases he
          exact ⟨rfl, rfl, _, _, .match_wildcard hv' ((ofSource_head _).symm.trans hc)
            hn hs' hf hm', rfl, rfl⟩
  | add m n => exact ⟨rfl, rfl, _, _, .add m n, rfl, rfl⟩
  | sub m n => exact ⟨rfl, rfl, _, _, .sub m n, rfl, rfl⟩
  | mul m n => exact ⟨rfl, rfl, _, _, .mul m n, rfl, rfl⟩
  | eq_int_true h => exact ⟨rfl, rfl, _, _, .eq_int_true h, rfl, rfl⟩
  | eq_int_false h => exact ⟨rfl, rfl, _, _, .eq_int_false h, rfl, rfl⟩
  | eq_id_true h => exact ⟨rfl, rfl, _, _, .eq_id_true h, rfl, rfl⟩
  | eq_id_false h => exact ⟨rfl, rfl, _, _, .eq_id_false h, rfl, rfl⟩
  | lt_true h => exact ⟨rfl, rfl, _, _, .lt_true h, rfl, rfl⟩
  | lt_false h => exact ⟨rfl, rfl, _, _, .lt_false h, rfl, rfl⟩
  | if_true hy hn =>
      obtain ⟨yes, hy', rfl⟩ := (show IsTerm ∅ _ from by simpa using hy).source_of_empty
      obtain ⟨no, hn', rfl⟩ := (show IsTerm ∅ _ from by simpa using hn).source_of_empty
      exact ⟨rfl, rfl, _, _, .if_true hy' hn', rfl, rfl⟩
  | if_false hy hn =>
      obtain ⟨yes, hy', rfl⟩ := (show IsTerm ∅ _ from by simpa using hy).source_of_empty
      obtain ⟨no, hn', rfl⟩ := (show IsTerm ∅ _ from by simpa using hn).source_of_empty
      exact ⟨rfl, rfl, _, _, .if_false hy' hn', rfl, rfl⟩
  | spawn_async => exact False.elim (ha.1 rfl)
  | spawn_app hex _ _ _ => obtain ⟨p, body, _, hp, _⟩ := hex; simp at hp
  | deref_app hp _ | deref_op_left hp _ | deref_op_right hp _ | deref_if hp _ | deref_match hp _ =>
      simp at hp

private theorem eq_initial {s : State} {a : Source.RawTerm 0} (ha : Source.IsTerm a)
    (hs : s.signature = ∅) (hm : s.mapping = ∅) (hf : s.focus = ofSource a) :
    s = initialState a ha := by
  cases s
  cases hs; cases hm; cases hf
  rfl

/-- Every successor is an empty-map source state, with no async anywhere in its focus. -/
theorem Step.source_of_asyncFree {a} {ha : Source.IsTerm a} {s : State}
    (h : Step (initialState a ha) s) (hf : AsyncFree (ofSource a)) :
    ∃ b, ∃ hstep : Source.Step a b,
      AsyncFree (ofSource b) ∧ s = initialState b hstep.formed.2 := by
  cases h with
  | focus h =>
      obtain ⟨hs, hm, a', b, hstep, he, hb⟩ := h.source_of_asyncFree hf
      have he' := ofSource_injective a' a he
      subst a'
      refine ⟨b, hstep, ?_, eq_initial hstep.formed.2 hs hm hb.symm⟩
      rw [hb]
      exact h.asyncFree_empty rfl hf
  | future hp _ _ _ _ => simp [initialState] at hp

/-- C-Async-Free, one step. Only source formation and absence of async are required. -/
theorem asyncFree_step_iff {a b} (ha : Source.IsTerm a) (hb : Source.IsTerm b)
    (hf : AsyncFree (ofSource a)) :
    Source.Step a b ↔ Step (initialState a ha) (initialState b hb) := by
  constructor
  · intro h; exact .focus (ofSource_step h hf)
  · intro h
    obtain ⟨b', hstep, _, he⟩ := h.source_of_asyncFree hf
    have hb' := ofSource_injective b b' (congrArg State.focus he)
    subst b'
    exact hstep

private theorem ofSource_steps {a b} (h : Source.Steps a b)
    {ha : Source.IsTerm a} {hb : Source.IsTerm b} (hf : AsyncFree (ofSource a)) :
    Steps (initialState a ha) (initialState b hb) := by
  induction h with
  | refl => exact .refl
  | step h hs ih =>
      have hl := ofSource_step h hf
      exact .step (t := initialState _ h.formed.2) (.focus hl) (ih (hl.asyncFree_empty rfl hf))

/-- Arbitrary finite executions preserve empty maps; intermediate states are not assumed empty. -/
theorem Steps.source_of_asyncFree {s u} (h : Steps s u) {a} (ha : Source.IsTerm a)
    (he : s = initialState a ha) (hf : AsyncFree (ofSource a)) :
    ∃ b, ∃ hb : Source.IsTerm b,
      Source.Steps a b ∧ AsyncFree (ofSource b) ∧ u = initialState b hb := by
  induction h generalizing a with
  | refl => exact ⟨a, ha, .refl ha, hf, he⟩
  | step hs _ ih =>
      rw [he] at hs
      obtain ⟨b, hstep, hf', he'⟩ := hs.source_of_asyncFree hf
      obtain ⟨c, hc, hsteps, hf'', he''⟩ := ih hstep.formed.2 he' hf'
      exact ⟨c, hc, .step hstep hsteps, hf'', he''⟩

/-- C-Async-Free, finite execution. -/
theorem asyncFree_steps_iff {a b} (ha : Source.IsTerm a) (hb : Source.IsTerm b)
    (hf : AsyncFree (ofSource a)) :
    Source.Steps a b ↔ Steps (initialState a ha) (initialState b hb) := by
  constructor
  · intro h; exact ofSource_steps h hf
  · intro h
    obtain ⟨b', hb', hsteps, _, he⟩ := h.source_of_asyncFree ha rfl hf
    have he' := ofSource_injective b b' (congrArg State.focus he)
    subst b'
    exact hsteps

end SourceRuntime.Runtime

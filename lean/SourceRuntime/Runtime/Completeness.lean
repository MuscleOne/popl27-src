import SourceRuntime.Runtime.Execution
import SourceRuntime.Runtime.Dereference

/-!
The execution construction in C-Seq-to-Obs, at arbitrary intermediate types.
Realization packages the paper's strengthened conclusion. CompletenessAt exposes
only the source step count used by its strong induction; neither is a runtime rule.
-/

namespace SourceRuntime.Runtime
open WSLN
open Source (Ty)

/-- Conclusions maintained by the constructed execution, including the let-path
    condition and retention of the input value entries. -/
private structure Realization (s t : State) (v : Source.RawTerm 0) : Prop where
  path : FocusReadySteps s t
  ok : t.Ok
  final : t.Final
  enumeration : HasValueEnumeration t.mapping
  retain : ∀ (p : FName) w, s.mapping[p]? = some w → t.mapping[p]? = some w
  readback : readback enumeration t.focus (ok.domains ▸ t.focus_formed) = v

/-- The paper's strengthened assertion for a source evaluation of exactly k steps. -/
private def CompletenessAt (k : Nat) : Prop :=
  ∀ (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) (A : Ty) (v : Source.RawTerm 0),
    HasType s.signature [] s.focus A →
    Source.StepsN k (readback hc s.focus (hs.domains ▸ s.focus_formed)) v →
    Source.IsValue v → ∃ t, Realization s t v

private theorem HasValueEnumeration.state_entries {s : State} (hc : HasValueEnumeration s.mapping) (hs : s.Ok) :
    ∀ (p : FName) w, s.mapping[p]? = some w → IsValue (domain s.signature) w := by
  intro p w hp
  exact hs.domains ▸ (hc.entries hp).1

/-- Zero source steps: value reflection supplies runtime finality. -/
private theorem CompletenessAt.zero : CompletenessAt 0 := by
  intro s hc hs A v ht he hv
  cases he
  exact ⟨s, ⟨.refl, hs,
    ⟨hs.domains ▸ (readback_value_iff hc (hs.domains ▸ s.focus_formed)).mp hv,
      hc.state_entries hs⟩,
    hc, fun _ _ hp => hp, rfl⟩⟩

/-- Finish a given operand realization inside a fresh future. Allocation places q
    first in time; the value dependency enumeration places q after its dependencies. -/
private theorem Realization.async {s t v} (h : Realization s t v) (hc : HasValueEnumeration s.mapping)
    (hs : s.Ok) {A} (ht : HasType s.signature [] s.focus A) :
    ∃ u, Realization (s.withFocus (Runtime.async s.focus) (.async s.focus_formed)) u v := by
  obtain ⟨q, fresh⟩ := t.signature.exists_fresh
  have fresh₀ : q ∉ domain s.signature := fun hq => fresh (h.path.steps.sigma_extends.domain q hq)
  let u := t.inFuture q A
  have path : FocusReadySteps (s.withFocus (Runtime.async s.focus) (.async s.focus_formed)) u :=
    .focus (t := s.inFuture q A) (hc.state_entries hs) (.spawn_async ht fresh₀) (h.path.steps.inFuture_ready q A fresh)
  have initial : (s.withFocus (Runtime.async s.focus) (.async s.focus_formed)).Ok :=
    ⟨hs.domains, ⟨A, .async ht⟩, hs.entries⟩
  have ok : u.Ok := (preservation_steps path.steps initial (.async ht)).1
  have fresh_map : q ∉ domain t.mapping := fun hq => fresh (t.domains q hq)
  have typed := (preservation_steps h.path.steps hs ht).2
  have enumeration : HasValueEnumeration u.mapping :=
    .snoc h.enumeration fresh_map (h.ok.domains ▸ h.final.focus) typed.closed
  have keep : ∀ (p : FName) w, t.mapping[p]? = some w → u.mapping[p]? = some w := by
    intro p w hp
    have hqp : q ≠ p := fun e => fresh_map (e ▸ mem_domain_of_lookup hp)
    change (t.mapping.insert q t.focus)[p]? = some w
    simpa [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hqp] using hp
  refine ⟨u, ⟨path, ok, h.final.inFuture q A, enumeration, fun p w hp => keep p w (h.retain p w hp), ?_⟩⟩
  change Runtime.readback enumeration (future q) _ = v
  rw [readback_future enumeration (w := t.focus) (by simp [u, State.inFuture, State.insert, State.withFocus])]
  rw [Trm.weaken_self]
  exact (readback_extension h.enumeration enumeration keep (h.ok.domains ▸ t.focus_formed) _).trans h.readback

/-- Async case of the strong induction: the source operand tail is one step shorter. -/
private theorem realize_async {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {body A v}
    (ht : HasType s.signature [] body A)
    (he : Source.StepsN k (readback hc (async body) (hs.domains ▸ (.async ht.formed))) v)
    (hv : Source.IsValue v) :
    ∃ t, Realization (s.withFocus (async body) (.async ht.formed)) t v := by
  change Source.StepsN k (Source.async (readback hc body (hs.domains ▸ ht.formed))) v at he
  obtain ⟨j, hk, hj⟩ := he.async_inv hv
  let operand := s.withFocus body ht.formed
  have ok : operand.Ok := ⟨hs.domains, ⟨A, ht⟩, hs.entries⟩
  obtain ⟨t, result⟩ := ih j (by omega) operand hc ok A v ht hj hv
  exact result.async hc ok ht

/-- Let case of the strong induction. The two calls use the shorter RHS and body
    paths; read-back extension and concretion identify the second call's source term. -/
private theorem realize_let {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {rhs body A B v}
    (hr : HasType s.signature [] rhs A)
    (hb : Typing s.signature [] (Source.push A Fin.elim0) body B)
    (he : Source.StepsN k
      (readback hc (letE rhs body) (hs.domains ▸ (.letE hr.formed hb.formed))) v)
    (hv : Source.IsValue v) :
    ∃ t, Realization (s.withFocus (letE rhs body) (.letE hr.formed hb.formed)) t v := by
  have hr₀ : IsTerm (domain s.mapping) rhs := hs.domains ▸ hr.formed
  have hb₀ : IsTerm (domain s.mapping) body := hs.domains ▸ hb.formed
  change Source.StepsN k (Source.letE (readback hc rhs hr₀) (readback hc body hb₀)) v at he
  obtain ⟨w, i, j, hw, h₁, h₂, hk⟩ := he.let_inv hv
  let operand := s.withFocus rhs hr.formed
  have operand_ok : operand.Ok := ⟨hs.domains, ⟨A, hr⟩, hs.entries⟩
  obtain ⟨t, first⟩ := ih i (by omega) operand hc operand_ok A w hr h₁ hw
  have hb₁ := hb.formed.mono first.path.steps.sigma_extends.domain
  let continuation := t.withFocus (body.conc t.focus) (hb₁.conc (.value first.final.focus))
  have path : FocusReadySteps (s.withFocus (letE rhs body) (.letE hr.formed hb.formed)) continuation :=
    first.path.let_value body hb.formed first.final
  have initial : (s.withFocus (letE rhs body) (.letE hr.formed hb.formed)).Ok :=
    ⟨hs.domains, ⟨B, .letE hr hb⟩, hs.entries⟩
  obtain ⟨ok, typed⟩ := preservation_steps path.steps initial (.letE hr hb)
  have equation : readback first.enumeration continuation.focus (ok.domains ▸ continuation.focus_formed) =
      (readback hc body hb₀).conc w := by
    change readback first.enumeration (body.conc t.focus) _ = _
    rw [readback_conc first.enumeration (first.ok.domains ▸ hb₁)
      (first.ok.domains ▸ (.value first.final.focus))]
    rw [readback_extension hc first.enumeration first.retain hb₀ (first.ok.domains ▸ hb₁), first.readback]
  rw [← equation] at h₂
  obtain ⟨u, second⟩ := ih j (by omega) continuation first.enumeration ok B v typed h₂ hv
  exact ⟨u, ⟨path.trans second.path, second.ok, second.final, second.enumeration,
    fun p term hp => second.retain p term (first.retain p term hp), second.readback⟩⟩

-- The four head cases share the same shorter source tail. Their callbacks below
-- expose only the positions demanded by the actual runtime rules.
private theorem realize_head {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {A v}
    (ht : HasType s.signature [] s.focus A)
    (he : Source.StepsN k (readback hc s.focus (hs.domains ▸ s.focus_formed)) v)
    (hv : Source.IsValue v)
    (advance : ∀ r, Source.Step (readback hc s.focus (hs.domains ▸ s.focus_formed)) r →
      ∃ t, ∃ formed : IsTerm (domain s.mapping) t,
        FocusReadySteps s (s.withFocus t (hs.domains ▸ formed)) ∧ readback hc t formed = r) :
    ∃ t, Realization s t v := by
  cases he with
  | refl formed => exact CompletenessAt.zero s hc hs A _ ht (.refl formed) hv
  | @step j _ r v first rest =>
      obtain ⟨t, formed, path, equation⟩ := advance r first
      obtain ⟨ok, typed⟩ := preservation_steps path.steps hs ht
      rw [← equation] at rest
      obtain ⟨u, result⟩ := ih j (by omega) (s.withFocus t (hs.domains ▸ formed)) hc ok A v typed rest hv
      exact ⟨u, ⟨path.trans result.path, result.ok, result.final, result.enumeration,
        result.retain, result.readback⟩⟩

private theorem closed_atom_value {sig a A} (ha : IsAtom (domain sig) a)
    (ht : HasType sig [] a A) : IsValue (domain sig) a := by
  cases ha with
  | bound i => exact Fin.elim0 i
  | free x => cases ht with | free h => simp at h
  | value hv => exact hv

/-- Expose the condition, take If-True/False, and use the shorter source tail. -/
private theorem realize_if {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {guard yes no A v}
    (hg : IsAtom (domain s.signature) guard) (htg : HasType s.signature [] guard .bool)
    (hy : HasType s.signature [] yes A) (hn : HasType s.signature [] no A)
    (he : Source.StepsN k (readback hc (ifE guard yes no)
      (hs.domains ▸ (.ifE hg hy.formed hn.formed))) v) (hv : Source.IsValue v) :
    ∃ t, Realization (s.withFocus (ifE guard yes no) (.ifE hg hy.formed hn.formed)) t v := by
  have typed : HasType s.signature [] (ifE guard yes no) A := .ifE hg htg hy hn
  apply realize_head ih (s.withFocus _ typed.formed) hc ⟨hs.domains, ⟨A, typed⟩, hs.entries⟩ typed he hv
  intro r step
  have hguard : IsValue (domain s.mapping) guard := hs.domains ▸ closed_atom_value hg htg
  obtain ⟨w, hw, head, chain⟩ := hc.exists_nonfuture_value hguard
  have path := chain.lift hc hs hguard hw (fun g => ifE g yes no)
    (fun _ h => .ifE (.value (hs.domains ▸ h)) hy.formed hn.formed)
    (fun _ _ hp h => .deref_if hp h)
  have equation := chain.readback_eq hc hguard hw
  change Source.Step (Source.ifE (readback hc guard (.atom (.value hguard)))
    (readback hc yes (hs.domains ▸ hy.formed)) (readback hc no (hs.domains ▸ hn.formed))) r at step
  rw [equation] at step
  obtain ⟨t, formed, rule, result⟩ := readback_if_step (yes := yes) (no := no) (result := r)
    hc hs.domains hw head (hs.domains ▸ hy.formed) (hs.domains ▸ hn.formed) step
  exact ⟨t, formed, path.trans (.focus (t := s.withFocus t (hs.domains ▸ formed))
    (hc.state_entries hs) rule .refl), result⟩

/-- Expose the two operands in sequence; no constructor fields are evaluated. -/
private theorem realize_operation {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {op a b A v}
    (ha : IsValue (domain s.signature) a) (hb : IsValue (domain s.signature) b)
    (ht : HasType s.signature [] (operation op a b) A)
    (he : Source.StepsN k (readback hc (operation op a b)
      (hs.domains ▸ (.operation op (.value ha) (.value hb)))) v) (hv : Source.IsValue v) :
    ∃ t, Realization (s.withFocus (operation op a b) (.operation op (.value ha) (.value hb))) t v := by
  apply realize_head ih (s.withFocus _ ht.formed) hc ⟨hs.domains, ⟨A, ht⟩, hs.entries⟩ ht he hv
  intro r step
  have ha₀ : IsValue (domain s.mapping) a := hs.domains ▸ ha
  have hb₀ : IsValue (domain s.mapping) b := hs.domains ▸ hb
  obtain ⟨x, hx, headX, chainX⟩ := hc.exists_nonfuture_value ha₀
  obtain ⟨y, hy, headY, chainY⟩ := hc.exists_nonfuture_value hb₀
  have left := chainX.lift hc hs ha₀ hx (fun w => operation op w b)
    (fun _ h => .operation op (.value (hs.domains ▸ h)) (.value hb))
    (fun _ _ hp h => .deref_op_left hp h)
  have right := chainY.lift hc hs hb₀ hy (fun w => operation op x w)
    (fun _ h => .operation op (.value (hs.domains ▸ hx)) (.value (hs.domains ▸ h)))
    (fun _ _ hp h => .deref_op_right hp h)
  have ex := chainX.readback_eq hc ha₀ hx
  have ey := chainY.readback_eq hc hb₀ hy
  change Source.Step (Source.operation op (readback hc a (.atom (.value ha₀)))
    (readback hc b (.atom (.value hb₀)))) r at step
  rw [ex, ey] at step
  obtain ⟨t, formed, rule, result⟩ := readback_operation_step (op := op) (result := r)
    hc hs.domains hx hy headX headY step
  exact ⟨t, formed, (left.trans right).trans (.focus (t := s.withFocus t (hs.domains ▸ formed))
    (hc.state_entries hs) rule .refl), result⟩

private theorem arguments_values {sig k As} {args : RawArgs 0 k}
    (hs : ArgsTyping sig [] Fin.elim0 As args) :
    ∃ vs : List (RawTerm 0), ∃ e : vs.length = k,
      (e ▸ toArgs vs) = args ∧ ∀ v ∈ vs, IsValue (domain sig) v := by
  induction k generalizing As with
  | zero => cases hs; exact ⟨[], rfl, rfl, by simp⟩
  | succ k ih =>
      cases hs with
      | cons ha ht hs =>
          obtain ⟨vs, e, he, hv⟩ := ih hs
          cases e
          cases he
          refine ⟨_ :: vs, rfl, rfl, ?_⟩
          intro v h
          rcases List.mem_cons.mp h with rfl | h
          · exact closed_atom_value ha ht
          · exact hv v h

/-- Expose only the function head. Beta and Fix-beta keep future arguments intact. -/
private theorem realize_app {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {count fn first A As B v}
    {rest : RawArgs 0 count}
    (hf : IsAtom (domain s.signature) fn) (ha : IsAtom (domain s.signature) first)
    (htf : HasType s.signature [] fn (.arrow A As B)) (hta : HasType s.signature [] first A)
    (args : ArgsTyping s.signature [] Fin.elim0 As rest)
    (he : Source.StepsN k (readback hc (app fn first rest)
      (hs.domains ▸ (.app hf ha args.formed))) v) (hv : Source.IsValue v) :
    ∃ t, Realization (s.withFocus (app fn first rest) (.app hf ha args.formed)) t v := by
  obtain ⟨vs, e, eqs, values⟩ := arguments_values args
  cases e
  cases eqs
  have typed : HasType s.signature [] (app fn first (toArgs vs)) B := .app hf ha htf hta args
  apply realize_head ih (s.withFocus _ typed.formed) hc ⟨hs.domains, ⟨B, typed⟩, hs.entries⟩ typed he hv
  intro r step
  have hfn : IsValue (domain s.mapping) fn := hs.domains ▸ closed_atom_value hf htf
  obtain ⟨w, hw, head, chain⟩ := hc.exists_nonfuture_value hfn
  have path := chain.lift hc hs hfn hw (fun f => app f first (toArgs vs))
    (fun _ h => .app (.value (hs.domains ▸ h)) ha args.formed)
    (fun _ _ hp h => .deref_app hp h)
  have equation := chain.readback_eq hc hfn hw
  change Source.Step (Source.app (readback hc fn (.atom (.value hfn))) _ _) r at step
  rw [equation] at step
  obtain ⟨t, formed, rule, result⟩ := readback_app_step (first := first) (result := r) hc hs.domains hw head
    (hs.domains ▸ closed_atom_value ha hta) vs (fun a h => hs.domains ▸ values a h) step
  exact ⟨t, formed, path.trans (.focus (t := s.withFocus t (hs.domains ▸ formed))
    (hc.state_entries hs) rule .refl), result⟩

/-- Expose the scrutinee; constructor fields pass directly to the selected branch. -/
private theorem realize_match {k : Nat} (ih : ∀ j, j < k → CompletenessAt j)
    (s : State) (hc : HasValueEnumeration s.mapping) (hs : s.Ok) {count ps a A v} {bs : RawArgs 0 count}
    (ha : IsAtom (domain s.signature) a) (hta : HasType s.signature [] a .sexp)
    (branches : BranchesTyping s.signature [] Fin.elim0 ps bs A) (patterns : Source.MatchPatterns ps)
    (he : Source.StepsN k (readback hc (matchE a bs)
      (hs.domains ▸ (.matchE ha branches.formed patterns))) v) (hv : Source.IsValue v) :
    ∃ t, Realization (s.withFocus (matchE a bs) (.matchE ha branches.formed patterns)) t v := by
  have typed : HasType s.signature [] (matchE a bs) A := .matchE ha hta branches patterns
  apply realize_head ih (s.withFocus _ typed.formed) hc ⟨hs.domains, ⟨A, typed⟩, hs.entries⟩ typed he hv
  intro r step
  have ha₀ : IsValue (domain s.mapping) a := hs.domains ▸ closed_atom_value ha hta
  obtain ⟨w, hw, head, chain⟩ := hc.exists_nonfuture_value ha₀
  have path := chain.lift hc hs ha₀ hw (fun v => matchE v bs)
    (fun _ h => .matchE (.value (hs.domains ▸ h)) branches.formed patterns)
    (fun _ _ hp h => .deref_match hp h)
  have equation := chain.readback_eq hc ha₀ hw
  change Source.Step (Source.matchE (readback hc a (.atom (.value ha₀))) _) r at step
  rw [equation] at step
  obtain ⟨t, formed, rule, result⟩ := readback_match_step (bs := bs) (result := r) hc hs.domains hw head
    (hs.domains ▸ branches.formed) patterns step
  exact ⟨t, formed, path.trans (.focus (t := s.withFocus t (hs.domains ▸ formed))
    (hc.state_entries hs) rule .refl), result⟩

/-- The strengthened construction, by strong induction on source evaluation length. -/
private theorem completeness_at (k : Nat) : CompletenessAt k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro s hc hs A v ht he hv
      have construct (t : RawTerm 0) (formed : IsTerm (domain s.signature) t)
          (typed : HasType s.signature [] t A)
          (eval : Source.StepsN k (readback hc t (hs.domains ▸ formed)) v) :
          ∃ u, Realization (s.withFocus t formed) u v := by
        cases formed with
        | atom ha =>
            have value : IsValue (domain s.mapping) t := hs.domains ▸ closed_atom_value ha typed
            cases eval with
            | refl formed =>
                exact CompletenessAt.zero (s.withFocus _ typed.formed) hc
                  ⟨hs.domains, ⟨A, typed⟩, hs.entries⟩ A _ typed (.refl formed) hv
            | step first _ => exact False.elim (Source.value_irreducible (readback_value hc value) first)
        | app hf ha args =>
            cases typed with
            | app hf ha tf ta ts => exact realize_app ih s hc hs hf ha tf ta ts eval hv
        | operation op ha hb =>
            cases typed with
            | arith hop ha hb ta tb =>
                exact realize_operation ih s hc hs (closed_atom_value ha ta) (closed_atom_value hb tb)
                  (.arith hop ha hb ta tb) eval hv
            | eq hA ha hb ta tb =>
                exact realize_operation ih s hc hs (closed_atom_value ha ta) (closed_atom_value hb tb)
                  (.eq hA ha hb ta tb) eval hv
            | lt ha hb ta tb =>
                exact realize_operation ih s hc hs (closed_atom_value ha ta) (closed_atom_value hb tb)
                  (.lt ha hb ta tb) eval hv
        | ifE hg hy hn =>
            cases typed with | ifE hg tg ty tn => exact realize_if ih s hc hs hg tg ty tn eval hv
        | letE hr hb =>
            cases typed with | letE tr tb => exact realize_let ih s hc hs tr tb eval hv
        | matchE ha branches patterns =>
            cases typed with | matchE ha ta tb hp => exact realize_match ih s hc hs ha ta tb hp eval hv
        | async hb =>
            cases typed with | async tb => exact realize_async ih s hc hs tb eval hv
      exact construct s.focus s.focus_formed ht he

/-- C-Seq-to-Obs: one permitted finite execution obtains the given sequential value. -/
theorem seq_to_obs {M v A} (ht : Source.HasType [] M A) (ho : ObservableType A)
    (he : Source.Steps M v) (hv : Source.IsValue v) :
    ∃ s, Steps (initialState M ht.formed) s ∧ s.Observes v := by
  obtain ⟨k, eval⟩ := he.exists_length
  have equation := readback_source (HasValueEnumeration.empty) M ht.formed
  rw [← equation] at eval
  obtain ⟨s, result⟩ := completeness_at k (initialState M ht.formed) .empty (initial_ok ht)
    A v (ofSource_typing ht) eval hv
  have typed := (preservation_steps result.path.steps (initial_ok ht) (ofSource_typing ht)).2
  have observed := State.observes_readback result.enumeration result.ok result.final typed ho
  rw [result.readback] at observed
  exact ⟨s, result.path.steps, observed⟩

end SourceRuntime.Runtime

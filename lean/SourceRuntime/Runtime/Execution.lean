import SourceRuntime.Runtime.Preservation

/-!
Execution construction used by C-Seq-to-Obs (metatheory.md): retain an unused entry
in a local derivation, then execute a supplied finite path inside that entry.
States keep their explicit names. Transport uses formation alone; FocusReadySteps
records the extra value-entry condition required when lifting a path through let.
-/

namespace SourceRuntime.Runtime
open WSLN
open Source (Ty)

private theorem insert_domain {sig : Signature} (q : FName) (A : Ty) :
    ∀ p, p ∈ domain sig → p ∈ domain (sig.insert q A) := by
  intro p hp
  simp only [domain_insert, Std.ExtTreeSet.mem_insert]
  exact .inr hp

private theorem insert_lookup {α} (m : FMap α) {p q : FName} (v : α) (h : q ≠ p) :
    (m.insert q v)[p]? = m[p]? := by
  simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, h]

private theorem insert_comm {α} (m : FMap α) {p q : FName} (a b : α) (h : p ≠ q) :
    (m.insert p a).insert q b = (m.insert q b).insert p a := by
  apply Std.ExtTreeMap.ext_getElem?
  intro r
  by_cases hp : p = r
  · subst r
    simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      if_neg (Ne.symm h)]
  · by_cases hq : q = r
    · subst r
      simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        if_neg h]
    · simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        if_neg hp, if_neg hq]

private theorem insert_twice {α} (m : FMap α) (q : FName) (a b : α) :
    (m.insert q a).insert q b = m.insert q b := by
  apply Std.ExtTreeMap.ext_getElem?
  intro r
  by_cases h : q = r <;>
    simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, h]

-- The active-name parameter checks fields, but cannot change a formed term's outer category.
private theorem value_of_formed {U V n} {t : RawTerm n} (ht : IsTerm U t)
    (hv : IsValue V t) : IsValue U t := by
  cases ht with
  | atom ha => cases ha with
    | value hv => exact hv
    | bound | free => cases hv
  | _ => cases hv

private theorem atom_future_mem {U n p} (ha : IsAtom U (future (n := n) p)) : p ∈ U := by
  cases ha with | value hv => exact future_value_iff.mp hv

private theorem ArgMember.atom {U a ms args} (hm : ArgMember a (ms := ms) args)
    (hs : IsAtoms U args) : IsAtom U a := by
  induction hm with
  | here => cases hs with | cons ha _ => exact ha
  | there _ ih => cases hs with | cons _ hs => exact ih hs

private theorem application_future_mem {U k fn first p} {rest : RawArgs 0 k}
    (ht : IsTerm U (app fn first rest))
    (hp : fn = future p ∨ first = future p ∨ ArgMember (future p) rest) : p ∈ U := by
  cases ht with
  | atom ha => cases ha with | value hv => cases hv
  | app hf ha hs =>
      rcases hp with h | h | h
      · rw [h] at hf; exact atom_future_mem hf
      · rw [h] at ha; exact atom_future_mem ha
      · exact atom_future_mem (h.atom hs)

private theorem let_rhs_formed {U} {rhs : RawTerm 0} {body : RawTerm 1}
    (ht : IsTerm U (letE rhs body)) : IsTerm U rhs := by
  cases ht with
  | atom ha => cases ha with | value hv => cases hv
  | letE hr _ => exact hr

private theorem MatchBranch.mono {U V v b r} (h : MatchBranch U v b r)
    (hUV : ∀ p, p ∈ U → p ∈ V) : MatchBranch V v b r := by
  cases h with
  | int ha => exact .int (ha.mono hUV)
  | bool ha => exact .bool (ha.mono hUV)
  | id ha => exact .id (ha.mono hUV)
  | nil => exact .nil
  | pair ha hb => exact .pair (ha.mono hUV) (hb.mono hUV)

/-- Raw rule transport; the enclosing State supplies formation and domain inclusion. -/
private theorem LocalStep.insert_entry {sig mu t sig' mu' t'} (h : LocalStep sig mu t sig' mu' t')
    (ht : IsTerm (domain sig) t)
    (hd : ∀ p, p ∈ domain mu → p ∈ domain sig)
    (hm : ∀ (p : FName) body, mu[p]? = some body → IsTerm (domain sig) body)
    (q : FName) (A : Ty) (body : RawTerm 0) (fresh : q ∉ domain sig') :
    LocalStep (sig.insert q A) (mu.insert q body) t (sig'.insert q A) (mu'.insert q body) t' := by
  have fresh₀ : q ∉ domain sig := fun hq => fresh (h.sigma_extends.domain q hq)
  have old_lookup {p : FName} {v} (hp : mu[p]? = some v) :
      (mu.insert q body)[p]? = some v := by
    have hqp : q ≠ p := fun e => fresh₀ (e ▸ hd p (mem_domain_of_lookup hp))
    rw [insert_lookup mu body hqp]
    exact hp
  induction h with
  | search_let hn h hb ih =>
      have hr := let_rhs_formed ht
      apply LocalStep.search_let
      · rintro ⟨k, fn, first, rest, p, v, he, hp, hm', hv⟩
        have hpU := application_future_mem (he ▸ hr) hp
        have hqp : q ≠ p := fun e => fresh₀ (e ▸ hpU)
        rw [insert_lookup mu body hqp] at hm'
        exact hn ⟨k, fn, first, rest, p, v, he, hp, hm',
          fun hv' => hv (hv'.mono (insert_domain q A))⟩
      · exact ih hr fresh
      · exact hb.mono (insert_domain q A)
  | beta arity hb hv hs =>
      exact .beta arity (hb.mono (insert_domain q A)) (hv.mono (insert_domain q A))
        (fun v hv => (hs v hv).mono (insert_domain q A))
  | fix_beta arity hb hv hs =>
      exact .fix_beta arity (hb.mono (insert_domain q A)) (hv.mono (insert_domain q A))
        (fun v hv => (hs v hv).mono (insert_domain q A))
  | let_value hv hb => exact .let_value (hv.mono (insert_domain q A)) (hb.mono (insert_domain q A))
  | match_constructor hs hf hp hc =>
      exact .match_constructor (hs.mono (insert_domain q A)) hf hp (hc.mono (insert_domain q A))
  | match_wildcard hv hc hn hs hf hp =>
      exact .match_wildcard (hv.mono (insert_domain q A)) hc hn (hs.mono (insert_domain q A)) hf hp
  | add m n => exact .add m n
  | sub m n => exact .sub m n
  | mul m n => exact .mul m n
  | eq_int_true he => exact .eq_int_true he
  | eq_int_false he => exact .eq_int_false he
  | eq_id_true he => exact .eq_id_true he
  | eq_id_false he => exact .eq_id_false he
  | lt_true he => exact .lt_true he
  | lt_false he => exact .lt_false he
  | if_true hy hn => exact .if_true (hy.mono (insert_domain q A)) (hn.mono (insert_domain q A))
  | if_false hy hn => exact .if_false (hy.mono (insert_domain q A)) (hn.mono (insert_domain q A))
  | @spawn_async body' B p hb hp =>
      have hqp : q ≠ p := by intro e; subst q; simp at fresh
      rw [insert_comm sig B A (Ne.symm hqp), insert_comm mu body' body (Ne.symm hqp)]
      exact .spawn_async (hb.sigma_weaken (Signature.extends_insert A fresh₀)) (by
        simpa [domain_insert, hqp] using hp)
  | deref_app hp hv => exact .deref_app (old_lookup hp) (hv.mono (insert_domain q A))
  | deref_op_left hp hv => exact .deref_op_left (old_lookup hp) (hv.mono (insert_domain q A))
  | deref_op_right hp hv => exact .deref_op_right (old_lookup hp) (hv.mono (insert_domain q A))
  | deref_if hp hv => exact .deref_if (old_lookup hp) (hv.mono (insert_domain q A))
  | deref_match hp hv => exact .deref_match (old_lookup hp) (hv.mono (insert_domain q A))
  | @spawn_app k fn first rest tail B p hex hb hp htail =>
      have hqp : q ≠ p := by intro e; subst q; simp at fresh
      rw [insert_comm sig B A (Ne.symm hqp), insert_comm mu (app fn first rest) body (Ne.symm hqp)]
      apply LocalStep.spawn_app
      · obtain ⟨r, v, hr, hv, hn⟩ := hex
        exact ⟨r, v, hr, old_lookup hv, fun hv' => hn (value_of_formed (hm r v hv) hv')⟩
      · exact hb.sigma_weaken (Signature.extends_insert A fresh₀)
      · simpa [domain_insert, hqp] using hp
      · exact htail.mono (insert_domain q A)

private theorem insert_domain_mono {sig sig' : Signature} (h : sig.Extends sig')
    (q : FName) (A : Ty) :
    ∀ p, p ∈ domain (sig.insert q A) → p ∈ domain (sig'.insert q A) := by
  intro p hp
  simp only [domain_insert, Std.ExtTreeSet.mem_insert] at hp ⊢
  exact hp.imp id (h.domain p)

/-- Apply the two finite-map updates to a formed display, retaining its focus. -/
def State.insert (s : State) (q : FName) (A : Ty) (body : RawTerm 0)
    (hb : IsTerm (domain (s.signature.insert q A)) body) : State where
  signature := s.signature.insert q A
  focus := s.focus
  mapping := s.mapping.insert q body
  domains := by
    intro p hp
    simp only [domain_insert, Std.ExtTreeSet.mem_insert] at hp ⊢
    exact hp.imp id (s.domains p)
  focus_formed := s.focus_formed.mono (insert_domain q A)
  entries_formed := by
    intro p term hp
    by_cases h : q = p
    · subst p
      simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hp
      subst term
      exact hb
    · rw [insert_lookup s.mapping body h] at hp
      exact (s.entries_formed p term hp).mono (insert_domain q A)

/-- Add an unused entry to a local step, including its formed source and target displays. -/
theorem State.LocalStep.insert {s t : State} (h : s.LocalStep t) (q : FName) (A : Ty)
    (body : RawTerm 0) (hb : IsTerm (domain (s.signature.insert q A)) body)
    (fresh : q ∉ domain t.signature) :
    (s.insert q A body hb).LocalStep
      (t.insert q A body (hb.mono (insert_domain_mono h.sigma_extends q A))) :=
  LocalStep.insert_entry h s.focus_formed s.domains s.entries_formed q A body fresh

/-- Store the original focus at q and use q itself as the new focus. -/
def State.inFuture (s : State) (q : FName) (A : Ty) : State :=
  (s.insert q A s.focus (s.focus_formed.mono (insert_domain q A))).withFocus
    (future q) (.atom (.value (.future (by simp [State.insert]))))

theorem Step.sigma_extends {s t} (h : Step s t) : s.signature.Extends t.signature := by
  cases h with
  | focus h => exact h.sigma_extends
  | future _ h hs _ _ => rw [hs]; exact h.sigma_extends

theorem Steps.sigma_extends {s t} (h : Steps s t) : s.signature.Extends t.signature := by
  induction h with
  | refl => exact fun _ _ hp => hp
  | step h _ ih => exact fun p A hp => ih p A (h.sigma_extends p A hp)

/-- Run one supplied step with its focus stored at a fresh future entry. -/
theorem Step.inFuture {s t : State} (h : Step s t) (q : FName) (A : Ty)
    (fresh : q ∉ domain t.signature) : Step (s.inFuture q A) (t.inFuture q A) := by
  have fresh₀ : q ∉ domain s.signature := fun hq => fresh (h.sigma_extends.domain q hq)
  cases h with
  | focus h =>
      let u := t.insert q A s.focus
        (s.focus_formed.mono (fun p hp => insert_domain q A p (h.sigma_extends.domain p hp)))
      apply Step.future (p := q) (body := s.focus) (t := u)
        (by simp [State.inFuture, State.insert, State.withFocus])
      · exact h.insert q A s.focus (s.focus_formed.mono (insert_domain q A)) fresh
      · rfl
      · rfl
      · dsimp [u, State.inFuture, State.insert, State.withFocus]
        rw [insert_twice]
  | @future t _ p body hp hl hs hf hm =>
      have fresh' : q ∉ domain t.signature := by simpa [hs] using fresh
      have hqp : q ≠ p := fun e => fresh₀ (e ▸ s.domains p (mem_domain_of_lookup hp))
      let v := t.insert q A s.focus
        (s.focus_formed.mono (fun p hp => insert_domain q A p (hl.sigma_extends.domain p hp)))
      apply Step.future (p := p) (body := body) (t := v)
        (by change (s.mapping.insert q s.focus)[p]? = some body; rw [insert_lookup _ _ hqp]; exact hp)
      · exact hl.insert q A s.focus (s.focus_formed.mono (insert_domain q A)) fresh'
      · dsimp only [State.inFuture, State.insert, State.withFocus, v]
        rw [hs]
      · rfl
      · dsimp only [State.inFuture, State.insert, State.withFocus, v]
        rw [hm, hf, insert_comm t.mapping t.focus s.focus (Ne.symm hqp)]

theorem State.Final.inFuture {s : State} (h : s.Final) (q : FName) (A : Ty) :
    (s.inFuture q A).Final := by
  refine ⟨.future (by simp [State.inFuture, State.insert, State.withFocus]), ?_⟩
  intro p body hp
  change (s.mapping.insert q s.focus)[p]? = some body at hp
  by_cases he : q = p
  · subst p
    simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hp
    subst body
    exact h.focus.mono (insert_domain q A)
  · rw [insert_lookup s.mapping s.focus he] at hp
    exact (h.entries p body hp).mono (insert_domain q A)

/-- A chosen finite path whose Interleave-Focus sources have value entries.
    Interleave-Future sources are unrestricted. This records the hypothesis of
    the paper's let transport lemma; `steps` forgets it to the existing relation. -/
inductive FocusReadySteps : State → State → Prop where
  | refl {s} : FocusReadySteps s s
  | focus {s t u} :
      (∀ (p : FName) body, s.mapping[p]? = some body → IsValue (domain s.signature) body) →
      s.LocalStep t → FocusReadySteps t u → FocusReadySteps s u
  | future {s t u v : State} {p : FName} {body : RawTerm 0}
      (hp : s.mapping[p]? = some body) :
      (s.withFocus body (s.entries_formed p body hp)).LocalStep t →
      u.signature = t.signature → u.focus = s.focus → u.mapping = t.mapping.insert p t.focus →
      FocusReadySteps u v → FocusReadySteps s v

/-- Every path carrying the extra hypothesis is an ordinary runtime execution. -/
theorem FocusReadySteps.steps {s t} (h : FocusReadySteps s t) : Steps s t := by
  induction h with
  | refl => exact .refl
  | focus _ hl _ ih => exact .step (.focus hl) ih
  | future hp hl hs hf hm _ ih => exact .step (.future hp hl hs hf hm) ih

/-- Retain the signature and mapping, enclosing only the focus in let. -/
def State.underLet (s : State) (body : RawTerm 1) (hb : IsTerm (domain s.signature) body) : State :=
  s.withFocus (letE s.focus body) (.letE s.focus_formed hb)

/-- Search-Let transports focus steps under the value-entry hypothesis;
    selected-future steps keep exactly their original mapping write-back. -/
theorem FocusReadySteps.underLet {s t} (h : FocusReadySteps s t) (body : RawTerm 1)
    (hb : IsTerm (domain s.signature) body) :
    FocusReadySteps (s.underLet body hb)
      (t.underLet body (hb.mono h.steps.sigma_extends.domain)) := by
  induction h with
  | refl => exact .refl
  | @focus s t u ready hl rest ih =>
      refine FocusReadySteps.focus (s := s.underLet body hb)
        (t := t.underLet body (hb.mono hl.sigma_extends.domain)) ready ?_
        (ih (hb.mono hl.sigma_extends.domain))
      apply LocalStep.search_let
      · rintro ⟨k, fn, first, args, p, w, _, _, hp, hn⟩
        exact hn (ready p w hp)
      · exact hl
      · exact hb
  | @future s t u v p w hp hl hs hf hm rest ih =>
      have hbu := hb.mono (Step.sigma_extends (.future hp hl hs hf hm)).domain
      refine FocusReadySteps.future (s := s.underLet body hb) (t := t)
        (u := u.underLet body hbu) hp hl hs ?_ hm (ih hbu)
      dsimp [State.underLet, State.withFocus]; rw [hf]

theorem FocusReadySteps.trans {s t u} (h : FocusReadySteps s t)
    (rest : FocusReadySteps t u) : FocusReadySteps s u := by
  induction h with
  | refl => exact rest
  | focus ready hl _ ih => exact .focus ready hl (ih rest)
  | future hp hl hs hf hm _ ih => exact .future hp hl hs hf hm (ih rest)

/-- At a final endpoint, append Let to instantiate the body with the returned value.
    The constructed path still satisfies the same focus-step condition. -/
theorem FocusReadySteps.let_value {s t} (h : FocusReadySteps s t) (body : RawTerm 1)
    (hb : IsTerm (domain s.signature) body) (final : t.Final) :
    FocusReadySteps (s.underLet body hb)
      (t.withFocus (body.conc t.focus)
        ((hb.mono h.steps.sigma_extends.domain).conc (.value final.focus))) := by
  have hb' := hb.mono h.steps.sigma_extends.domain
  exact (h.underLet body hb).trans
    (.focus (s := t.underLet body hb')
      (t := t.withFocus (body.conc t.focus) (hb'.conc (.value final.focus)))
      final.entries (.let_value final.focus hb') .refl)

/-- The transported focus is a future value, so every selected step advances an entry.
    This gives the path condition required by the completeness construction. -/
theorem Steps.inFuture_ready {s t : State} (h : Steps s t) (q : FName) (A : Ty)
    (fresh : q ∉ domain t.signature) : FocusReadySteps (s.inFuture q A) (t.inFuture q A) := by
  induction h with
  | refl => exact .refl
  | @step s u t hs rest ih =>
      have hf : q ∉ domain u.signature := fun hq => fresh (rest.sigma_extends.domain q hq)
      have lifted := hs.inFuture q A hf
      cases lifted with
      | focus hl =>
          exact False.elim (value_irreducible (.future (by simp [State.inFuture, State.insert, State.withFocus])) hl)
      | future hp hl hsig hfocus hmap =>
          exact .future hp hl hsig hfocus hmap (ih fresh)

end SourceRuntime.Runtime

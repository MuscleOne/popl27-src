import SourceRuntime.Runtime.Readback
import SourceRuntime.Runtime.Preservation

/-!
C-Obs-to-Seq: future-name dependence along a given execution (metatheory.md).
Entries may still be terms. Each entry uses only the preceding names, including
references under binders. Interleave-Future may insert a new name before the
selected name. The final-state argument then supplies HasValueEnumeration.
-/

namespace SourceRuntime.Runtime
open WSLN

/-- A finite dependency enumeration of terms; entries need not be values or closed. -/
inductive HasTermEnumeration : Mapping → Prop where
  | empty : HasTermEnumeration ∅
  | snoc {mu p body} : HasTermEnumeration mu → p ∉ domain mu →
      IsTerm (domain mu) body → HasTermEnumeration (mu.insert p body)

private theorem value_of_formed {U V n} {t : RawTerm n} (ht : IsTerm U t)
    (hv : IsValue V t) : IsValue U t := by
  cases ht with
  | atom ha => cases ha with
    | value hv => exact hv
    | bound | free => cases hv
  | _ => cases hv

private theorem atom_future_mem {U n p} (ha : IsAtom U (future (n := n) p)) : p ∈ U := by
  cases ha with | value hv => exact future_value_iff.mp hv

private theorem atoms_members {U} (vs : List (RawTerm 0)) (hs : IsAtoms U (toArgs vs)) :
    ∀ a ∈ vs, IsAtom U a := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      cases hs with
      | cons hv hs =>
          intro a h
          rcases List.mem_cons.mp h with rfl | h
          · exact hv
          · exact ih hs a h

private theorem ArgMember.branch {U b ms bs ps} (h : ArgMember b (ms := ms) bs)
    (hs : IsBranches U ps bs) : ∃ p, IsBranch U p b := by
  induction h generalizing ps with
  | here => cases hs with | cons hb _ => exact ⟨_, hb⟩
  | there _ ih => cases hs with | cons _ hs => exact ih hs

private theorem MatchBranch.formation {U V v b result p} (h : MatchBranch V v b result)
    (hv : IsAtom U v) (hb : IsBranch U p b) : IsTerm U result := by
  cases hv with
  | bound | free => cases h
  | value hv =>
      cases h <;> cases hv <;> cases hb
      all_goals first
        | exact IsTerm.conc (by assumption) (by assumption)
        | assumption
        | exact (IsTerm.open (by assumption) ⟨0, by decide⟩ (by assumption) rfl).conc (by assumption)

/-- The paper's local formation assertion under a smaller active-name set U.
    Lookup closure is required only for the names in U. -/
theorem LocalStep.formation {sig mu t sig' mu' t'} (h : LocalStep sig mu t sig' mu' t')
    {U : ActiveNames} (ht : IsTerm U t)
    (entries : ∀ (p : FName) body, p ∈ U → mu[p]? = some body → IsTerm U body) :
    (sig' = sig ∧ mu' = mu ∧ IsTerm U t') ∨
    ∃ q A body, q ∉ domain sig ∧ sig' = sig.insert q A ∧ mu' = mu.insert q body ∧
      IsTerm U body ∧ IsTerm (U.insert q) t' := by
  induction h with
  | search_let _ h hb ih =>
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | letE hr hb =>
          rcases ih hr with ⟨hs, hm, hr'⟩ | ⟨q, A, body, fresh, hs, hm, hf, hr'⟩
          · exact .inl ⟨hs, hm, .letE hr' hb⟩
          · exact .inr ⟨q, A, body, fresh, hs, hm, hf,
              .letE hr' (hb.mono (by intro p hp; simp [hp]))⟩
  | beta arity hb hv hvs =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | app hf ha hs =>
          cases hf with | value hf =>
            cases hf with | funE _ _ _ hb =>
              exact (hb.castScope _).instantiate _ (by
                intro a h
                rcases List.mem_cons.mp h with rfl | h
                · exact ha
                · exact atoms_members _ hs a h)
  | fix_beta arity hb hv hvs =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | app hf ha hs =>
          cases hf with | value hf =>
            cases hf with | fixE _ _ _ hb =>
              exact (hb.castScope _).instantiate _ (by
                intro a h
                rcases List.mem_cons.mp h with rfl | h
                · exact .value (.fixE _ _ _ hb)
                · rcases List.mem_cons.mp h with rfl | h
                  · exact ha
                  · exact atoms_members _ hs a h)
  | let_value hv hb =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | letE hr hb => exact hb.conc (.value (value_of_formed hr hv))
  | match_constructor _ _ member matched =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | matchE ha bs _ =>
          obtain ⟨p, hb⟩ := member.branch bs
          exact matched.formation ha hb
  | match_wildcard _ _ _ _ _ member =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | matchE _ bs _ =>
          obtain ⟨p, hb⟩ := member.branch bs
          cases hb with | branch hb => exact hb
  | add | sub | mul => exact .inl ⟨rfl, rfl, .atom (.value (.integer _))⟩
  | eq_int_true | eq_int_false | eq_id_true | eq_id_false | lt_true | lt_false =>
      exact .inl ⟨rfl, rfl, .atom (.value (.boolean _))⟩
  | if_true hy hn =>
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | ifE _ hy _ => exact .inl ⟨rfl, rfl, hy⟩
  | if_false hy hn =>
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | ifE _ _ hn => exact .inl ⟨rfl, rfl, hn⟩
  | spawn_async hb fresh =>
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | async hb => exact .inr ⟨_, _, _, fresh, rfl, rfl, hb, .atom (.value (.future (by simp)))⟩
  | spawn_app _ _ fresh _ =>
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | letE hr hb => exact .inr ⟨_, _, _, fresh, rfl, rfl, hr,
          .letE (.atom (.value (.future (by simp)))) (hb.mono (by intro p hp; simp [hp]))⟩
  | deref_app hp hw =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | app hf ha hs => exact .app (.value (value_of_formed (entries _ _ (atom_future_mem hf) hp) hw)) ha hs
  | deref_op_left hp hw =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | operation op ha hb => exact .operation _ (.value (value_of_formed (entries _ _ (atom_future_mem ha) hp) hw)) hb
  | deref_op_right hp hw =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | operation op ha hb => exact .operation _ ha (.value (value_of_formed (entries _ _ (atom_future_mem hb) hp) hw))
  | deref_if hp hw =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | ifE hg hy hn => exact .ifE (.value (value_of_formed (entries _ _ (atom_future_mem hg) hp) hw)) hy hn
  | deref_match hp hw =>
      refine .inl ⟨rfl, rfl, ?_⟩
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | matchE ha hs patterns =>
          exact .matchE (.value (value_of_formed (entries _ _ (atom_future_mem ha) hp) hw)) hs patterns

private theorem lookup_insert_ne {α} (mu : FMap α) {p q : FName} (body : α) (hne : q ≠ p) :
    (mu.insert q body)[p]? = mu[p]? := by
  simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hne]

private theorem insert_comm (mu : Mapping) {p q : FName} (a b : RawTerm 0) (hne : p ≠ q) :
    (mu.insert p a).insert q b = (mu.insert q b).insert p a := by
  apply Std.ExtTreeMap.ext_getElem?
  intro r
  by_cases hp : p = r
  · subst r
    simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
      if_neg (Ne.symm hne)]
  · by_cases hq : q = r
    · subst r
      simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        if_neg hne]
    · simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
        if_neg hp, if_neg hq]

private theorem insert_twice (mu : Mapping) (p : FName) (a b : RawTerm 0) :
    (mu.insert p a).insert p b = mu.insert p b := by
  apply Std.ExtTreeMap.ext_getElem?
  intro r
  by_cases hp : p = r <;>
    simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hp]

private theorem domain_update (mu : Mapping) {p : FName} (body : RawTerm 0) (hp : p ∈ domain mu) :
    domain (mu.insert p body) = domain mu := by
  rw [domain_insert]
  apply Std.ExtTreeSet.ext_mem
  intro q
  simp only [Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq]
  exact ⟨fun h => h.elim (fun e => e ▸ hp) id, Or.inr⟩

private theorem HasTermEnumeration.entries {mu} (h : HasTermEnumeration mu)
    {p : FName} {body : RawTerm 0} (hp : mu[p]? = some body) : IsTerm (domain mu) body := by
  induction h with
  | empty => simp at hp
  | @snoc mu q v h fresh hv ih =>
      have inc : ∀ p, p ∈ domain mu → p ∈ domain (mu.insert q v) := by
        intro p hp; simp [hp]
      by_cases he : q = p
      · subst p
        simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hp
        subst body
        exact hv.mono inc
      · rw [lookup_insert_ne mu v he] at hp
        exact (ih hp).mono inc

private theorem HasTermEnumeration.prefix_entries {pre mu : Mapping} (h : HasTermEnumeration pre)
    (keep : ∀ (p : FName) body, pre[p]? = some body → mu[p]? = some body) :
    ∀ (p : FName) body, p ∈ domain pre → mu[p]? = some body → IsTerm (domain pre) body := by
  intro p body hp lookup
  have old := Std.ExtTreeMap.getElem?_eq_some_getElem (mem_domain.mp hp)
  have eq := Option.some.inj ((keep p _ old).symm.trans lookup)
  exact eq ▸ h.entries old

-- Recurse down the enumeration to the selected entry. The ambient mapping stays
-- fixed: every prefix lookup is retained in it, even while the proof visits a prefix.
private theorem HasTermEnumeration.future_step {pre} (h : HasTermEnumeration pre)
    {sig mu body sig' mu' result p}
    (keep : ∀ (q : FName) t, pre[q]? = some t → mu[q]? = some t)
    (domains : ∀ q, q ∈ domain mu → q ∈ domain sig)
    (lookup : pre[p]? = some body) (step : LocalStep sig mu body sig' mu' result) :
    (mu' = mu ∧ HasTermEnumeration (pre.insert p result)) ∨
    ∃ q term, q ∉ domain sig ∧ mu' = mu.insert q term ∧
      HasTermEnumeration ((pre.insert q term).insert p result) := by
  induction h generalizing p body with
  | empty => simp at lookup
  | @snoc pre last v h fresh hv ih =>
      have old_lookup {q : FName} {t : RawTerm 0} (hq : pre[q]? = some t) : (pre.insert last v)[q]? = some t := by
        rw [lookup_insert_ne pre (p := q) (q := last) v (fun e => fresh (e ▸ mem_domain_of_lookup hq))]
        exact hq
      have keep₀ : ∀ (q : FName) t, pre[q]? = some t → mu[q]? = some t :=
        fun q t hq => keep q t (old_lookup hq)
      have last_sig : last ∈ domain sig := domains last (mem_domain_of_lookup (keep last v (by simp)))
      by_cases he : last = p
      · subst p
        simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at lookup
        subst body
        rcases step.formation hv (h.prefix_entries keep₀) with
          ⟨_, hm, formed⟩ | ⟨q, A, term, freshq, _, hm, ht, formed⟩
        · refine .inl ⟨hm, ?_⟩
          rw [insert_twice]
          exact .snoc h fresh formed
        · refine .inr ⟨q, term, freshq, hm, ?_⟩
          have hqlast : q ≠ last := fun e => freshq (e ▸ last_sig)
          have hfq : q ∉ domain pre := fun hq =>
            freshq (domains q (mem_domain_of_lookup (keep₀ q _
              (Std.ExtTreeMap.getElem?_eq_some_getElem (mem_domain.mp hq)))))
          rw [insert_comm pre v term (Ne.symm hqlast), insert_twice]
          exact .snoc (.snoc h hfq ht)
            (by simpa [domain_insert, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hqlast] using fresh)
            (by simpa only [domain_insert] using formed)
      · rw [lookup_insert_ne pre v he] at lookup
        have hp : p ∈ domain pre := mem_domain_of_lookup lookup
        rcases ih keep₀ lookup step with ⟨hm, updated⟩ | ⟨q, term, freshq, hm, updated⟩
        · refine .inl ⟨hm, ?_⟩
          rw [insert_comm pre v result he]
          exact .snoc updated (by simpa only [domain_update pre result hp] using fresh)
            (by simpa only [domain_update pre result hp] using hv)
        · refine .inr ⟨q, term, freshq, hm, ?_⟩
          have hqlast : q ≠ last := fun e => freshq (e ▸ last_sig)
          have dom : domain ((pre.insert q term).insert p result) = (domain pre).insert q := by
            rw [domain_update _ result (by simp [hp]), domain_insert]
          rw [insert_comm pre v term (Ne.symm hqlast), insert_comm (pre.insert q term) v result he]
          exact .snoc updated
            (by simpa only [dom, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq,
              hqlast, false_or] using fresh)
            (hv.mono (by intro r hr; rw [dom]; simp [hr]))

/-- Both interleaving rules preserve the existence of a term dependency enumeration. -/
theorem HasTermEnumeration.step {s t : State} (h : HasTermEnumeration s.mapping)
    (hs : s.Ok) (step : Step s t) : HasTermEnumeration t.mapping := by
  cases step with
  | focus step =>
      rcases step.formation (hs.domains ▸ s.focus_formed) (fun _ _ _ hp => h.entries hp) with
        ⟨_, hm, _⟩ | ⟨q, A, body, fresh, _, hm, formed, _⟩
      · rw [hm]; exact h
      · rw [hm]
        exact .snoc h (fun hq => fresh (hs.domains ▸ hq)) formed
  | future hp step _ _ hm =>
      rcases h.future_step (fun _ _ hp => hp) s.domains hp step with
        ⟨eq, result⟩ | ⟨q, body, _, eq, result⟩
      · rw [hm, eq]; exact result
      · rw [hm, eq]; exact result

/-- The enumeration is maintained along the given finite path. -/
theorem HasTermEnumeration.steps {s t : State} (h : HasTermEnumeration s.mapping)
    (hs : s.Ok) (steps : Steps s t) : HasTermEnumeration t.mapping := by
  induction steps with
  | refl => exact h
  | step step _ ih =>
      obtain ⟨A, typed⟩ := hs.focus
      exact ih (h.step hs step) (preservation step hs typed).1

/-- Every state on a finite execution from a well-typed source initial state has the enumeration. -/
theorem initial_term_enumeration {M A s} (ht : Source.HasType [] M A)
    (steps : Steps (initialState M ht.formed) s) : HasTermEnumeration s.mapping :=
  HasTermEnumeration.steps .empty (initial_ok ht) steps

private theorem HasTermEnumeration.to_values {mu V} (h : HasTermEnumeration mu)
    (values : ∀ (p : FName) body, mu[p]? = some body → IsValue V body)
    (closed : ∀ (p : FName) body, mu[p]? = some body → supp body ⊆ ∅) :
    HasValueEnumeration mu := by
  induction h with
  | empty => exact .empty
  | @snoc mu p body h fresh formed ih =>
      have keep {q : FName} {t : RawTerm 0} (hq : mu[q]? = some t) : (mu.insert p body)[q]? = some t := by
        rw [lookup_insert_ne mu (p := q) (q := p) body (fun e => fresh (e ▸ mem_domain_of_lookup hq))]
        exact hq
      exact .snoc (ih (fun _ _ hq => values _ _ (keep hq)) (fun _ _ hq => closed _ _ (keep hq)))
        fresh (value_of_formed formed (values p body (by simp))) (closed p body (by simp))

/-- Finality supplies values; State-Ok supplies their empty source-variable support. -/
theorem State.Final.value_enumeration {s : State} (hf : s.Final) (hs : s.Ok)
    (h : HasTermEnumeration s.mapping) : HasValueEnumeration s.mapping := by
  apply h.to_values hf.entries
  intro p body hp
  have typed_key := Std.ExtTreeMap.getElem?_eq_some_getElem
    (mem_domain.mp (s.domains p (mem_domain_of_lookup hp)))
  exact (hs.entries p body _ hp typed_key).closed

/-- The given final execution supplies exactly the mapping condition needed by read-back. -/
theorem initial_value_enumeration {M A s} (ht : Source.HasType [] M A)
    (steps : Steps (initialState M ht.formed) s) (hf : s.Final) : HasValueEnumeration s.mapping :=
  hf.value_enumeration (preservation_steps steps (initial_ok ht) (ofSource_typing ht)).1
    (initial_term_enumeration ht steps)

end SourceRuntime.Runtime

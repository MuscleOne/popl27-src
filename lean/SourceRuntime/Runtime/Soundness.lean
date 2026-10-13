import SourceRuntime.Runtime.Dependencies
import SourceRuntime.Runtime.Execution

/-!
C-Obs-to-Seq (metatheory.md): read every intermediate state under the fixed final
mapping. Backward induction follows the given execution, simultaneously for its
focus and every mapping entry. It does not construct a different schedule.
-/

namespace SourceRuntime.Runtime
open WSLN

private theorem lookup_insert_ne (mu : Mapping) (w : RawTerm 0) {p q : FName} (hne : q ≠ p) :
    (mu.insert q w)[p]? = mu[p]? := by
  simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hne]

private theorem LocalStep.retain_entry {sig mu t sig' mu' t'}
    (h : LocalStep sig mu t sig' mu' t')
    (domains : ∀ p, p ∈ domain mu → p ∈ domain sig)
    {p : FName} {w : RawTerm 0} (hp : mu[p]? = some w) : mu'[p]? = some w := by
  rcases h.extension with ⟨_, rfl⟩ | ⟨q, A, body, fresh, _, rfl, _⟩
  · exact hp
  · rw [lookup_insert_ne mu body (p := p) (q := q) (fun e => fresh (e ▸ domains p (mem_domain_of_lookup hp)))]
    exact hp

/-- An entry that is already a runtime value is retained along any given path. -/
theorem Steps.retain_value_entry {s t : State} (path : Steps s t) {p : FName} {w : RawTerm 0}
    (hp : s.mapping[p]? = some w) (hw : IsValue (domain s.signature) w) :
    t.mapping[p]? = some w := by
  induction path with
  | refl => exact hp
  | @step s t u step rest ih =>
      apply ih _ (hw.mono step.sigma_extends.domain)
      cases step with
      | focus rule => exact rule.retain_entry s.domains hp
      | @future mid t q body hq rule es ef em =>
          have hne : q ≠ p := by
            intro eqn
            subst q
            have same := Option.some.inj (hq.symm.trans hp)
            subst body
            exact value_irreducible hw rule
          rw [em, lookup_insert_ne _ _ hne]
          exact rule.retain_entry s.domains hp

-- Keep both assertions together: allocation can depend on an entry that the
-- current focus never dereferences, including entries with function type.
private theorem readback_steps {s final : State} (path : Steps s final)
    (h : HasValueEnumeration final.mapping) (ok : final.Ok)
    (ds : ∀ p, p ∈ domain s.signature → p ∈ domain final.mapping) :
    Source.Steps (readback h s.focus (s.focus_formed.mono ds))
      (readback h final.focus (ok.domains ▸ final.focus_formed)) ∧
    ∀ (p : FName) w (hp : s.mapping[p]? = some w),
      Source.Steps (readback h w ((s.entries_formed p w hp).mono ds))
        (readback h (future p) (.atom (.value (.future (ds p (s.domains p (mem_domain_of_lookup hp))))))) := by
  induction path with
  | refl =>
      refine ⟨.refl (readback_formed h _), ?_⟩
      intro p w hp
      rw [readback_future h hp, Trm.weaken_self]
      exact .refl (readback_formed h _)
  | @step s t final step rest ih =>
      have dt : ∀ p, p ∈ domain t.signature → p ∈ domain final.mapping := by
        intro p hp
        exact ok.domains ▸ rest.sigma_extends.domain p hp
      obtain ⟨focus, entries⟩ := ih h ok dt
      have retain (p : FName) (w : RawTerm 0) (hp : s.mapping[p]? = some w)
          (hw : IsValue (domain s.signature) w) : final.mapping[p]? = some w :=
        (Steps.step step rest).retain_value_entry hp hw
      cases step with
      | focus rule =>
          refine ⟨(rule.readback_steps h ds dt retain (fun q w _ hp => entries q w hp)).trans focus, ?_⟩
          intro p w hp
          exact entries p w (rule.retain_entry s.domains hp)
      | @future mid t p body hp rule es ef em =>
          have dm : ∀ q, q ∈ domain mid.signature → q ∈ domain final.mapping := by
            intro q hq
            exact dt q (es.symm ▸ hq)
          have evaluated := rule.readback_steps h ds dm retain (by
            intro q w fresh hq
            have hne : p ≠ q := fun eqn => fresh (eqn ▸ mem_domain_of_lookup hp)
            have stored : t.mapping[q]? = some w := by rw [em, lookup_insert_ne _ _ hne]; exact hq
            exact entries q w stored)
          refine ⟨?_, ?_⟩
          · simpa only [ef] using focus
          · intro q w hq
            by_cases eqn : p = q
            · subst q
              have same := Option.some.inj (hp.symm.trans hq)
              subst w
              exact evaluated.trans (entries p mid.focus (by simp [em]))
            · exact entries q w (by
                rw [em, lookup_insert_ne _ _ eqn]
                exact rule.retain_entry s.domains hq)

/-- C-Obs-to-Seq: every given finite execution with an observation agrees with
    source sequential evaluation, including Spawn-App and either interleaving rule. -/
theorem obs_to_seq {M v A s} (ht : Source.HasType [] M A) (ho : ObservableType A)
    (path : Steps (initialState M ht.formed) s) (observed : s.Observes v) :
    Source.Steps M v := by
  have h := initial_value_enumeration ht path observed.final
  have typed := (preservation_steps path (initial_ok ht) (ofSource_typing ht)).2
  have same := (State.observes_readback h observed.ok observed.final typed ho).unique observed
  have domains : ∀ p, p ∈ domain (initialState M ht.formed).signature → p ∈ domain s.mapping := by
    simp [initialState]
  have result := (readback_steps path h observed.ok domains).1
  rw [same] at result
  change Source.Steps (readback h (ofSource M) (ofSource_term ht.formed)) v at result
  rwa [readback_source h M ht.formed] at result

/-- The paper's at-most-one-observed-value corollary, across two given executions. -/
theorem observed_value_unique {M A s₁ s₂ v₁ v₂} (ht : Source.HasType [] M A) (ho : ObservableType A)
    (path₁ : Steps (initialState M ht.formed) s₁) (obs₁ : s₁.Observes v₁)
    (path₂ : Steps (initialState M ht.formed) s₂) (obs₂ : s₂.Observes v₂) : v₁ = v₂ :=
  (obs_to_seq ht ho path₁ obs₁).value_unique obs₁.unravels.value
    (obs_to_seq ht ho path₂ obs₂) obs₂.unravels.value

end SourceRuntime.Runtime

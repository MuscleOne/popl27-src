import SourceRuntime.Runtime.Readback
import SourceRuntime.Runtime.Execution

/-!
Finite top-level future lookup for C-Seq-to-Obs. A chain stops at a non-future
value; it does not traverse function bodies, arguments or constructor fields.
Each chain is then realised by an existing dereference rule at its demanded position.
-/

namespace SourceRuntime.Runtime
open WSLN

/-- A finite chain of top-level lookups in one fixed mapping. -/
inductive Dereferences (mu : Mapping) : RawTerm 0 → RawTerm 0 → Prop where
  | refl {w} : Dereferences mu w w
  | future {p w v} : mu[p]? = some w → Dereferences mu w v → Dereferences mu (Runtime.future p) v

private theorem Dereferences.retain {mu mu' a b} (h : Dereferences mu a b)
    (keep : ∀ (p : FName) w, mu[p]? = some w → mu'[p]? = some w) : Dereferences mu' a b := by
  induction h with
  | refl => exact .refl
  | future hp _ ih => exact .future (keep _ _ hp) ih

/-- Dependency order ensures that following top-level futures reaches a value head. -/
theorem HasValueEnumeration.exists_nonfuture_value {mu} (hc : HasValueEnumeration mu) {a : RawTerm 0} (ha : IsValue (domain mu) a) :
    ∃ w, IsValue (domain mu) w ∧ (∀ p, w ≠ future p) ∧ Dereferences mu a w := by
  induction hc generalizing a with
  | empty =>
      cases ha with
      | future hp => simp at hp
      | _ =>
          refine ⟨_, ?_, ?_, .refl⟩
          · constructor <;> assumption
          · intro p e; cases e
  | @snoc mu q v hc fresh hv closed ih =>
      have inc : ∀ p, p ∈ domain mu → p ∈ domain (mu.insert q v) := by
        intro p hp; simp [domain_insert, hp]
      have keep : ∀ (p : FName) w, mu[p]? = some w → (mu.insert q v)[p]? = some w := by
        intro p w hp
        have hqp : q ≠ p := fun e => fresh (e ▸ mem_domain_of_lookup hp)
        simpa [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hqp] using hp
      cases ha with
      | future hp =>
          simp only [domain_insert, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq] at hp
          rcases hp with rfl | hp
          · obtain ⟨w, hw, hn, chain⟩ := ih hv
            exact ⟨w, hw.mono inc, hn, .future (by simp) (chain.retain keep)⟩
          · obtain ⟨w, hw, hn, chain⟩ := ih (.future hp)
            exact ⟨w, hw.mono inc, hn, chain.retain keep⟩
      | _ =>
          refine ⟨_, ?_, ?_, .refl⟩
          · constructor <;> assumption
          · intro p e; cases e

/-- Lookup changes only the chosen runtime occurrence, not its reconstructed source value. -/
theorem Dereferences.readback_eq {mu a b} (h : Dereferences mu a b) (hc : HasValueEnumeration mu)
    (ha : IsValue (domain mu) a) (hb : IsValue (domain mu) b) :
    Runtime.readback hc a (.atom (.value ha)) = Runtime.readback hc b (.atom (.value hb)) := by
  induction h with
  | refl => rfl
  | future hp rest ih =>
      rw [readback_future hc hp, Trm.weaken_self]
      exact ih (hc.entries hp).1 hb

/-- Realise the chain using one of the five existing demanded-position rules.
    C supplies that position and its formation, without a new evaluation-context syntax. -/
theorem Dereferences.lift {s : State} {a b} (h : Dereferences s.mapping a b)
    (hc : HasValueEnumeration s.mapping) (hs : s.Ok)
    (ha : IsValue (domain s.mapping) a) (hb : IsValue (domain s.mapping) b)
    (C : RawTerm 0 → RawTerm 0)
    (formed : ∀ w, IsValue (domain s.mapping) w → IsTerm (domain s.signature) (C w))
    (step : ∀ (p : FName) w, s.mapping[p]? = some w → IsValue (domain s.signature) w →
      LocalStep s.signature s.mapping (C (Runtime.future p)) s.signature s.mapping (C w)) :
    FocusReadySteps (s.withFocus (C a) (formed a ha)) (s.withFocus (C b) (formed b hb)) := by
  induction h with
  | refl => exact .refl
  | @future p w v hp rest ih =>
      have hw := (hc.entries hp).1
      exact .focus (t := s.withFocus (C w) (formed w hw))
        (fun p w hp => hs.domains ▸ (hc.entries hp).1)
        (step p w hp (hs.domains ▸ hw)) (ih hw hb)

end SourceRuntime.Runtime

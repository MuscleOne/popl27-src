import SourceRuntime.Runtime.Typing

/-!
Runtime §8: value unravelling and final-state observation.
Unravelling records the 11 rule schemas on raw trees. Unravels restricts
them to the paper's formed subjects and source-value results, as State.LocalStep
restricts local derivations to formed states. State.Observes adds Ok and Final
only at the state level, as required by Unravel-State.
-/

namespace SourceRuntime.Runtime

/-- Finite derivations of the value-unravelling rules, with one fixed mapping. -/
inductive Unravelling (mu : Mapping) : RawTerm 0 → Source.RawTerm 0 → Prop where
  | integer (z : Int) : Unravelling mu (integer z) (Source.integer z)
  | true : Unravelling mu (boolean true) (Source.boolean true)
  | false : Unravelling mu (boolean false) (Source.boolean false)
  | unit : Unravelling mu unit Source.unit
  | identifier (i : Source.Id) : Unravelling mu (identifier i) (Source.identifier i)
  | future {p w v} : mu[p]? = some w → Unravelling mu w v → Unravelling mu (future p) v
  | sexp_int {w v} : Unravelling mu w v → Unravelling mu (sexp_int w) (Source.sexp_int v)
  | sexp_bool {w v} : Unravelling mu w v → Unravelling mu (sexp_bool w) (Source.sexp_bool v)
  | sexp_id {w v} : Unravelling mu w v → Unravelling mu (sexp_id w) (Source.sexp_id v)
  | nil : Unravelling mu nil Source.nil
  | pair {w₁ w₂ v₁ v₂} : Unravelling mu w₁ v₁ → Unravelling mu w₂ v₂ →
      Unravelling mu (pair w₁ w₂) (Source.pair v₁ v₂)

/-- The auxiliary judgment μ ⊢ w ↝ v, with exactly the carrier conditions of §8.2. -/
structure Unravels (mu : Mapping) (w : RawTerm 0) (v : Source.RawTerm 0) : Prop where
  formed : ∃ U : ActiveNames,
    (∀ p, p ∈ domain mu → p ∈ U) ∧ IsValue U w ∧
    (∀ (p : FName) (body : RawTerm 0), mu[p]? = some body → IsTerm U body)
  value : Source.IsValue v
  derivation : Unravelling mu w v

/-- Induction follows the first derivation, including when a future lookup grows the tree. -/
theorem Unravelling.unique {mu w v₁ v₂} (h₁ : Unravelling mu w v₁)
    (h₂ : Unravelling mu w v₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ with
  | integer z => cases h₂; rfl
  | true => cases h₂; rfl
  | false => cases h₂; rfl
  | unit => cases h₂; rfl
  | identifier i => cases h₂; rfl
  | future hp _ ih =>
      cases h₂ with
      | future hp' h =>
          cases Option.some.inj (hp.symm.trans hp')
          exact ih h
  | sexp_int _ ih =>
      cases h₂ with
      | sexp_int h => exact congrArg Source.sexp_int (ih h)
  | sexp_bool _ ih =>
      cases h₂ with
      | sexp_bool h => exact congrArg Source.sexp_bool (ih h)
  | sexp_id _ ih =>
      cases h₂ with
      | sexp_id h => exact congrArg Source.sexp_id (ih h)
  | nil => cases h₂; rfl
  | pair _ _ ih₁ ih₂ =>
      cases h₂ with
      | pair h₁ h₂ => rw [ih₁ h₁, ih₂ h₂]

/-- O-Unique-Unravelling: two unfoldings of the same value under μ agree. -/
theorem Unravels.unique {mu w v₁ v₂} (h₁ : Unravels mu w v₁)
    (h₂ : Unravels mu w v₂) : v₁ = v₂ :=
  h₁.derivation.unique h₂.derivation

/-- Outputs of field derivations are values, hence atoms for source constructor typing. -/
theorem Unravelling.value {mu w v} (h : Unravelling mu w v) : Source.IsValue v := by
  induction h with
  | integer z => exact .integer z
  | true => exact .boolean Bool.true
  | false => exact .boolean Bool.false
  | unit => exact .unit
  | identifier i => exact .identifier i
  | future _ _ ih => exact ih
  | sexp_int _ ih => exact .sexp_int (.value ih)
  | sexp_bool _ ih => exact .sexp_bool (.value ih)
  | sexp_id _ ih => exact .sexp_id (.value ih)
  | nil => exact .nil
  | pair _ _ ih₁ ih₂ => exact .pair (.value ih₁) (.value ih₂)

/-- The induction uses consistent types at each successful future lookup. -/
theorem Unravelling.preserves_type {sig mu w v A} (h : Unravelling mu w v)
    (entries : ∀ (p : FName) body B, mu[p]? = some body → sig[p]? = some B →
      HasType sig [] body B)
    (ht : HasType sig [] w A) : Source.HasType [] v A := by
  induction h generalizing A with
  | integer z => cases ht; exact .integer z
  | true => cases ht; exact .boolean Bool.true
  | false => cases ht; exact .boolean Bool.false
  | unit => cases ht; exact .unit
  | identifier i => cases ht; exact .identifier i
  | future hp _ ih => exact ih (entries _ _ _ hp (typing_future_iff.mp ht))
  | sexp_int hv ih =>
      cases ht with
      | sexp_int _ hw => exact .sexp_int (.value hv.value) (ih hw)
  | sexp_bool hv ih =>
      cases ht with
      | sexp_bool _ hw => exact .sexp_bool (.value hv.value) (ih hw)
  | sexp_id hv ih =>
      cases ht with
      | sexp_id _ hw => exact .sexp_id (.value hv.value) (ih hw)
  | nil => cases ht; exact .nil
  | pair hv₁ hv₂ ih₁ ih₂ =>
      cases ht with
      | pair _ _ hw₁ hw₂ => exact .pair (.value hv₁.value) (.value hv₂.value) (ih₁ hw₁) (ih₂ hw₂)

/-- O-Unravelling-Type retains the paper's domain equality; the induction above
    needs only consistency at visited entries, not finality of the whole mapping. -/
theorem Unravels.preserves_type {sig mu w v A} (h : Unravels mu w v)
    (_domains : domain mu = domain sig)
    (entries : ∀ (p : FName) body B, mu[p]? = some body → sig[p]? = some B →
      HasType sig [] body B)
    (ht : HasType sig [] w A) : Source.HasType [] v A :=
  h.derivation.preserves_type entries ht

/-- WSLN support records free source variables. Empty membership expresses FV(v) = ∅;
    Fset itself retains the syntax of unions, so structural equality to ∅ would be too strong. -/
theorem Unravelling.closed {mu w v} (h : Unravelling mu w v) : WSLN.supp v ⊆ ∅ := by
  induction h with
  | integer _ | true | false | unit | identifier _ | nil => exact WSLN.Fset.empty_subset
  | future _ _ ih => exact ih
  | sexp_int _ ih | sexp_bool _ ih | sexp_id _ ih =>
      exact WSLN.Fset.union_subset ih WSLN.Fset.empty_subset
  | pair _ _ ih₁ ih₂ =>
      exact WSLN.Fset.union_subset ih₁ (WSLN.Fset.union_subset ih₂ WSLN.Fset.empty_subset)

/-- Unravel-State (§8.3): the three paper premises for S ↝ v. -/
structure State.Observes (s : State) (v : Source.RawTerm 0) : Prop where
  ok : s.Ok
  final : s.Final
  unravels : Unravels s.mapping s.focus v

/-- O-State, first clause: observations of the same state agree. -/
theorem State.Observes.unique {s : State} {v₁ v₂}
    (h₁ : s.Observes v₁) (h₂ : s.Observes v₂) : v₁ = v₂ :=
  h₁.unravels.unique h₂.unravels

/-- O-State, closedness: the observed source value has no free source variables. -/
theorem State.Observes.closed {s : State} {v} (h : s.Observes v) : WSLN.supp v ⊆ ∅ :=
  h.unravels.derivation.closed

/-- O-State, typing: retain the specified focus type, using the mapping premises of Ok. -/
theorem State.Observes.preserves_type {s : State} {v A} (h : s.Observes v)
    (ht : HasType s.signature [] s.focus A) : Source.HasType [] v A :=
  h.unravels.preserves_type h.ok.domains h.ok.entries ht

end SourceRuntime.Runtime

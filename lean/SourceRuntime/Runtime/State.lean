import SourceRuntime.Runtime.Syntax
import Std.Data.ExtTreeMap

/-!
Runtime §§2.3–3 and State-Final (§5).
Finite maps use the standard library's extensional equality and insert/lookup.
State contains exactly the three formation conditions; State.Ok is in Typing.
Future names are retained, not quotiented by state-level alpha-equivalence.
-/

namespace SourceRuntime.Runtime

abbrev FMap (α : Type) := Std.ExtTreeMap FName α (compareOn FName.index)
abbrev Signature := FMap Source.Ty
abbrev Mapping := FMap (RawTerm 0)

/-- The finite set of keys; map entries have no semantic ordering. -/
def domain {α : Type} (φ : FMap α) : ActiveNames :=
  .ofList φ.keys (cmp := compareOn FName.index)

@[simp] theorem mem_domain {α : Type} {φ : FMap α} {p : FName} :
    p ∈ domain φ ↔ p ∈ φ := by
  simp [domain, Std.ExtTreeSet.mem_ofList, Std.ExtTreeMap.mem_keys]

theorem mem_domain_of_lookup {α : Type} {φ : FMap α} {p : FName} {a : α}
    (h : φ[p]? = some a) : p ∈ domain φ := by
  rw [mem_domain, Std.ExtTreeMap.mem_iff_isSome_getElem?, h]
  rfl

@[simp] theorem domain_empty {α : Type} : domain (∅ : FMap α) = ∅ := by
  simp [domain]

@[simp] theorem domain_insert {α : Type} (φ : FMap α) (p : FName) (a : α) :
    domain (φ.insert p a) = (domain φ).insert p := by
  apply Std.ExtTreeSet.ext_mem
  intro q
  simp [Std.ExtTreeMap.mem_insert, Std.ExtTreeSet.mem_insert]

/-- Formed displays νΣ{N ∥ μ}; RawTerm 0 may still have free source variables. -/
structure State where
  signature : Signature
  focus : RawTerm 0
  mapping : Mapping
  domains : ∀ p, p ∈ domain mapping → p ∈ domain signature
  focus_formed : IsTerm (domain signature) focus
  entries_formed : ∀ (p : FName) body,
    mapping[p]? = some body → IsTerm (domain signature) body

/-- State-Final checks only the focus and the entries present in μ. -/
structure State.Final (s : State) : Prop where
  focus : IsValue (domain s.signature) s.focus
  entries : ∀ (p : FName) body,
    s.mapping[p]? = some body → IsValue (domain s.signature) body

/-- R-Sigma-Weakening uses extensions that retain every old declaration's type. -/
def Signature.Extends (sig sig' : Signature) : Prop :=
  ∀ (p : FName) A, sig[p]? = some A → sig'[p]? = some A

theorem Signature.Extends.domain {sig sig' : Signature} (h : sig.Extends sig') :
    ∀ p, p ∈ domain sig → p ∈ domain sig' := by
  intro p hp
  exact mem_domain_of_lookup (h p _ (Std.ExtTreeMap.getElem?_eq_some_getElem (mem_domain.mp hp)))

theorem Signature.extends_insert {sig : Signature} {q : FName} (A : Source.Ty)
    (fresh : q ∉ domain sig) : sig.Extends (sig.insert q A) := by
  intro p B hp
  have hne : q ≠ p := by
    intro e; subst q
    exact fresh (mem_domain_of_lookup hp)
  simpa [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, hne] using hp

/-- A finite signature leaves a fresh future name, used by spawning and alpha-renaming proofs. -/
theorem Signature.exists_fresh (sig : Signature) : ∃ q, q ∉ domain sig := by
  let b := (sig.keys.map FName.index).max?.getD 0
  refine ⟨⟨b + 1⟩, ?_⟩
  intro hp
  have hm : b + 1 ∈ sig.keys.map FName.index :=
    List.mem_map.mpr ⟨⟨b + 1⟩, (Std.ExtTreeMap.mem_keys).mpr (mem_domain.mp hp), rfl⟩
  have := List.le_max?_getD_of_mem (k := 0) hm
  change b + 1 ≤ b at this
  omega

end SourceRuntime.Runtime

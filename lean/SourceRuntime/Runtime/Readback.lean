import SourceRuntime.Runtime.Source
import SourceRuntime.Runtime.Observation
import SourceRuntime.Runtime.Reduction

/-!
The proof-only read-back in metatheory.md, C-Seq-to-Obs and C-Obs-to-Seq.
HasValueEnumeration records a finite dependency enumeration of closed value entries.
It is not a State-Ok premise or a runtime scheduling condition.
-/

namespace SourceRuntime.Runtime
open WSLN

/-- A finite dependency enumeration of runtime values: each entry has no free
    source variables and uses only future names from the preceding entries. -/
inductive HasValueEnumeration : Mapping → Prop where
  | empty : HasValueEnumeration ∅
  | snoc {mu q w} : HasValueEnumeration mu → q ∉ domain mu →
      IsValue (domain mu) w → supp w ⊆ ∅ → HasValueEnumeration (mu.insert q w)

-- Structural reconstruction with already reconstructed future values.
-- Only the wrapper below gives this traversal its mapping interpretation.
mutual
private def readbackWith (ρ : FName → Source.RawTerm 0) {n} : RawTerm n → Source.RawTerm n
  | .var i => .var i
  | .atom x => .atom x
  | .op (.future p) .nil => (ρ p).weaken n (Nat.zero_le n)
  | .op (.source o) args => .op o (readbackArgsWith ρ args)

private def readbackArgsWith (ρ : FName → Source.RawTerm 0) {n ms} :
    Arg signature n ms → Arg Source.signature n ms
  | .nil => .nil
  | .cons t rest => .cons (readbackWith ρ t) (readbackArgsWith ρ rest)
end

mutual
private theorem readbackWith_weaken (ρ : FName → Source.RawTerm 0) {m n}
    (t : RawTerm m) (h : m ≤ n) :
    readbackWith ρ (t.weaken n h) = (readbackWith ρ t).weaken n h := by
  match t with
  | .var _ | .atom _ => rfl
  | .op (.future p) .nil => exact (Trm.weaken_trans (ρ p) m n (by omega) h (by omega)).symm
  | .op (.source o) args => exact congrArg (Trm.op (Sg := Source.signature) o) (readbackArgsWith_weaken ρ args h)
termination_by structural t

private theorem readbackArgsWith_weaken (ρ : FName → Source.RawTerm 0) {m n ms}
    (args : Arg signature m ms) (h : m ≤ n) :
    readbackArgsWith ρ (args.weaken n h) = (readbackArgsWith ρ args).weaken n h := by
  match args with
  | .nil => rfl
  | .cons t rest =>
      change Arg.cons (readbackWith ρ (t.weaken _ _)) (readbackArgsWith ρ (rest.weaken n h)) = _
      rw [readbackWith_weaken, readbackArgsWith_weaken]
      rfl
termination_by structural args
end

mutual
private theorem readbackWith_source (ρ : FName → Source.RawTerm 0) {n} (t : Source.RawTerm n) :
    readbackWith ρ (ofSource t) = t := by
  match t with
  | .var _ | .atom _ => rfl
  | .op o args => exact congrArg (Trm.op (Sg := Source.signature) o) (readbackArgsWith_source ρ args)
termination_by structural t

private theorem readbackArgsWith_source (ρ : FName → Source.RawTerm 0) {n ms}
    (args : Arg Source.signature n ms) : readbackArgsWith ρ (ofSourceArgs args) = args := by
  match args with
  | .nil => rfl
  | .cons t rest =>
      change Arg.cons (readbackWith ρ (ofSource t)) (readbackArgsWith ρ (ofSourceArgs rest)) = _
      rw [readbackWith_source, readbackArgsWith_source]
termination_by structural args
end

mutual
private theorem readbackWith_supp (ρ : FName → Source.RawTerm 0)
    (closed : ∀ p, supp (ρ p) ⊆ ∅) {n} (t : RawTerm n) (x : WSLN.Atom) :
    x ∈ supp (readbackWith ρ t) ↔ x ∈ supp t := by
  match t with
  | .var _ | .atom _ => rfl
  | .op (.future p) .nil =>
      change x ∈ supp ((ρ p).weaken n _) ↔ x ∈ (∅ : Fset)
      rw [Trm.supp_weaken]
      exact ⟨fun hx => closed p hx, fun hx => by cases hx⟩
  | .op (.source o) args => exact readbackArgsWith_supp ρ closed args x
termination_by structural t

private theorem readbackArgsWith_supp (ρ : FName → Source.RawTerm 0)
    (closed : ∀ p, supp (ρ p) ⊆ ∅) {n ms} (args : Arg signature n ms) (x : WSLN.Atom) :
    x ∈ supp (readbackArgsWith ρ args) ↔ x ∈ supp args := by
  match args with
  | .nil => rfl
  | .cons t rest =>
      change x ∈ supp (Arg.cons (readbackWith ρ t) (readbackArgsWith ρ rest)) ↔ _
      simp only [supp_cons, Fset.mem_union_iff, readbackWith_supp ρ closed t x,
        readbackArgsWith_supp ρ closed rest x]
termination_by structural args
end

mutual
private theorem IsValue.readback_congr {U n t ρ ρ'} (ht : IsValue U (n := n) t)
    (h : ∀ p, p ∈ U → ρ p = ρ' p) : readbackWith ρ t = readbackWith ρ' t := by
  match ht with
  | .integer _ | .boolean _ | .unit | .identifier _ | .nil => rfl
  | .future hp => exact congrArg (fun v : Source.RawTerm 0 => v.weaken n (Nat.zero_le n)) (h _ hp)
  | .funE A As B hb => exact congrArg (Source.funE A As B) (hb.readback_congr h)
  | .fixE A As B hb => exact congrArg (Source.fixE A As B) (hb.readback_congr h)
  | .sexp_int ha => exact congrArg Source.sexp_int (ha.readback_congr h)
  | .sexp_bool ha => exact congrArg Source.sexp_bool (ha.readback_congr h)
  | .sexp_id ha => exact congrArg Source.sexp_id (ha.readback_congr h)
  | .pair ha hb =>
      change Source.pair _ _ = Source.pair _ _
      rw [ha.readback_congr h, hb.readback_congr h]
termination_by structural ht

private theorem IsAtom.readback_congr {U n t ρ ρ'} (ht : IsAtom U (n := n) t)
    (h : ∀ p, p ∈ U → ρ p = ρ' p) : readbackWith ρ t = readbackWith ρ' t := by
  match ht with
  | .bound _ | .free _ => rfl
  | .value hv => exact hv.readback_congr h
termination_by structural ht

private theorem IsTerm.readback_congr {U n t ρ ρ'} (ht : IsTerm U (n := n) t)
    (h : ∀ p, p ∈ U → ρ p = ρ' p) : readbackWith ρ t = readbackWith ρ' t := by
  match ht with
  | .atom ha => exact ha.readback_congr h
  | .operation op ha hb =>
      change Source.operation op _ _ = Source.operation op _ _
      rw [ha.readback_congr h, hb.readback_congr h]
  | .app hf ha hs =>
      change Source.app _ _ _ = Source.app _ _ _
      rw [hf.readback_congr h, ha.readback_congr h, hs.readback_congr h]
  | .ifE hg hy hn =>
      change Source.ifE _ _ _ = Source.ifE _ _ _
      rw [hg.readback_congr h, hy.readback_congr h, hn.readback_congr h]
  | .letE hr hb =>
      change Source.letE _ _ = Source.letE _ _
      rw [hr.readback_congr h, hb.readback_congr h]
  | .async hb => exact congrArg Source.async (hb.readback_congr h)
  | .matchE ha hs _ =>
      change Source.matchE _ _ = Source.matchE _ _
      rw [ha.readback_congr h, hs.readback_congr h]
termination_by structural ht

private theorem IsBranch.readback_congr {U n p t ρ ρ'} (ht : IsBranch U p (n := n) t)
    (h : ∀ p, p ∈ U → ρ p = ρ' p) : readbackWith ρ t = readbackWith ρ' t := by
  match ht with
  | .branch hb => exact congrArg (Source.branch p) (hb.readback_congr h)
termination_by structural ht

private theorem IsBranches.readback_congr {U n ps ms ts ρ ρ'}
    (ht : IsBranches U ps (n := n) (ms := ms) ts) (h : ∀ p, p ∈ U → ρ p = ρ' p) :
    readbackArgsWith ρ ts = readbackArgsWith ρ' ts := by
  match ht with
  | .nil => rfl
  | .cons hb hs =>
      change Arg.cons _ _ = Arg.cons _ _
      rw [hb.readback_congr h, hs.readback_congr h]
termination_by structural ht

private theorem IsAtoms.readback_congr {U n ms ts ρ ρ'}
    (ht : IsAtoms U (n := n) (ms := ms) ts) (h : ∀ p, p ∈ U → ρ p = ρ' p) :
    readbackArgsWith ρ ts = readbackArgsWith ρ' ts := by
  match ht with
  | .nil => rfl
  | .cons ha hs =>
      change Arg.cons _ _ = Arg.cons _ _
      rw [ha.readback_congr h, hs.readback_congr h]
termination_by structural ht
end

mutual
private theorem IsValue.readbackWith {U n t ρ} (ht : IsValue U (n := n) t)
    (h : ∀ p, p ∈ U → Source.IsValue (ρ p)) : Source.IsValue (readbackWith ρ t) := by
  match ht with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .nil => exact .nil
  | .future hp => exact (h _ hp).weaken (Nat.zero_le n)
  | .funE A As B hb => exact .funE A As B (hb.readbackWith h)
  | .fixE A As B hb => exact .fixE A As B (hb.readbackWith h)
  | .sexp_int ha => exact .sexp_int (ha.readbackWith h)
  | .sexp_bool ha => exact .sexp_bool (ha.readbackWith h)
  | .sexp_id ha => exact .sexp_id (ha.readbackWith h)
  | .pair ha hb => exact .pair (ha.readbackWith h) (hb.readbackWith h)
termination_by structural ht

private theorem IsAtom.readbackWith {U n t ρ} (ht : IsAtom U (n := n) t)
    (h : ∀ p, p ∈ U → Source.IsValue (ρ p)) : Source.IsAtom (readbackWith ρ t) := by
  match ht with
  | .bound i => exact .bound i
  | .free x => exact .free x
  | .value hv => exact .value (hv.readbackWith h)
termination_by structural ht

private theorem IsTerm.readbackWith {U n t ρ} (ht : IsTerm U (n := n) t)
    (h : ∀ p, p ∈ U → Source.IsValue (ρ p)) : Source.IsTerm (readbackWith ρ t) := by
  match ht with
  | .atom ha => exact .atom (ha.readbackWith h)
  | .operation op ha hb => exact .operation op (ha.readbackWith h) (hb.readbackWith h)
  | .app hf ha hs => exact .app (hf.readbackWith h) (ha.readbackWith h) (hs.readbackWith h)
  | .ifE hg hy hn => exact .ifE (hg.readbackWith h) (hy.readbackWith h) (hn.readbackWith h)
  | .letE hr hb => exact .letE (hr.readbackWith h) (hb.readbackWith h)
  | .async hb => exact .async (hb.readbackWith h)
  | .matchE ha hs hf => exact .matchE (ha.readbackWith h) (hs.readbackWith h) hf
termination_by structural ht

private theorem IsBranch.readbackWith {U n p t ρ} (ht : IsBranch U p (n := n) t)
    (h : ∀ p, p ∈ U → Source.IsValue (ρ p)) : Source.IsBranch p (readbackWith ρ t) := by
  match ht with
  | .branch hb => exact .branch (hb.readbackWith h)
termination_by structural ht

private theorem IsBranches.readbackWith {U n ps ms ts ρ}
    (ht : IsBranches U ps (n := n) (ms := ms) ts)
    (h : ∀ p, p ∈ U → Source.IsValue (ρ p)) : Source.IsBranches ps (readbackArgsWith ρ ts) := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.readbackWith h) (hs.readbackWith h)
termination_by structural ht

private theorem IsAtoms.readbackWith {U n ms ts ρ}
    (ht : IsAtoms U (n := n) (ms := ms) ts)
    (h : ∀ p, p ∈ U → Source.IsValue (ρ p)) : Source.IsAtoms (readbackArgsWith ρ ts) := by
  match ht with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.readbackWith h) (hs.readbackWith h)
termination_by structural ht
end

private theorem lookup_insert_ne {α} (mu : FMap α) {q p : FName} (w : α) (h : q ≠ p) :
    (mu.insert q w)[p]? = mu[p]? := by
  simp [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, h]

/-- Every enumerated entry is a closed value under the entire mapping domain. -/
theorem HasValueEnumeration.entries {mu} (h : HasValueEnumeration mu) {p : FName} {w : RawTerm 0} (hp : mu[p]? = some w) :
    IsValue (domain mu) w ∧ supp w ⊆ ∅ := by
  induction h with
  | empty => simp at hp
  | @snoc mu q v h fresh hv closed ih =>
      have inc : ∀ p, p ∈ domain mu → p ∈ domain (mu.insert q v) := by
        intro p hp; simp [domain_insert, hp]
      by_cases he : q = p
      · subst p
        simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hp
        subst w
        exact ⟨hv.mono inc, closed⟩
      · rw [lookup_insert_ne mu v he] at hp
        exact ⟨(ih hp).1.mono inc, (ih hp).2⟩

-- Values outside dom(mu) are irrelevant. They are kept closed so the raw traversal
-- can reuse WSLN's substitution laws without carrying a scope proof through every child.
private structure Expansion (mu : Mapping) where
  entry : FName → Source.RawTerm 0
  closed : ∀ p, supp (entry p) ⊆ ∅
  value : ∀ p, p ∈ domain mu → Source.IsValue (entry p)
  lookup : ∀ p w, mu[p]? = some w → entry p = readbackWith entry w

private theorem HasValueEnumeration.nonempty_expansion {mu} (h : HasValueEnumeration mu) : Nonempty (Expansion mu) := by
  induction h with
  | empty =>
      exact ⟨⟨fun _ => Source.unit, fun _ => Fset.empty_subset, by simp, by simp⟩⟩
  | @snoc mu q w hc fresh hw closed ih =>
      obtain ⟨old⟩ := ih
      let v := readbackWith old.entry w
      let ρ := updateFn old.entry q v
      have same : ∀ p, p ∈ domain mu → ρ p = old.entry p := by
        intro p hp
        exact updateFn_neq old.entry v (fun e => fresh (e ▸ hp))
      have hv : Source.IsValue v := hw.readbackWith old.value
      have cv : supp v ⊆ ∅ := by
        intro x hx
        exact closed ((readbackWith_supp old.entry old.closed w x).mp hx)
      refine ⟨⟨ρ, ?_, ?_, ?_⟩⟩
      · intro p
        by_cases he : q = p
        · subst p; simpa [ρ] using cv
        · simpa [ρ, updateFn, he] using old.closed p
      · intro p hp
        simp only [domain_insert, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq] at hp
        rcases hp with rfl | hp
        · simpa [ρ] using hv
        · rw [same p hp]; exact old.value p hp
      · intro p body hp
        by_cases he : q = p
        · subst p
          simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hp
          subst body
          change ρ q = readbackWith ρ w
          rw [show ρ q = v from updateFn_eq old.entry q v]
          exact (hw.readback_congr same).symm
        · rw [lookup_insert_ne mu w he] at hp
          rw [same p (mem_domain_of_lookup hp), old.lookup p body hp]
          exact ((hc.entries hp).1.readback_congr same).symm

/-- The future equations determine every declared name, independently of the enumeration. -/
private theorem HasValueEnumeration.unique {mu} (h : HasValueEnumeration mu) (ρ ρ' : FName → Source.RawTerm 0)
    (eqs : ∀ p w, mu[p]? = some w → ρ p = readbackWith ρ w)
    (eqs' : ∀ p w, mu[p]? = some w → ρ' p = readbackWith ρ' w) :
    ∀ p, p ∈ domain mu → ρ p = ρ' p := by
  induction h with
  | empty => simp
  | @snoc mu q w hc fresh hw closed ih =>
      have old_lookup {p : FName} {v : RawTerm 0} (hp : mu[p]? = some v) : (mu.insert q w)[p]? = some v := by
        have hqp : q ≠ p := fun e => fresh (e ▸ mem_domain_of_lookup hp)
        rw [lookup_insert_ne mu w hqp]
        exact hp
      have same := ih (fun p v hp => eqs p v (old_lookup hp))
        (fun p v hp => eqs' p v (old_lookup hp))
      intro p hp
      simp only [domain_insert, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq] at hp
      rcases hp with rfl | hp
      · rw [eqs q w (by simp), eqs' q w (by simp)]
        exact hw.readback_congr same
      · exact same p hp

private noncomputable def HasValueEnumeration.expansion {mu} (h : HasValueEnumeration mu) : Expansion mu :=
  Classical.choice h.nonempty_expansion

/-- Paper read-back on its stated domain. The formation argument excludes all undefined lookups. -/
noncomputable def readback {mu n} (h : HasValueEnumeration mu) (t : RawTerm n)
    (_ht : IsTerm (domain mu) t) : Source.RawTerm n := readbackWith h.expansion.entry t

theorem readback_formed {mu n t} (h : HasValueEnumeration mu) (ht : IsTerm (domain mu) (n := n) t) :
    Source.IsTerm (readback h t ht) := ht.readbackWith h.expansion.value

theorem readback_value {mu n t} (h : HasValueEnumeration mu) (hv : IsValue (domain mu) (n := n) t) :
    Source.IsValue (readback h t (.atom (.value hv))) := hv.readbackWith h.expansion.value

/-- The defining future equation is justified by the finite dependency construction. -/
theorem readback_future {mu n} (h : HasValueEnumeration mu) {p : FName} {w : RawTerm 0}
    (hp : mu[p]? = some w) :
    readback h (future (n := n) p) (.atom (.value (.future (mem_domain_of_lookup hp)))) =
      (readback h w (.atom (.value (h.entries hp).1))).weaken n (Nat.zero_le n) :=
  congrArg (fun v : Source.RawTerm 0 => v.weaken n (Nat.zero_le n)) (h.expansion.lookup p w hp)

theorem readback_source {mu n} (h : HasValueEnumeration mu) (t : Source.RawTerm n) (ht : Source.IsTerm t) :
    readback h (ofSource t) (ofSource_term ht) = t := readbackWith_source h.expansion.entry t

/-- Retaining old entries leaves read-back of every old formed term unchanged. -/
theorem readback_extension {mu mu' n t} (h : HasValueEnumeration mu) (h' : HasValueEnumeration mu')
    (retain : ∀ (p : FName) w, mu[p]? = some w → mu'[p]? = some w)
    (ht : IsTerm (domain mu) (n := n) t) (ht' : IsTerm (domain mu') t) :
    readback h' t ht' = readback h t ht := by
  exact ht.readback_congr (h.unique h'.expansion.entry h.expansion.entry
    (fun p w hp => h'.expansion.lookup p w (retain p w hp)) h.expansion.lookup)

mutual
private theorem readbackWith_open (ρ : FName → Source.RawTerm 0) {m n}
    (t : RawTerm m) (i : Fin m) (a : RawTerm 0) (e : m = n + 1) :
    readbackWith ρ (opn i a t e) = opn i (readbackWith ρ a) (readbackWith ρ t) e := by
  match t with
  | .var j =>
      by_cases h : i = j
      · subst j; simp only [opn_var_eq, readbackWith, readbackWith_weaken]
      · simp only [opn_var_ne a e h, readbackWith, opn_var_ne (readbackWith ρ a) e h]
  | .atom _ => rfl
  | .op (.future p) .nil =>
      exact (opn_lt i (readbackWith ρ a) e (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (ρ p)).symm
  | .op (.source o) args =>
      exact congrArg (Trm.op (Sg := Source.signature) o) (readbackArgsWith_open ρ args i a e)
termination_by structural t

private theorem readbackArgsWith_open (ρ : FName → Source.RawTerm 0) {m n ms}
    (args : Arg signature m ms) (i : Fin m) (a : RawTerm 0) (e : m = n + 1) :
    readbackArgsWith ρ (opnArg i a args e) = opnArg i (readbackWith ρ a) (readbackArgsWith ρ args) e := by
  match args with
  | .nil => rfl
  | .cons t rest =>
      change Arg.cons (readbackWith ρ (opn _ a t _)) (readbackArgsWith ρ (opnArg i a rest e)) = _
      rw [readbackWith_open, readbackArgsWith_open]
      rfl
termination_by structural args
end

/-- WSLN opening commutes with reconstruction at every binder depth. -/
theorem readback_open {mu m n t a} (h : HasValueEnumeration mu) (ht : IsTerm (domain mu) (n := m) t)
    (i : Fin m) (ha : IsAtom (domain mu) (n := 0) a) (e : m = n + 1) :
    readback h (opn i a t e) (ht.open i ha e) =
      opn i (readback h a (.atom ha)) (readback h t ht) e :=
  readbackWith_open h.expansion.entry t i a e

theorem readback_conc {mu n body a} (h : HasValueEnumeration mu)
    (hb : IsTerm (domain mu) (n := n + 1) body) (ha : IsAtom (domain mu) (n := 0) a) :
    readback h (body.conc a) (hb.open _ ha rfl) =
      (readback h body hb).conc (readback h a (.atom ha)) :=
  readback_open h hb _ ha rfl

/-- Reflection is needed for the zero-step case of the completeness induction. -/
theorem readback_value_iff {mu n t} (h : HasValueEnumeration mu) (ht : IsTerm (domain mu) (n := n) t) :
    Source.IsValue (readback h t ht) ↔ IsValue (domain mu) t := by
  constructor
  · intro hv
    cases ht with
    | atom ha => cases ha with
      | value hw => exact hw
      | bound | free => cases hv
    | _ => cases hv
  · intro hv; exact readback_value h hv

/-- The five result types of runtime §8; there is no function-unravelling rule. -/
def ObservableType : Source.Ty → Prop
  | .int | .bool | .unit | .id | .sexp => True
  | .arrow _ _ _ => False

mutual
private theorem IsValue.readback_unravelling {U t ρ sig mu A} (hf : IsValue U (n := 0) t)
    (ht : HasType sig [] t A) (ho : ObservableType A)
    (futures : ∀ p B, p ∈ U → sig[p]? = some B → ObservableType B → Unravelling mu (future p) (ρ p)) :
    Unravelling mu t (Runtime.readbackWith ρ t) := by
  match hf with
  | .integer z => exact .integer z
  | .boolean b => cases b <;> first | exact .false | exact .true
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .nil => exact .nil
  | .future hp => simpa only [Runtime.readbackWith, future, Trm.weaken_self] using futures _ _ hp (typing_future_iff.mp ht) ho
  | .funE _ _ _ _ => cases ht; exact False.elim ho
  | .fixE _ _ _ _ => cases ht; exact False.elim ho
  | .sexp_int ha => cases ht with
    | sexp_int _ ht => exact .sexp_int (ha.readback_unravelling ht trivial futures)
  | .sexp_bool ha => cases ht with
    | sexp_bool _ ht => exact .sexp_bool (ha.readback_unravelling ht trivial futures)
  | .sexp_id ha => cases ht with
    | sexp_id _ ht => exact .sexp_id (ha.readback_unravelling ht trivial futures)
  | .pair ha hb => cases ht with
    | pair _ _ ht hu =>
      exact .pair (ha.readback_unravelling ht trivial futures) (hb.readback_unravelling hu trivial futures)
termination_by (sizeOf t, 1)
decreasing_by
  all_goals apply Prod.Lex.left
  all_goals simp [sexp_int, sexp_bool, sexp_id, pair, sizeOf, Trm._sizeOf_1]; omega

private theorem IsAtom.readback_unravelling {U t ρ sig mu A} (hf : IsAtom U (n := 0) t)
    (ht : HasType sig [] t A) (ho : ObservableType A)
    (futures : ∀ p B, p ∈ U → sig[p]? = some B → ObservableType B → Unravelling mu (future p) (ρ p)) :
    Unravelling mu t (Runtime.readbackWith ρ t) := by
  match hf with
  | .bound i => exact Fin.elim0 i
  | .free x => cases ht with | free hx => simp at hx
  | .value hv => exact hv.readback_unravelling ht ho futures
termination_by (sizeOf t, 2)
decreasing_by exact Prod.Lex.right _ (by decide)
end

private theorem HasValueEnumeration.unravelling_entries {mu sig ρ target} (h : HasValueEnumeration mu)
    (retain : ∀ (p : FName) w, mu[p]? = some w → target[p]? = some w)
    (eqs : ∀ p w, mu[p]? = some w → ρ p = readbackWith ρ w)
    (entries : ∀ (p : FName) w A, mu[p]? = some w → sig[p]? = some A → HasType sig [] w A) :
    ∀ p A, p ∈ domain mu → sig[p]? = some A → ObservableType A → Unravelling target (future p) (ρ p) := by
  induction h with
  | empty => simp
  | @snoc mu q w hc fresh hw closed ih =>
      have old_lookup {p : FName} {v : RawTerm 0} (hp : mu[p]? = some v) : (mu.insert q w)[p]? = some v := by
        have hqp : q ≠ p := fun e => fresh (e ▸ mem_domain_of_lookup hp)
        rw [lookup_insert_ne mu w hqp]; exact hp
      have old := ih (fun p v hp => retain p v (old_lookup hp))
        (fun p v hp => eqs p v (old_lookup hp)) (fun p v A hp => entries p v A (old_lookup hp))
      intro p A hp ht ho
      simp only [domain_insert, Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq] at hp
      rcases hp with rfl | hp
      · rw [eqs q w (by simp)]
        exact .future (retain q w (by simp)) (hw.readback_unravelling (entries q w A (by simp) ht) ho old)
      · exact old p A hp ht ho

/-- At the five observable types, read-back agrees with the existing value judgment. -/
theorem readback_unravels {mu sig w A} (h : HasValueEnumeration mu)
    (_domains : domain mu = domain sig)
    (entries : ∀ (p : FName) v B, mu[p]? = some v → sig[p]? = some B → HasType sig [] v B)
    (hw : IsValue (domain mu) w) (ht : HasType sig [] w A) (ho : ObservableType A) :
    Unravels mu w (readback h w (.atom (.value hw))) := by
  refine ⟨⟨domain mu, fun _ hp => hp, hw, fun _ _ hp => .atom (.value (h.entries hp).1)⟩,
    readback_value h hw, ?_⟩
  exact hw.readback_unravelling ht ho
    (h.unravelling_entries (fun _ _ hp => hp) h.expansion.lookup entries)

/-- Unravel-State applied to a final, ok state whose mapping has a value enumeration. -/
theorem State.observes_readback {s : State} (h : HasValueEnumeration s.mapping) (ok : s.Ok)
    (final : s.Final) {A} (ht : HasType s.signature [] s.focus A) (ho : ObservableType A) :
    s.Observes (readback h s.focus (ok.domains ▸ s.focus_formed)) := by
  exact ⟨ok, final, readback_unravels h ok.domains ok.entries (ok.domains ▸ final.focus) ht ho⟩

/-- Once the guard's future chain is exposed, the displayed source branch is selected. -/
theorem readback_if_step {mu sig guard yes no result} (hc : HasValueEnumeration mu)
    (domains : domain mu = domain sig) (hg : IsValue (domain mu) guard)
    (head : ∀ p, guard ≠ future p) (hy : IsTerm (domain mu) yes) (hn : IsTerm (domain mu) no)
    (step : Source.Step (readback hc (ifE guard yes no) (.ifE (.value hg) hy hn)) result) :
    ∃ t, ∃ ht : IsTerm (domain mu) t,
      LocalStep sig mu (ifE guard yes no) sig mu t ∧ readback hc t ht = result := by
  cases hg with
  | future hp => exact False.elim (head _ rfl)
  | boolean b =>
      cases b <;> cases step
      · exact ⟨no, hn, .if_false (domains ▸ hy) (domains ▸ hn), rfl⟩
      · exact ⟨yes, hy, .if_true (domains ▸ hy) (domains ▸ hn), rfl⟩
  | _ => cases step

/-- Both demanded operands are exposed; the same primitive rule and premise apply. -/
theorem readback_operation_step {mu sig op a b result} (hc : HasValueEnumeration mu)
    (_domains : domain mu = domain sig) (ha : IsValue (domain mu) a) (hb : IsValue (domain mu) b)
    (headA : ∀ p, a ≠ future p) (headB : ∀ p, b ≠ future p)
    (step : Source.Step (readback hc (operation op a b) (.operation op (.value ha) (.value hb))) result) :
    ∃ t, ∃ ht : IsTerm (domain mu) t,
      LocalStep sig mu (operation op a b) sig mu t ∧ readback hc t ht = result := by
  cases ha <;> cases hb
  all_goals try exact False.elim (headA _ rfl)
  all_goals try exact False.elim (headB _ rfl)
  all_goals cases step
  all_goals first
    | exact ⟨_, .atom (.value (.integer _)), .add _ _, rfl⟩
    | exact ⟨_, .atom (.value (.integer _)), .sub _ _, rfl⟩
    | exact ⟨_, .atom (.value (.integer _)), .mul _ _, rfl⟩
    | exact ⟨_, .atom (.value (.boolean _)), .eq_int_true (by assumption), rfl⟩
    | exact ⟨_, .atom (.value (.boolean _)), .eq_int_false (by assumption), rfl⟩
    | exact ⟨_, .atom (.value (.boolean _)), .eq_id_true (by assumption), rfl⟩
    | exact ⟨_, .atom (.value (.boolean _)), .eq_id_false (by assumption), rfl⟩
    | exact ⟨_, .atom (.value (.boolean _)), .lt_true (by assumption), rfl⟩
    | exact ⟨_, .atom (.value (.boolean _)), .lt_false (by assumption), rfl⟩

private theorem values_toArgs {U} {vs : List (RawTerm 0)} (hv : ∀ v ∈ vs, IsValue U v) :
    IsAtoms U (toArgs vs) := by
  induction vs with
  | nil => exact .nil
  | cons a rest ih => exact .cons (.value (hv a (by simp))) (ih (fun v h => hv v (by simp [h])))

private theorem instantiate_formed {U} (vs : List (RawTerm 0)) {body : RawTerm vs.length}
    (hb : IsTerm U body) (hv : ∀ v ∈ vs, IsValue U v) : IsTerm U (instantiate vs body) := by
  induction vs with
  | nil => exact hb
  | cons a rest ih =>
      exact ih (hb.open _ (.value (hv a (by simp))) rfl) (fun v h => hv v (by simp [h]))

private theorem readbackWith_castScope (ρ : FName → Source.RawTerm 0) {m n}
    (t : RawTerm m) (e : m = n) :
    readbackWith ρ (t.castScope e) = (readbackWith ρ t).castScope e := by cases e; rfl

private theorem readbackWith_conc (ρ : FName → Source.RawTerm 0) {n}
    (body : RawTerm (n + 1)) (a : RawTerm 0) :
    readbackWith ρ (body.conc a) = (readbackWith ρ body).conc (readbackWith ρ a) :=
  readbackWith_open ρ body _ a rfl

private theorem readbackWith_instantiate (ρ : FName → Source.RawTerm 0)
    (args : List (RawTerm 0)) (body : RawTerm args.length) :
    readbackWith ρ (instantiate args body) = Source.instantiate (args.map (readbackWith ρ))
      ((readbackWith ρ body).castScope (by simp)) := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
      simp only [instantiate, List.map_cons, Source.instantiate]
      rw [ih, readbackWith_conc]
      have cast_conc {m n} (e : m = n) (b : Source.RawTerm (m + 1)) (v : Source.RawTerm 0) :
          (b.castScope (congrArg (· + 1) e)).conc v = (b.conc v).castScope e := by cases e; rfl
      rw [cast_conc]

private theorem readbackWith_app (ρ : FName → Source.RawTerm 0) (fn first : RawTerm 0)
    (rest : List (RawTerm 0)) :
    readbackWith ρ (app fn first (toArgs rest)) =
      Source.app (readbackWith ρ fn) (readbackWith ρ first) (Source.toArgs (rest.map (readbackWith ρ))) := by
  have cons_heq {ms ns} (e : ms = ns) (t : Source.RawTerm 0)
      (as : Arg Source.signature 0 ms) (bs : Arg Source.signature 0 ns) (h : HEq as bs) :
      HEq (Arg.cons (m := 0) t as) (Arg.cons (m := 0) t bs) := by cases e; cases h; rfl
  have args : HEq (readbackArgsWith ρ (toArgs rest)) (Source.toArgs (rest.map (readbackWith ρ))) := by
    induction rest with
    | nil => rfl
    | cons a rest ih => exact cons_heq (by simp) (readbackWith ρ a) _ _ ih
  have h := cons_heq (by simp) (readbackWith ρ fn) _ _
    (cons_heq (by simp) (readbackWith ρ first) _ _ args)
  have op_eq {o o' : Source.Op} (e : o = o') (as : Arg Source.signature 0 (Source.signature.ar o))
      (bs : Arg Source.signature 0 (Source.signature.ar o')) (he : HEq as bs) :
      Trm.op (Sg := Source.signature) o as = Trm.op o' bs := by cases e; cases he; rfl
  exact op_eq (by simp) _ _ h

/-- A non-future function head takes the matching beta rule with the original arguments. -/
theorem readback_app_step {mu sig fn first result} (hc : HasValueEnumeration mu)
    (domains : domain mu = domain sig) (hf : IsValue (domain mu) fn)
    (head : ∀ p, fn ≠ future p) (ha : IsValue (domain mu) first)
    (rest : List (RawTerm 0)) (hvs : ∀ v ∈ rest, IsValue (domain mu) v)
    (step : Source.Step (readback hc (app fn first (toArgs rest))
      (.app (.value hf) (.value ha) (values_toArgs hvs))) result) :
    ∃ t, ∃ ht : IsTerm (domain mu) t,
      LocalStep sig mu (app fn first (toArgs rest)) sig mu t ∧ readback hc t ht = result := by
  change Source.Step (readbackWith hc.expansion.entry (app fn first (toArgs rest))) result at step
  rw [readbackWith_app] at step
  generalize he : Source.app (readbackWith hc.expansion.entry fn) (readbackWith hc.expansion.entry first)
    (Source.toArgs (rest.map (readbackWith hc.expansion.entry))) = start at step
  cases step with
  | beta arity body arg args =>
      obtain ⟨ef, ea, es⟩ := Source.app_inj he
      cases ea
      cases es
      cases hf with
      | future hp => exact False.elim (head _ rfl)
      | funE A As B hb =>
          cases ef
          have arity' := arity
          simp only [List.length_map] at arity'
          have cast_formed {m n} {t : RawTerm m} (e : m = n) (h : IsTerm (domain mu) t) :
              IsTerm (domain mu) (t.castScope e) := by cases e; exact h
          refine ⟨_, instantiate_formed (first :: rest) (cast_formed _ hb)
            (by intro a h; rcases List.mem_cons.mp h with rfl | h; exact ha; exact hvs a h),
            .beta arity' (domains ▸ hb) (domains ▸ ha) (fun a h => domains ▸ hvs a h), ?_⟩
          change readbackWith hc.expansion.entry _ = _
          simp only [readbackWith_instantiate, readbackWith_castScope, List.map_cons,
            Source.castScope_trans]
      | _ => cases ef
  | fix_beta arity body arg args =>
      obtain ⟨ef, ea, es⟩ := Source.app_inj he
      cases ea
      cases es
      cases hf with
      | future hp => exact False.elim (head _ rfl)
      | fixE A As B hb =>
          cases ef
          have arity' := arity
          simp only [List.length_map] at arity'
          have cast_formed {m n} {t : RawTerm m} (e : m = n) (h : IsTerm (domain mu) t) :
              IsTerm (domain mu) (t.castScope e) := by cases e; exact h
          refine ⟨_, instantiate_formed (_ :: first :: rest) (cast_formed _ hb)
            (by intro a h; rcases List.mem_cons.mp h with rfl | h; exact .fixE _ _ _ hb
                rcases List.mem_cons.mp h with rfl | h; exact ha; exact hvs a h),
            .fix_beta arity' (domains ▸ hb) (domains ▸ ha) (fun a h => domains ▸ hvs a h), ?_⟩
          change readbackWith hc.expansion.entry _ = _
          simp only [readbackWith_instantiate, readbackWith_castScope, List.map_cons,
            Source.castScope_trans]
          rfl
      | _ => cases ef
  | _ => cases he

private theorem readback_member {U ρ ps ms b} {bs : Arg signature 0 ms}
    (hs : IsBranches U ps bs) (h : Source.BranchMember b (readbackArgsWith ρ bs)) :
    ∃ p t, ArgMember t bs ∧ IsBranch U p t ∧ readbackWith ρ t = b := by
  induction ps generalizing ms b with
  | nil => cases hs; cases h
  | cons p ps ih =>
      cases hs with
      | cons hb rest =>
          cases h with
          | here => exact ⟨_, _, .here, hb, rfl⟩
          | there h =>
              obtain ⟨p, t, hm, ht, e⟩ := ih rest h
              exact ⟨p, t, .there hm, ht, e⟩

private theorem source_patterns_unique {n ps qs ms} {bs : Arg Source.signature n ms}
    (hp : Source.IsBranches ps bs) (hq : Source.IsBranches qs bs) : ps = qs := by
  match hp, hq with
  | .nil, .nil => rfl
  | .cons hb hs, .cons hb' hs' =>
      have e := source_patterns_unique hs hs'
      cases hb
      cases hb'
      exact congrArg (_ :: ·) e
termination_by structural hp

private theorem readback_matchBranch {U ρ v b result p}
    (hv : IsValue U v) (head : ∀ q, v ≠ future q) (hb : IsBranch U p b)
    (h : Source.MatchBranch (readbackWith ρ v) (readbackWith ρ b) result) :
    ∃ t, IsTerm U t ∧ MatchBranch U v b t ∧ readbackWith ρ t = result := by
  cases hb with | branch ht =>
    cases hv
    all_goals try exact False.elim (head _ rfl)
    all_goals cases h
    all_goals first
      | exact ⟨_, ht.conc (by assumption), .int (by assumption), readbackWith_conc _ _ _⟩
      | exact ⟨_, ht.conc (by assumption), .bool (by assumption), readbackWith_conc _ _ _⟩
      | exact ⟨_, ht.conc (by assumption), .id (by assumption), readbackWith_conc _ _ _⟩
      | exact ⟨_, ht, .nil, rfl⟩
      | exact ⟨_, (ht.open ⟨0, by decide⟩ (by assumption) rfl).conc (by assumption), .pair (by assumption) (by assumption),
          by rw [readbackWith_conc, readbackWith_open]; rfl⟩

/-- Read-back preserves branch selection and the constructor or wildcard side conditions. -/
theorem readback_match_step {mu sig k ps a result} {bs : RawArgs 0 k}
    (hc : HasValueEnumeration mu) (domains : domain mu = domain sig)
    (ha : IsValue (domain mu) a) (head : ∀ p, a ≠ future p)
    (hb : IsBranches (domain mu) ps bs) (hp : Source.MatchPatterns ps)
    (step : Source.Step (readback hc (matchE a bs) (.matchE (.value ha) hb hp)) result) :
    ∃ t, ∃ ht : IsTerm (domain mu) t,
      LocalStep sig mu (matchE a bs) sig mu t ∧ readback hc t ht = result := by
  change Source.Step (Source.matchE (readbackWith hc.expansion.entry a)
    (readbackArgsWith hc.expansion.entry bs)) result at step
  cases step with
  | match_constructor hs patterns member matched =>
      obtain ⟨p, b, member', formed, e⟩ := readback_member hb member
      rw [← e] at matched
      obtain ⟨t, ht, matched', equation⟩ := readback_matchBranch ha head formed matched
      refine ⟨t, ht, .match_constructor (domains ▸ hb) hp member' ?_, equation⟩
      exact domains ▸ matched'
  | match_wildcard hv constructor absent hs patterns member =>
      have ep := source_patterns_unique (hb.readbackWith hc.expansion.value) hs
      obtain ⟨p, b, member', formed, e⟩ := readback_member hb member
      cases formed with | branch ht =>
        cases e
        have same_head : constructorHead a = Source.constructorHead (readbackWith hc.expansion.entry a) := by
          cases ha <;> try rfl
          exact False.elim (head _ rfl)
        refine ⟨_, ht, .match_wildcard (domains ▸ ha) (same_head.trans constructor)
          (ep ▸ absent) (domains ▸ hb) hp member', rfl⟩

private theorem ArgMember.readbackWith {a ms bs ρ} (h : ArgMember a (ms := ms) bs) :
    Source.BranchMember (readbackWith ρ a) (readbackArgsWith ρ bs) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

private theorem MatchBranch.readbackWith {U v b result ρ} (h : MatchBranch U v b result)
    (values : ∀ p, p ∈ U → Source.IsValue (ρ p)) :
    Source.MatchBranch (readbackWith ρ v) (readbackWith ρ b) (readbackWith ρ result) := by
  cases h with
  | int ha => rw [readbackWith_conc]; exact .int (ha.readbackWith values)
  | bool ha => rw [readbackWith_conc]; exact .bool (ha.readbackWith values)
  | id ha => rw [readbackWith_conc]; exact .id (ha.readbackWith values)
  | nil => exact .nil
  | pair ha hb =>
      rw [readbackWith_conc, readbackWith_conc]
      exact .pair (ha.readbackWith values) (hb.readbackWith values)

-- The two hypotheses are precisely the fixed-final-mapping conditions in
-- C-Obs-to-Seq: retained value entries and evaluation of newly allocated entries.
private theorem LocalStep.readback_raw {sig mu t sig' mu' t'}
    (h : LocalStep sig mu t sig' mu' t') (ρ : FName → Source.RawTerm 0)
    (values : ∀ p, p ∈ domain sig → Source.IsValue (ρ p))
    (domains : ∀ p, p ∈ domain mu → p ∈ domain sig)
    (retain : ∀ p w, mu[p]? = some w → IsValue (domain sig) w →
      ρ p = readbackWith ρ w)
    (allocated : ∀ q w, q ∉ domain mu → mu'[q]? = some w →
      Source.Steps (readbackWith ρ w) (ρ q))
    (ht : IsTerm (domain sig) t) :
    Source.Steps (readbackWith ρ t) (readbackWith ρ t') := by
  have one {a b} (step : Source.Step a b) : Source.Steps a b := .step step (.refl step.formed.2)
  induction h with
  | search_let _ rule hb ih =>
      cases ht with
      | atom ha => cases ha with | value hv => cases hv
      | letE hr _ => exact (ih allocated hr).search_let (hb.readbackWith values)
  | beta arity hb hv hvs =>
      rw [readbackWith_app, readbackWith_instantiate]
      simp only [List.map_cons, readbackWith_castScope, Source.castScope_trans]
      exact one (.beta (by simpa using arity) (hb.readbackWith values) (hv.readbackWith values) (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact (hvs b hb).readbackWith values))
  | fix_beta arity hb hv hvs =>
      rw [readbackWith_app, readbackWith_instantiate]
      simp only [List.map_cons, readbackWith_castScope, Source.castScope_trans]
      exact one (.fix_beta (by simpa using arity) (hb.readbackWith values) (hv.readbackWith values) (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact (hvs b hb).readbackWith values))
  | let_value hv hb =>
      rw [readbackWith_conc]
      exact one (.let_value (hv.readbackWith values) (hb.readbackWith values))
  | match_constructor hs hp hm hb =>
      exact one (.match_constructor (hs.readbackWith values) hp hm.readbackWith (hb.readbackWith values))
  | @match_wildcard k ps p scrutinee body bs hv head absent hs hp hm =>
      have head' : Source.constructorHead (readbackWith ρ scrutinee) = some p := by
        cases hv <;> first | exact head | cases head
      exact one (.match_wildcard (hv.readbackWith values) head' absent (hs.readbackWith values) hp hm.readbackWith)
  | add m n => exact one (.add m n)
  | sub m n => exact one (.sub m n)
  | mul m n => exact one (.mul m n)
  | eq_int_true he => exact one (.eq_int_true he)
  | eq_int_false he => exact one (.eq_int_false he)
  | eq_id_true he => exact one (.eq_id_true he)
  | eq_id_false he => exact one (.eq_id_false he)
  | lt_true he => exact one (.lt_true he)
  | lt_false he => exact one (.lt_false he)
  | if_true hy hn => exact one (.if_true (hy.readbackWith values) (hn.readbackWith values))
  | if_false hy hn => exact one (.if_false (hy.readbackWith values) (hn.readbackWith values))
  | spawn_async hb fresh =>
      simpa only [readbackWith, future, Trm.weaken_self] using
        Source.Steps.step (.src_async (hb.formed.readbackWith values))
          (allocated _ _ (fun hq => fresh (domains _ hq)) (by simp))
  | spawn_app _ ha fresh hb =>
      simpa only [readbackWith, readbackArgsWith, letE, future, Source.letE, Trm.weaken_self] using
        (allocated _ _ (fun hq => fresh (domains _ hq)) (by simp)).search_let (hb.readbackWith values)
  | deref_app hp hw | deref_op_left hp hw | deref_op_right hp hw | deref_if hp hw | deref_match hp hw =>
      have eqn := retain _ _ hp hw
      have hf := ht.readbackWith values
      simp only [app, operation, ifE, matchE, future, readbackWith, readbackArgsWith,
        Trm.weaken_self, eqn] at hf ⊢
      exact .refl hf

/-- Fixed-final-mapping local correspondence (all 24 runtime rule schemas).
    The allocated-entry premise is later supplied by backward induction. -/
theorem State.LocalStep.readback_steps {s t : State} (step : s.LocalStep t)
    {mu} (h : HasValueEnumeration mu)
    (ds : ∀ p, p ∈ domain s.signature → p ∈ domain mu)
    (dt : ∀ p, p ∈ domain t.signature → p ∈ domain mu)
    (retain : ∀ (p : FName) (w : RawTerm 0), s.mapping[p]? = some w → IsValue (domain s.signature) w → mu[p]? = some w)
    (allocated : ∀ (q : FName) (w : RawTerm 0), q ∉ domain s.mapping → (hp : t.mapping[q]? = some w) →
      Source.Steps (readback h w ((t.entries_formed q w hp).mono dt))
        (readback h (future q) (.atom (.value (.future (dt q (t.domains q (mem_domain_of_lookup hp)))))))) :
    Source.Steps (readback h s.focus (s.focus_formed.mono ds))
      (readback h t.focus (t.focus_formed.mono dt)) := by
  apply step.readback_raw h.expansion.entry (fun p hp => h.expansion.value p (ds p hp)) s.domains
  · intro p w hp hw
    exact h.expansion.lookup p w (retain p w hp hw)
  · intro q w fresh hp
    simpa only [Runtime.readback, readbackWith, future, Trm.weaken_self] using allocated q w fresh hp
  · exact s.focus_formed

end SourceRuntime.Runtime

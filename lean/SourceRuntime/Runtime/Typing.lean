import SourceRuntime.Runtime.State
import SourceRuntime.Runtime.Binding
import SourceRuntime.Source.Typing

/-!
Runtime §4: all term and branch rules, with Σ fixed throughout each derivation.
The parameter sig is the paper signature Σ. Γ and Δ use the source context conventions; all subjects are runtime trees.
T-Future reads only Σ. State-Ok (§5) separately relates Σ to μ.
-/

namespace SourceRuntime.Runtime

open WSLN
open Source (Ty Id Pattern MatchPatterns Context push pushMany)

mutual
/-- The IsAtom premises enforce the atom positions declared by the runtime grammar. -/
inductive Typing (sig : Signature) (Γ : Context) : {n : Nat} → (Fin n → Ty) → RawTerm n → Ty → Prop where
  | bound {n Δ} (i : Fin n) : Typing sig Γ Δ (.var i) (Δ i)
  | free {n Δ x A} : Γ.lookup x = some A → Typing sig Γ (n := n) Δ (var x) A
  | future {n Δ A} {p : FName} : sig[p]? = some A → Typing sig Γ (n := n) Δ (future p) A
  | integer {n Δ} (z : Int) : Typing sig Γ (n := n) Δ (integer z) .int
  | boolean {n Δ} (b : Bool) : Typing sig Γ (n := n) Δ (boolean b) .bool
  | unit {n Δ} : Typing sig Γ (n := n) Δ unit .unit
  | identifier {n Δ} (i : Id) : Typing sig Γ (n := n) Δ (identifier i) .id
  | funE {n Δ first rest result} {body : RawTerm (n + (rest.length + 1))} :
      Typing sig Γ (pushMany (first :: rest) Δ) body result →
      Typing sig Γ Δ (funE first rest result body) (.arrow first rest result)
  | fixE {n Δ first rest result} {body : RawTerm (n + (rest.length + 2))} :
      Typing sig Γ (pushMany (.arrow first rest result :: first :: rest) Δ) body result →
      Typing sig Γ Δ (fixE first rest result body) (.arrow first rest result)
  | sexp_int {n Δ} {a : RawTerm n} :
      IsAtom (domain sig) a → Typing sig Γ Δ a .int → Typing sig Γ Δ (sexp_int a) .sexp
  | sexp_bool {n Δ} {a : RawTerm n} :
      IsAtom (domain sig) a → Typing sig Γ Δ a .bool → Typing sig Γ Δ (sexp_bool a) .sexp
  | sexp_id {n Δ} {a : RawTerm n} :
      IsAtom (domain sig) a → Typing sig Γ Δ a .id → Typing sig Γ Δ (sexp_id a) .sexp
  | nil {n Δ} : Typing sig Γ (n := n) Δ nil .sexp
  | pair {n Δ} {a b : RawTerm n} :
      IsAtom (domain sig) a → IsAtom (domain sig) b → Typing sig Γ Δ a .sexp → Typing sig Γ Δ b .sexp →
      Typing sig Γ Δ (pair a b) .sexp
  | app {n k Δ A As B} {fn first : RawTerm n} {rest : RawArgs n k} :
      IsAtom (domain sig) fn → IsAtom (domain sig) first → Typing sig Γ Δ fn (.arrow A As B) →
      Typing sig Γ Δ first A → ArgsTyping sig Γ Δ As rest → Typing sig Γ Δ (app fn first rest) B
  | arith {n Δ op} {a b : RawTerm n} :
      (op = .add ∨ op = .sub ∨ op = .mul) → IsAtom (domain sig) a → IsAtom (domain sig) b →
      Typing sig Γ Δ a .int → Typing sig Γ Δ b .int → Typing sig Γ Δ (operation op a b) .int
  | eq {n Δ A} {a b : RawTerm n} :
      (A = .int ∨ A = .id) → IsAtom (domain sig) a → IsAtom (domain sig) b →
      Typing sig Γ Δ a A → Typing sig Γ Δ b A → Typing sig Γ Δ (operation .eq a b) .bool
  | lt {n Δ} {a b : RawTerm n} :
      IsAtom (domain sig) a → IsAtom (domain sig) b → Typing sig Γ Δ a .int → Typing sig Γ Δ b .int →
      Typing sig Γ Δ (operation .lt a b) .bool
  | ifE {n Δ A} {guard yes no : RawTerm n} :
      IsAtom (domain sig) guard → Typing sig Γ Δ guard .bool → Typing sig Γ Δ yes A → Typing sig Γ Δ no A →
      Typing sig Γ Δ (ifE guard yes no) A
  | letE {n Δ A B} {rhs : RawTerm n} {body : RawTerm (n + 1)} :
      Typing sig Γ Δ rhs A → Typing sig Γ (push A Δ) body B → Typing sig Γ Δ (letE rhs body) B
  | matchE {n k Δ ps A} {a : RawTerm n} {bs : RawArgs n k} :
      IsAtom (domain sig) a → Typing sig Γ Δ a .sexp → BranchesTyping sig Γ Δ ps bs A →
      MatchPatterns ps → Typing sig Γ Δ (matchE a bs) A
  | async {n Δ A} {body : RawTerm n} : Typing sig Γ Δ body A → Typing sig Γ Δ (async body) A

inductive BranchTyping (sig : Signature) (Γ : Context) : {n : Nat} → (Fin n → Ty) → Pattern → RawTerm n → Ty → Prop where
  | int {n Δ A} {body : RawTerm (n + 1)} :
      Typing sig Γ (push .int Δ) body A → BranchTyping sig Γ Δ .int (branch .int body) A
  | bool {n Δ A} {body : RawTerm (n + 1)} :
      Typing sig Γ (push .bool Δ) body A → BranchTyping sig Γ Δ .bool (branch .bool body) A
  | id {n Δ A} {body : RawTerm (n + 1)} :
      Typing sig Γ (push .id Δ) body A → BranchTyping sig Γ Δ .id (branch .id body) A
  | nil {n Δ A} {body : RawTerm n} :
      Typing sig Γ Δ body A → BranchTyping sig Γ Δ .nil (branch .nil body) A
  | pair {n Δ A} {body : RawTerm (n + 2)} :
      Typing sig Γ (push .sexp (push .sexp Δ)) body A → BranchTyping sig Γ Δ .pair (branch .pair body) A
  | wildcard {n Δ A} {body : RawTerm n} :
      Typing sig Γ Δ body A → BranchTyping sig Γ Δ .wildcard (branch .wildcard body) A

/-- Pointwise argument typing, with the same ordered type sequence as T-App. -/
inductive ArgsTyping (sig : Signature) (Γ : Context) : {n : Nat} → (Fin n → Ty) → List Ty →
    {ms : List Nat} → Arg signature n ms → Prop where
  | nil {n Δ} : ArgsTyping sig Γ (n := n) Δ [] .nil
  | cons {n Δ A As ms} {a : RawTerm n} {rest : Arg signature n ms} :
      IsAtom (domain sig) a → Typing sig Γ Δ a A → ArgsTyping sig Γ Δ As rest →
      ArgsTyping sig Γ Δ (A :: As) (.cons (m := 0) a rest)

/-- All branches have the one result type required by T-Match. -/
inductive BranchesTyping (sig : Signature) (Γ : Context) : {n : Nat} → (Fin n → Ty) → List Pattern →
    {ms : List Nat} → Arg signature n ms → Ty → Prop where
  | nil {n Δ A} : BranchesTyping sig Γ (n := n) Δ [] .nil A
  | cons {n Δ p ps ms A} {b : RawTerm n} {rest : Arg signature n ms} :
      BranchTyping sig Γ Δ p b A → BranchesTyping sig Γ Δ ps rest A →
      BranchesTyping sig Γ Δ (p :: ps) (.cons (m := 0) b rest) A
end

abbrev HasType (sig : Signature) (Γ : Context) (t : RawTerm 0) (A : Ty) := Typing sig Γ Fin.elim0 t A
abbrev HasBranchType (sig : Signature) (Γ : Context) (p : Pattern) (b : RawTerm 0) (A : Ty) :=
  BranchTyping sig Γ Fin.elim0 p b A

mutual
theorem Typing.formed {sig Γ n Δ t A} (h : Typing sig Γ (n := n) Δ t A) : IsTerm (domain sig) t := by
  match h with
  | .bound i => exact .atom (.bound i)
  | .free _ => exact .atom (.free _)
  | .future hp => exact .atom (.value (.future (mem_domain_of_lookup hp)))
  | .integer z => exact .atom (.value (.integer z))
  | .boolean b => exact .atom (.value (.boolean b))
  | .unit => exact .atom (.value .unit)
  | .identifier i => exact .atom (.value (.identifier i))
  | .funE hb => exact .atom (.value (.funE _ _ _ hb.formed))
  | .fixE hb => exact .atom (.value (.fixE _ _ _ hb.formed))
  | .sexp_int ha _ => exact .atom (.value (.sexp_int ha))
  | .sexp_bool ha _ => exact .atom (.value (.sexp_bool ha))
  | .sexp_id ha _ => exact .atom (.value (.sexp_id ha))
  | .nil => exact .atom (.value .nil)
  | .pair ha hb _ _ => exact .atom (.value (.pair ha hb))
  | .app hf ha _ _ hs => exact .app hf ha hs.formed
  | .arith _ ha hb _ _ => exact .operation _ ha hb
  | .eq _ ha hb _ _ => exact .operation _ ha hb
  | .lt ha hb _ _ => exact .operation _ ha hb
  | .ifE hg _ hy hn => exact .ifE hg hy.formed hn.formed
  | .letE hr hb => exact .letE hr.formed hb.formed
  | .matchE ha _ hs hf => exact .matchE ha hs.formed hf
  | .async hb => exact .async hb.formed
termination_by structural h

theorem BranchTyping.formed {sig Γ n Δ p b A} (h : BranchTyping sig Γ (n := n) Δ p b A) :
    IsBranch (domain sig) p b := by
  match h with
  | .int hb => exact .branch hb.formed
  | .bool hb => exact .branch hb.formed
  | .id hb => exact .branch hb.formed
  | .nil hb => exact .branch hb.formed
  | .pair hb => exact .branch hb.formed
  | .wildcard hb => exact .branch hb.formed
termination_by structural h

theorem ArgsTyping.formed {sig Γ n Δ As ms args} (h : ArgsTyping sig Γ (n := n) Δ As (ms := ms) args) :
    IsAtoms (domain sig) args := by
  match h with
  | .nil => exact .nil
  | .cons ha _ hs => exact .cons ha hs.formed
termination_by structural h

theorem BranchesTyping.formed {sig Γ n Δ ps ms bs A}
    (h : BranchesTyping sig Γ (n := n) Δ ps (ms := ms) bs A) : IsBranches (domain sig) ps bs := by
  match h with
  | .nil => exact .nil
  | .cons hb hs => exact .cons hb.formed hs.formed
termination_by structural h
end

/-- T-Future is the only typing rule with a future name as its subject. -/
theorem typing_future_iff {sig Γ n Δ p A} :
    Typing sig Γ (n := n) Δ (future p) A ↔ sig[p]? = some A := by
  constructor
  · intro h; cases h with | future hp => exact hp
  · exact Typing.future

/-- State-Ok: equal domains, a typed focus, and consistent types for all entries.
    Domain equality ensures both lookups in the last premise are defined. -/
structure State.Ok (s : State) : Prop where
  domains : domain s.mapping = domain s.signature
  focus : ∃ A, HasType s.signature [] s.focus A
  entries : ∀ (p : FName) body A, s.mapping[p]? = some body → s.signature[p]? = some A →
    HasType s.signature [] body A

-- Only scope transport, substitution and opening are needed by reduction.
-- Context transport is shared with source; the subjects here are runtime trees.
open Source (pushMany_weaken pushMany_open)

@[simp] private theorem shift_zero {n} (i : Fin n) : shiftIdx 0 i = i := by
  apply Fin.ext; simp [shiftIdx]

-- Scope weakening preserves the types of all previously available indices.
mutual
theorem Typing.weaken {sig Γ m Δ t A} (ht : Typing sig Γ (n := m) Δ t A)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : Typing sig Γ Δ' (t.weaken n h) A := by
  match ht with
  | .bound i => rw [← hΔ i]; exact .bound _
  | .free hx => exact .free hx
  | .future hp => exact .future hp
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE hb => exact .funE (hb.weaken _ (pushMany_weaken _ h hΔ))
  | .fixE hb => exact .fixE (hb.weaken _ (pushMany_weaken _ h hΔ))
  | .sexp_int ha ht => exact .sexp_int (ha.weaken h) (ht.weaken h hΔ)
  | .sexp_bool ha ht => exact .sexp_bool (ha.weaken h) (ht.weaken h hΔ)
  | .sexp_id ha ht => exact .sexp_id (ha.weaken h) (ht.weaken h hΔ)
  | .nil => exact .nil
  | .pair ha hb hta htb => exact .pair (ha.weaken h) (hb.weaken h) (hta.weaken h hΔ) (htb.weaken h hΔ)
  | .app hf ha htf hta hs =>
      exact .app (hf.weaken h) (ha.weaken h) (htf.weaken h hΔ) (hta.weaken h hΔ) (hs.weaken h hΔ)
  | .arith hop ha hb hta htb =>
      exact .arith hop (ha.weaken h) (hb.weaken h) (hta.weaken h hΔ) (htb.weaken h hΔ)
  | .eq hA ha hb hta htb => exact .eq hA (ha.weaken h) (hb.weaken h) (hta.weaken h hΔ) (htb.weaken h hΔ)
  | .lt ha hb hta htb => exact .lt (ha.weaken h) (hb.weaken h) (hta.weaken h hΔ) (htb.weaken h hΔ)
  | .ifE hg ht hy hn => exact .ifE (hg.weaken h) (ht.weaken h hΔ) (hy.weaken h hΔ) (hn.weaken h hΔ)
  | .letE (A := C) hr hb => exact .letE (hr.weaken h hΔ) (hb.weaken _ (pushMany_weaken [C] h hΔ))
  | .matchE ha ht hs hf => exact .matchE (ha.weaken h) (ht.weaken h hΔ) (hs.weaken h hΔ) hf
  | .async hb => exact .async (hb.weaken h hΔ)
termination_by structural ht

theorem BranchTyping.weaken {sig Γ m Δ p b A} (ht : BranchTyping sig Γ (n := m) Δ p b A)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : BranchTyping sig Γ Δ' p (b.weaken n h) A := by
  match ht with
  | .int hb => exact .int (hb.weaken _ (pushMany_weaken [.int] h hΔ))
  | .bool hb => exact .bool (hb.weaken _ (pushMany_weaken [.bool] h hΔ))
  | .id hb => exact .id (hb.weaken _ (pushMany_weaken [.id] h hΔ))
  | .nil hb => exact .nil (hb.weaken h hΔ)
  | .pair hb => exact .pair (hb.weaken _ (pushMany_weaken [.sexp, .sexp] h hΔ))
  | .wildcard hb => exact .wildcard (hb.weaken h hΔ)
termination_by structural ht

theorem ArgsTyping.weaken {sig Γ m Δ As ms args} (ht : ArgsTyping sig Γ (n := m) Δ As (ms := ms) args)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : ArgsTyping sig Γ Δ' As (args.weaken n h) := by
  match ht with
  | .nil => exact .nil
  | .cons ha ht hs => exact .cons (ha.weaken h) (ht.weaken h hΔ) (hs.weaken h hΔ)
termination_by structural ht

theorem BranchesTyping.weaken {sig Γ m Δ ps ms bs A}
    (ht : BranchesTyping sig Γ (n := m) Δ ps (ms := ms) bs A)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : BranchesTyping sig Γ Δ' ps (bs.weaken n h) A := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.weaken h hΔ) (hs.weaken h hΔ)
termination_by structural ht
end

mutual
/-- Simultaneous atom substitution, respecting the types assigned by Γ. -/
theorem Typing.subst {sig Γ n Δ t A} (ht : Typing sig Γ (n := n) Δ t A)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (domain sig) (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType sig Γ' (σ x) B) : Typing sig Γ' Δ (σ * t) A := by
  match ht with
  | .bound i => exact .bound i
  | .free hx => exact (hσ _ _ hx).weaken (Nat.zero_le n) (fun i => Fin.elim0 i)
  | .future hp => exact .future hp
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE hb => exact .funE (hb.subst ha hσ)
  | .fixE hb => exact .fixE (hb.subst ha hσ)
  | .sexp_int hp ht => exact .sexp_int (hp.subst ha) (ht.subst ha hσ)
  | .sexp_bool hp ht => exact .sexp_bool (hp.subst ha) (ht.subst ha hσ)
  | .sexp_id hp ht => exact .sexp_id (hp.subst ha) (ht.subst ha hσ)
  | .nil => exact .nil
  | .pair hp hq hp' hq' => exact .pair (hp.subst ha) (hq.subst ha) (hp'.subst ha hσ) (hq'.subst ha hσ)
  | .app hf hp htf htp hs =>
      exact .app (hf.subst ha) (hp.subst ha) (htf.subst ha hσ) (htp.subst ha hσ) (hs.subst ha hσ)
  | .arith hop hp hq hp' hq' =>
      exact .arith hop (hp.subst ha) (hq.subst ha) (hp'.subst ha hσ) (hq'.subst ha hσ)
  | .eq hA hp hq hp' hq' => exact .eq hA (hp.subst ha) (hq.subst ha) (hp'.subst ha hσ) (hq'.subst ha hσ)
  | .lt hp hq hp' hq' => exact .lt (hp.subst ha) (hq.subst ha) (hp'.subst ha hσ) (hq'.subst ha hσ)
  | .ifE hg ht hy hn => exact .ifE (hg.subst ha) (ht.subst ha hσ) (hy.subst ha hσ) (hn.subst ha hσ)
  | .letE hr hb => exact .letE (hr.subst ha hσ) (hb.subst ha hσ)
  | .matchE hp ht hs hf => exact .matchE (hp.subst ha) (ht.subst ha hσ) (hs.subst ha hσ) hf
  | .async hb => exact .async (hb.subst ha hσ)
termination_by structural ht

theorem BranchTyping.subst {sig Γ n Δ p b A} (ht : BranchTyping sig Γ (n := n) Δ p b A)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (domain sig) (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType sig Γ' (σ x) B) : BranchTyping sig Γ' Δ p (σ * b) A := by
  match ht with
  | .int hb => exact .int (hb.subst ha hσ)
  | .bool hb => exact .bool (hb.subst ha hσ)
  | .id hb => exact .id (hb.subst ha hσ)
  | .nil hb => exact .nil (hb.subst ha hσ)
  | .pair hb => exact .pair (hb.subst ha hσ)
  | .wildcard hb => exact .wildcard (hb.subst ha hσ)
termination_by structural ht

theorem ArgsTyping.subst {sig Γ n Δ As ms args} (ht : ArgsTyping sig Γ (n := n) Δ As (ms := ms) args)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (domain sig) (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType sig Γ' (σ x) B) : ArgsTyping sig Γ' Δ As (σ * args) := by
  match ht with
  | .nil => exact .nil
  | .cons hp ht hs => exact .cons (hp.subst ha) (ht.subst ha hσ) (hs.subst ha hσ)
termination_by structural ht

theorem BranchesTyping.subst {sig Γ n Δ ps ms bs A} (ht : BranchesTyping sig Γ (n := n) Δ ps (ms := ms) bs A)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (domain sig) (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType sig Γ' (σ x) B) : BranchesTyping sig Γ' Δ ps (σ * bs) A := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.subst ha hσ) (hs.subst ha hσ)
termination_by structural ht
end

mutual
/-- Replace a bound slot by a well-typed atom, preserving the other slot types. -/
theorem Typing.open {sig Γ m Δ t B} (ht : Typing sig Γ (n := m) Δ t B)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    Typing sig Γ Δ' (opn i a t e) B := by
  match ht with
  | .bound j =>
      by_cases h : i = j
      · subst j
        rw [opn_var_eq]
        exact hta.weaken (Nat.zero_le n) (fun k => Fin.elim0 k)
      · rw [opn_var_ne a e h, ← hΔ j h]
        exact .bound _
  | .free hx => exact .free hx
  | .future hp => exact .future hp
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier j => exact .identifier j
  | .funE (first := first) (rest := rest) (result := result) hb =>
      have ho := pushMany_open (first :: rest) i e hΔ
      simpa only [Runtime.funE, opn_op, opnArg] using
        Typing.funE (hb.open (shiftIdx _ i) (by omega) ha (by simpa only [ho.1] using hta) ho.2)
  | .fixE (first := first) (rest := rest) (result := result) hb =>
      have ho := pushMany_open (.arrow first rest result :: first :: rest) i e hΔ
      simpa only [Runtime.fixE, opn_op, opnArg] using
        Typing.fixE (hb.open (shiftIdx _ i) (by omega) ha (by simpa only [ho.1] using hta) ho.2)
  | .sexp_int hp ht =>
      simpa only [Runtime.sexp_int, opn_op, opnArg, shift_zero] using
        Typing.sexp_int (hp.open i ha e) (ht.open i e ha hta hΔ)
  | .sexp_bool hp ht =>
      simpa only [Runtime.sexp_bool, opn_op, opnArg, shift_zero] using
        Typing.sexp_bool (hp.open i ha e) (ht.open i e ha hta hΔ)
  | .sexp_id hp ht =>
      simpa only [Runtime.sexp_id, opn_op, opnArg, shift_zero] using
        Typing.sexp_id (hp.open i ha e) (ht.open i e ha hta hΔ)
  | .nil => exact .nil
  | .pair hp hq hp' hq' =>
      simpa only [Runtime.pair, opn_op, opnArg, shift_zero] using
        Typing.pair (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .app hf hp htf htp hs =>
      simpa only [Runtime.app, opn_op, opnArg, shift_zero] using
        Typing.app (hf.open i ha e) (hp.open i ha e)
          (htf.open i e ha hta hΔ) (htp.open i e ha hta hΔ) (hs.open i e ha hta hΔ)
  | .arith hop hp hq hp' hq' =>
      simpa only [Runtime.operation, opn_op, opnArg, shift_zero] using
        Typing.arith hop (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .eq hA hp hq hp' hq' =>
      simpa only [Runtime.operation, opn_op, opnArg, shift_zero] using
        Typing.eq hA (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .lt hp hq hp' hq' =>
      simpa only [Runtime.operation, opn_op, opnArg, shift_zero] using
        Typing.lt (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .ifE hg ht hy hn =>
      simpa only [Runtime.ifE, opn_op, opnArg, shift_zero] using
        Typing.ifE (hg.open i ha e) (ht.open i e ha hta hΔ) (hy.open i e ha hta hΔ) (hn.open i e ha hta hΔ)
  | .matchE hp ht hs hf =>
      simpa only [Runtime.matchE, opn_op, opnArg, shift_zero] using
        Typing.matchE (hp.open i ha e) (ht.open i e ha hta hΔ) (hs.open i e ha hta hΔ) hf
  | .async hb =>
      simpa only [Runtime.async, opn_op, opnArg, shift_zero] using
        Typing.async (hb.open i e ha hta hΔ)
  | .letE (A := C) hr hb =>
      have ho := pushMany_open [C] i e hΔ
      simpa only [Runtime.letE, opn_op, opnArg, shift_zero] using
        Typing.letE (hr.open i e ha hta hΔ)
          (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
termination_by structural ht

theorem BranchTyping.open {sig Γ m Δ p b B} (ht : BranchTyping sig Γ (n := m) Δ p b B)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    BranchTyping sig Γ Δ' p (opn i a b e) B := by
  match ht with
  | .int hb =>
      have ho := pushMany_open [.int] i e hΔ
      simpa only [Runtime.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.int (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
  | .bool hb =>
      have ho := pushMany_open [.bool] i e hΔ
      simpa only [Runtime.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.bool (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
  | .id hb =>
      have ho := pushMany_open [.id] i e hΔ
      simpa only [Runtime.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.id (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
  | .nil hb =>
      simpa only [Runtime.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.nil (hb.open i e ha hta hΔ)
  | .pair hb =>
      have ho := pushMany_open [.sexp, .sexp] i e hΔ
      simpa only [Runtime.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.pair (hb.open (n := n + 2) (shiftIdx 2 i) (by omega) ha
          (by simpa [push, show 2 = 1 + 1 from rfl] using hta) ho.2)
  | .wildcard hb =>
      simpa only [Runtime.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.wildcard (hb.open i e ha hta hΔ)
termination_by structural ht

theorem ArgsTyping.open {sig Γ m Δ As ms args} (ht : ArgsTyping sig Γ (n := m) Δ As (ms := ms) args)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    ArgsTyping sig Γ Δ' As (opnArg i a args e) := by
  match ht with
  | .nil => exact .nil
  | .cons hp ht hs =>
      simpa only [opnArg, shift_zero] using
        ArgsTyping.cons (hp.open i ha e) (ht.open i e ha hta hΔ) (hs.open i e ha hta hΔ)
termination_by structural ht

theorem BranchesTyping.open {sig Γ m Δ ps ms bs B} (ht : BranchesTyping sig Γ (n := m) Δ ps (ms := ms) bs B)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    BranchesTyping sig Γ Δ' ps (opnArg i a bs e) B := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs =>
      simpa only [opnArg, shift_zero] using BranchesTyping.cons (hb.open i e ha hta hΔ) (hs.open i e ha hta hΔ)
termination_by structural ht
end

-- A single replacement has the required type at every free-name lookup.
private theorem single_typed {sig Γ x A a} (hta : HasType sig Γ a A) :
    ∀ y B, ((x, A) :: Γ).lookup y = some B → HasType sig Γ (((x ≔ a) : Sb signature) y) B := by
  intro y B hy
  by_cases h : x = y
  · subst y
    have : A = B := by simpa using hy
    subst B
    simpa using hta
  · rw [Sb.single_neq a h]
    exact .free (by simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm h)] using hy)

/-- R-Substitution for term subjects in the locally nameless representation. -/
theorem substitution {sig Γ x A t B a} (ht : HasType sig ((x, A) :: Γ) t B)
    (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a A) : HasType sig Γ ((x ≔ a) * t) B :=
  ht.subst (atom_substitution x ha) (single_typed hta)

/-- The branch-subject clause of R-Substitution. -/
theorem branch_substitution {sig Γ x A p b B a} (ht : HasBranchType sig ((x, A) :: Γ) p b B)
    (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a A) : HasBranchType sig Γ p ((x ≔ a) * b) B :=
  ht.subst (atom_substitution x ha) (single_typed hta)

/-- Instantiate slot zero, retaining the other bound slots and their types. -/
theorem Typing.conc {sig Γ n Δ A body B} (hb : Typing sig Γ (n := n + 1) (push A Δ) body B)
    {a : RawTerm 0} (ha : IsAtom (domain sig) a) (hta : HasType sig Γ a A) : Typing sig Γ Δ (body.conc a) B := by
  apply hb.open (0 : Fin (n + 1)) rfl ha (by simpa [push] using hta)
  intro j
  refine Fin.cases ?_ (fun k h => ?_) j
  · intro h; exact False.elim (h rfl)
  · have hr : remove (0 : Fin (n + 1)) k.succ h = k := by
      apply Fin.ext
      simp [remove_val]
    simp only [Fin.cast_refl, id_eq, hr, push, Fin.cases_succ]

/-- Ordered multi-binder instantiation; each atom has the type of its slot. -/
theorem Typing.instantiate {sig Γ args Δ body B} (hb : Typing sig Γ (n := args.length) Δ body B)
    (ha : ∀ i : Fin args.length, IsAtom (domain sig) args[i] ∧ HasType sig Γ args[i] (Δ i)) :
    HasType sig Γ (instantiate args body) B := by
  induction args with
  | nil =>
      have hΔ : Δ = Fin.elim0 := funext (fun i => Fin.elim0 i)
      simpa only [instantiate, hΔ] using hb
  | cons a rest ih =>
      have hΔ : push (Δ 0) (fun i => Δ i.succ) = Δ := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hb' : Typing sig Γ (push (Δ 0) (fun i => Δ i.succ)) body B := by
        rw [hΔ]; exact hb
      exact ih (hb'.conc (ha 0).1 (ha 0).2) (fun i => ha i.succ)

/-- Transport only the scope index; the syntax and assigned type are unchanged. -/
theorem Typing.castScope {sig Γ m Δ t A} (ht : Typing sig Γ (n := m) Δ t A) {n} (e : m = n) :
    Typing sig Γ (fun i => Δ (Fin.cast e.symm i)) (t.castScope e) A := by
  cases e; exact ht

-- T-App's pointwise premises supply exactly one type per actual argument.
private theorem args_types {sig Γ As args} (hs : ArgsTyping sig Γ Fin.elim0 As (toArgs args)) :
    ∃ e : 0 + As.length = args.length, ∀ i : Fin args.length,
      IsAtom (domain sig) args[i] ∧ HasType sig Γ args[i] (pushMany As Fin.elim0 (Fin.cast e.symm i)) := by
  induction args generalizing As with
  | nil => cases hs; exact ⟨rfl, fun i => Fin.elim0 i⟩
  | cons a rest ih =>
      cases hs with
      | cons ha ht hs =>
          obtain ⟨e, h⟩ := ih hs
          refine ⟨by simp only [List.length_cons, Nat.zero_add] at e ⊢; omega, ?_⟩
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa [pushMany, push] using And.intro ha ht
          · simpa [pushMany, push] using h j

/-- Apply the ordered argument typing premises to a multi-binder body. -/
theorem ArgsTyping.instantiate {sig Γ As args body B} (hs : ArgsTyping sig Γ Fin.elim0 As (toArgs args))
    (hb : Typing sig Γ (pushMany As Fin.elim0) body B) (e : 0 + As.length = args.length) :
    HasType sig Γ (instantiate args (body.castScope e)) B := by
  obtain ⟨_, h⟩ := args_types hs
  exact (hb.castScope e).instantiate h

-- Signature extension changes neither Γ nor bound slots.
mutual
theorem Typing.sigma_weaken {sig sig' Γ n Δ t A} (ht : Typing sig Γ (n := n) Δ t A)
    (h : sig.Extends sig') : Typing sig' Γ Δ t A := by
  match ht with
  | .bound i => exact .bound i
  | .free hx => exact .free hx
  | .future hp => exact .future (h _ _ hp)
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE hb => exact .funE (hb.sigma_weaken h)
  | .fixE hb => exact .fixE (hb.sigma_weaken h)
  | .sexp_int ha ht => exact .sexp_int (ha.mono h.domain) (ht.sigma_weaken h)
  | .sexp_bool ha ht => exact .sexp_bool (ha.mono h.domain) (ht.sigma_weaken h)
  | .sexp_id ha ht => exact .sexp_id (ha.mono h.domain) (ht.sigma_weaken h)
  | .nil => exact .nil
  | .pair ha hb ht hu => exact .pair (ha.mono h.domain) (hb.mono h.domain) (ht.sigma_weaken h) (hu.sigma_weaken h)
  | .app hf ha ht hu hs => exact .app (hf.mono h.domain) (ha.mono h.domain) (ht.sigma_weaken h) (hu.sigma_weaken h) (hs.sigma_weaken h)
  | .arith hop ha hb ht hu => exact .arith hop (ha.mono h.domain) (hb.mono h.domain) (ht.sigma_weaken h) (hu.sigma_weaken h)
  | .eq hA ha hb ht hu => exact .eq hA (ha.mono h.domain) (hb.mono h.domain) (ht.sigma_weaken h) (hu.sigma_weaken h)
  | .lt ha hb ht hu => exact .lt (ha.mono h.domain) (hb.mono h.domain) (ht.sigma_weaken h) (hu.sigma_weaken h)
  | .ifE hg ht hy hn => exact .ifE (hg.mono h.domain) (ht.sigma_weaken h) (hy.sigma_weaken h) (hn.sigma_weaken h)
  | .letE hr hb => exact .letE (hr.sigma_weaken h) (hb.sigma_weaken h)
  | .matchE ha ht hs hf => exact .matchE (ha.mono h.domain) (ht.sigma_weaken h) (hs.sigma_weaken h) hf
  | .async hb => exact .async (hb.sigma_weaken h)
termination_by structural ht

theorem BranchTyping.sigma_weaken {sig sig' Γ n Δ p b A} (ht : BranchTyping sig Γ (n := n) Δ p b A)
    (h : sig.Extends sig') : BranchTyping sig' Γ Δ p b A := by
  match ht with
  | .int hb => exact .int (hb.sigma_weaken h)
  | .bool hb => exact .bool (hb.sigma_weaken h)
  | .id hb => exact .id (hb.sigma_weaken h)
  | .nil hb => exact .nil (hb.sigma_weaken h)
  | .pair hb => exact .pair (hb.sigma_weaken h)
  | .wildcard hb => exact .wildcard (hb.sigma_weaken h)
termination_by structural ht

theorem ArgsTyping.sigma_weaken {sig sig' Γ n Δ As ms args} (ht : ArgsTyping sig Γ (n := n) Δ As (ms := ms) args)
    (h : sig.Extends sig') : ArgsTyping sig' Γ Δ As args := by
  match ht with
  | .nil => exact .nil
  | .cons ha ht hs => exact .cons (ha.mono h.domain) (ht.sigma_weaken h) (hs.sigma_weaken h)
termination_by structural ht

theorem BranchesTyping.sigma_weaken {sig sig' Γ n Δ ps ms bs A} (ht : BranchesTyping sig Γ (n := n) Δ ps (ms := ms) bs A)
    (h : sig.Extends sig') : BranchesTyping sig' Γ Δ ps bs A := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.sigma_weaken h) (hs.sigma_weaken h)
termination_by structural ht
end

-- Spawn records a type obtained from a separate typing premise.
-- Uniqueness identifies it with the result type recovered from the redex.
mutual
theorem Typing.unique {sig Γ n Δ t A} (ht : Typing sig Γ (n := n) Δ t A)
    {B} (hu : Typing sig Γ Δ t B) : A = B := by
  match ht with
  | .bound _ => cases hu; rfl
  | .free hx => cases hu with | free hy => exact Option.some.inj (hx.symm.trans hy)
  | .future hp => cases hu with | future hq => exact Option.some.inj (hp.symm.trans hq)
  | .integer _ => cases hu; rfl
  | .boolean _ => cases hu; rfl
  | .unit => cases hu; rfl
  | .identifier _ => cases hu; rfl
  | .funE _ => cases hu; rfl
  | .fixE _ => cases hu; rfl
  | .sexp_int _ _ => cases hu; rfl
  | .sexp_bool _ _ => cases hu; rfl
  | .sexp_id _ _ => cases hu; rfl
  | .nil => cases hu; rfl
  | .pair _ _ _ _ => cases hu; rfl
  | .app _ _ hf _ _ =>
      cases hu with
      | app _ _ hf' _ _ => exact (Source.Ty.arrow.inj (hf.unique hf')).2.2
  | .arith hop _ _ _ _ => cases hu <;> simp_all
  | .eq _ _ _ _ _ => cases hu <;> simp_all
  | .lt _ _ _ _ => cases hu <;> simp_all
  | .ifE _ _ hy _ => cases hu with | ifE _ _ hy' _ => exact hy.unique hy'
  | .letE hr hb =>
      cases hu with
      | letE hr' hb' =>
          cases hr.unique hr'
          exact hb.unique hb'
  | .matchE _ _ hs hf =>
      cases hu with
      | matchE _ _ hs' _ =>
          exact hs.unique hs' (by intro e; subst e; simp [Source.MatchPatterns] at hf)
  | .async hb => cases hu with | async hb' => exact hb.unique hb'
termination_by structural ht

theorem BranchTyping.unique {sig Γ n Δ p b A} (ht : BranchTyping sig Γ (n := n) Δ p b A)
    {q B} (hu : BranchTyping sig Γ Δ q b B) : A = B := by
  match ht with
  | .int hb => cases hu with | int hb' => exact hb.unique hb'
  | .bool hb => cases hu with | bool hb' => exact hb.unique hb'
  | .id hb => cases hu with | id hb' => exact hb.unique hb'
  | .nil hb => cases hu with | nil hb' => exact hb.unique hb'
  | .pair hb => cases hu with | pair hb' => exact hb.unique hb'
  | .wildcard hb => cases hu with | wildcard hb' => exact hb.unique hb'
termination_by structural ht
theorem BranchesTyping.unique {sig Γ n Δ ps ms bs A}
    (ht : BranchesTyping sig Γ (n := n) Δ ps (ms := ms) bs A)
    {qs B} (hu : BranchesTyping sig Γ Δ qs bs B) (hne : ps ≠ []) : A = B := by
  match ht with
  | .nil => exact False.elim (hne rfl)
  | .cons hb _ => cases hu with | cons hb' _ => exact hb.unique hb'
termination_by structural ht
end

mutual
/-- R-Scope at any binder depth. Support counts source variables, not future names. -/
theorem Typing.scope {sig Γ n Δ t A} (ht : Typing sig Γ (n := n) Δ t A) : supp t ⊆ Source.Context.domain Γ := by
  match ht with
  | .bound _ => exact Fset.empty_subset
  | .free hx => exact Fset.single_subset_iff.mpr (Source.Context.lookup_mem hx)
  | .future _ | .integer _ | .boolean _ | .unit | .identifier _ | .nil => exact Fset.empty_subset
  | .funE hb | .fixE hb | .sexp_int _ hb | .sexp_bool _ hb | .sexp_id _ hb | .async hb =>
      exact Fset.union_subset hb.scope Fset.empty_subset
  | .pair _ _ ha hb | .arith _ _ _ ha hb | .eq _ _ _ ha hb | .lt _ _ ha hb | .letE ha hb =>
      exact Fset.union_subset ha.scope (Fset.union_subset hb.scope Fset.empty_subset)
  | .app _ _ hf ha hs => exact Fset.union_subset hf.scope (Fset.union_subset ha.scope hs.scope)
  | .ifE _ hg hy hn =>
      exact Fset.union_subset hg.scope (Fset.union_subset hy.scope (Fset.union_subset hn.scope Fset.empty_subset))
  | .matchE _ ha hs _ => exact Fset.union_subset ha.scope hs.scope
termination_by structural ht

/-- R-Scope for branches. -/
theorem BranchTyping.scope {sig Γ n Δ p b A} (ht : BranchTyping sig Γ (n := n) Δ p b A) :
    supp b ⊆ Source.Context.domain Γ := by
  match ht with
  | .int hb | .bool hb | .id hb | .nil hb | .pair hb | .wildcard hb =>
      exact Fset.union_subset hb.scope Fset.empty_subset
termination_by structural ht

private theorem ArgsTyping.scope {sig Γ n Δ As ms args} (ht : ArgsTyping sig Γ (n := n) Δ As (ms := ms) args) :
    supp args ⊆ Source.Context.domain Γ := by
  match ht with
  | .nil => exact Fset.empty_subset
  | .cons _ ha hs => exact Fset.union_subset ha.scope hs.scope
termination_by structural ht

private theorem BranchesTyping.scope {sig Γ n Δ ps ms bs A}
    (ht : BranchesTyping sig Γ (n := n) Δ ps (ms := ms) bs A) : supp bs ⊆ Source.Context.domain Γ := by
  match ht with
  | .nil => exact Fset.empty_subset
  | .cons hb hs => exact Fset.union_subset hb.scope hs.scope
termination_by structural ht
end

/-- Closed runtime typings have no free source variables. -/
theorem Typing.closed {sig n Δ t A} (ht : Typing sig [] (n := n) Δ t A) : supp t ⊆ ∅ :=
  ht.scope

/-- R-Gamma-Weakening: preserve lookups of source variables, with Σ fixed. -/
theorem Typing.gamma_weaken {sig Γ n Δ t A} (ht : Typing sig Γ (n := n) Δ t A)
    {Γ' : Context} (hΓ : ∀ x B, Γ.lookup x = some B → Γ'.lookup x = some B) :
    Typing sig Γ' Δ t A := by
  simpa only [sbUnit] using ht.subst (σ := Sb.id) (fun x => IsAtom.free x)
    (fun x B hx => Typing.free (hΓ x B hx))

/-- R-Gamma-Weakening for branches. -/
theorem BranchTyping.gamma_weaken {sig Γ n Δ p b A} (ht : BranchTyping sig Γ (n := n) Δ p b A)
    {Γ' : Context} (hΓ : ∀ x B, Γ.lookup x = some B → Γ'.lookup x = some B) :
    BranchTyping sig Γ' Δ p b A := by
  simpa only [sbUnit] using ht.subst (σ := Sb.id) (fun x => IsAtom.free x)
    (fun x B hx => Typing.free (hΓ x B hx))

end SourceRuntime.Runtime

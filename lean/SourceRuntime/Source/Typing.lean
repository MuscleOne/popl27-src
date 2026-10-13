import SourceRuntime.Source.Reduction

/-!
Source typing (§6), with all term and branch rules.
Γ is a finite association list, read by List.lookup (the first binding wins).
Δ records bound-index types. A binder prepends its types in displayed order;
fix places self before its parameters. ArgsTyping and BranchesTyping express
pointwise premises on the paper's argument and branch sequences.
Substitution proofs follow the typed-substitution organization in
upstream/lean-subst/Examples/STLC/Theory.lean, using WSLN's operations throughout.
Preservation below covers all rules in source §7.
-/

namespace SourceRuntime.Source

open WSLN

abbrev Context := List (WSLN.Atom × Ty)

def push {n : Nat} (A : Ty) (Δ : Fin n → Ty) : Fin (n + 1) → Ty := Fin.cases A Δ

/-- The first displayed parameter occupies index zero. -/
def pushMany {n : Nat} (As : List Ty) (Δ : Fin n → Ty) : Fin (n + As.length) → Ty :=
  match As with
  | [] => Δ
  | A :: As => push A (pushMany As Δ)

mutual
/-- The IsAtom premises enforce the atom positions declared by the source grammar. -/
inductive Typing (Γ : Context) : {n : Nat} → (Fin n → Ty) → RawTerm n → Ty → Prop where
  | bound {n Δ} (i : Fin n) : Typing Γ Δ (.var i) (Δ i)
  | free {n Δ x A} : Γ.lookup x = some A → Typing Γ (n := n) Δ (var x) A
  | integer {n Δ} (z : Int) : Typing Γ (n := n) Δ (integer z) .int
  | boolean {n Δ} (b : Bool) : Typing Γ (n := n) Δ (boolean b) .bool
  | unit {n Δ} : Typing Γ (n := n) Δ unit .unit
  | identifier {n Δ} (i : Id) : Typing Γ (n := n) Δ (identifier i) .id
  | funE {n Δ first rest result} {body : RawTerm (n + (rest.length + 1))} :
      Typing Γ (pushMany (first :: rest) Δ) body result →
      Typing Γ Δ (funE first rest result body) (.arrow first rest result)
  | fixE {n Δ first rest result} {body : RawTerm (n + (rest.length + 2))} :
      Typing Γ (pushMany (.arrow first rest result :: first :: rest) Δ) body result →
      Typing Γ Δ (fixE first rest result body) (.arrow first rest result)
  | sexp_int {n Δ} {a : RawTerm n} :
      IsAtom a → Typing Γ Δ a .int → Typing Γ Δ (sexp_int a) .sexp
  | sexp_bool {n Δ} {a : RawTerm n} :
      IsAtom a → Typing Γ Δ a .bool → Typing Γ Δ (sexp_bool a) .sexp
  | sexp_id {n Δ} {a : RawTerm n} :
      IsAtom a → Typing Γ Δ a .id → Typing Γ Δ (sexp_id a) .sexp
  | nil {n Δ} : Typing Γ (n := n) Δ nil .sexp
  | pair {n Δ} {a b : RawTerm n} :
      IsAtom a → IsAtom b → Typing Γ Δ a .sexp → Typing Γ Δ b .sexp →
      Typing Γ Δ (pair a b) .sexp
  | app {n k Δ A As B} {fn first : RawTerm n} {rest : RawArgs n k} :
      IsAtom fn → IsAtom first → Typing Γ Δ fn (.arrow A As B) →
      Typing Γ Δ first A → ArgsTyping Γ Δ As rest → Typing Γ Δ (app fn first rest) B
  | arith {n Δ op} {a b : RawTerm n} :
      (op = .add ∨ op = .sub ∨ op = .mul) → IsAtom a → IsAtom b →
      Typing Γ Δ a .int → Typing Γ Δ b .int → Typing Γ Δ (operation op a b) .int
  | eq {n Δ A} {a b : RawTerm n} :
      (A = .int ∨ A = .id) → IsAtom a → IsAtom b →
      Typing Γ Δ a A → Typing Γ Δ b A → Typing Γ Δ (operation .eq a b) .bool
  | lt {n Δ} {a b : RawTerm n} :
      IsAtom a → IsAtom b → Typing Γ Δ a .int → Typing Γ Δ b .int →
      Typing Γ Δ (operation .lt a b) .bool
  | ifE {n Δ A} {guard yes no : RawTerm n} :
      IsAtom guard → Typing Γ Δ guard .bool → Typing Γ Δ yes A → Typing Γ Δ no A →
      Typing Γ Δ (ifE guard yes no) A
  | letE {n Δ A B} {rhs : RawTerm n} {body : RawTerm (n + 1)} :
      Typing Γ Δ rhs A → Typing Γ (push A Δ) body B → Typing Γ Δ (letE rhs body) B
  | matchE {n k Δ ps A} {a : RawTerm n} {bs : RawArgs n k} :
      IsAtom a → Typing Γ Δ a .sexp → BranchesTyping Γ Δ ps bs A →
      MatchPatterns ps → Typing Γ Δ (matchE a bs) A
  | async {n Δ A} {body : RawTerm n} : Typing Γ Δ body A → Typing Γ Δ (async body) A

inductive BranchTyping (Γ : Context) : {n : Nat} → (Fin n → Ty) → Pattern → RawTerm n → Ty → Prop where
  | int {n Δ A} {body : RawTerm (n + 1)} :
      Typing Γ (push .int Δ) body A → BranchTyping Γ Δ .int (branch .int body) A
  | bool {n Δ A} {body : RawTerm (n + 1)} :
      Typing Γ (push .bool Δ) body A → BranchTyping Γ Δ .bool (branch .bool body) A
  | id {n Δ A} {body : RawTerm (n + 1)} :
      Typing Γ (push .id Δ) body A → BranchTyping Γ Δ .id (branch .id body) A
  | nil {n Δ A} {body : RawTerm n} :
      Typing Γ Δ body A → BranchTyping Γ Δ .nil (branch .nil body) A
  | pair {n Δ A} {body : RawTerm (n + 2)} :
      Typing Γ (push .sexp (push .sexp Δ)) body A → BranchTyping Γ Δ .pair (branch .pair body) A
  | wildcard {n Δ A} {body : RawTerm n} :
      Typing Γ Δ body A → BranchTyping Γ Δ .wildcard (branch .wildcard body) A

/-- Pointwise argument typing, with the same ordered type sequence as T-App. -/
inductive ArgsTyping (Γ : Context) : {n : Nat} → (Fin n → Ty) → List Ty →
    {ms : List Nat} → Arg signature n ms → Prop where
  | nil {n Δ} : ArgsTyping Γ (n := n) Δ [] .nil
  | cons {n Δ A As ms} {a : RawTerm n} {rest : Arg signature n ms} :
      IsAtom a → Typing Γ Δ a A → ArgsTyping Γ Δ As rest →
      ArgsTyping Γ Δ (A :: As) (.cons (m := 0) a rest)

/-- All branches have the one result type required by T-Match. -/
inductive BranchesTyping (Γ : Context) : {n : Nat} → (Fin n → Ty) → List Pattern →
    {ms : List Nat} → Arg signature n ms → Ty → Prop where
  | nil {n Δ A} : BranchesTyping Γ (n := n) Δ [] .nil A
  | cons {n Δ p ps ms A} {b : RawTerm n} {rest : Arg signature n ms} :
      BranchTyping Γ Δ p b A → BranchesTyping Γ Δ ps rest A →
      BranchesTyping Γ Δ (p :: ps) (.cons (m := 0) b rest) A
end

abbrev HasType (Γ : Context) (t : RawTerm 0) (A : Ty) := Typing Γ Fin.elim0 t A
abbrev HasBranchType (Γ : Context) (p : Pattern) (b : RawTerm 0) (A : Ty) :=
  BranchTyping Γ Fin.elim0 p b A

/-- The existing addition notation is an instance of T-Arith. -/
theorem Typing.add {Γ n Δ} {a b : RawTerm n}
    (ha : IsAtom a) (hb : IsAtom b) (hta : Typing Γ Δ a .int) (htb : Typing Γ Δ b .int) :
    Typing Γ Δ (add a b) .int := .arith (Or.inl rfl) ha hb hta htb

mutual
theorem Typing.formed {Γ n Δ t A} (h : Typing Γ (n := n) Δ t A) : IsTerm t := by
  match h with
  | .bound i => exact .atom (.bound i)
  | .free _ => exact .atom (.free _)
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

theorem BranchTyping.formed {Γ n Δ p b A} (h : BranchTyping Γ (n := n) Δ p b A) :
    IsBranch p b := by
  match h with
  | .int hb => exact .branch hb.formed
  | .bool hb => exact .branch hb.formed
  | .id hb => exact .branch hb.formed
  | .nil hb => exact .branch hb.formed
  | .pair hb => exact .branch hb.formed
  | .wildcard hb => exact .branch hb.formed
termination_by structural h

theorem ArgsTyping.formed {Γ n Δ As ms args} (h : ArgsTyping Γ (n := n) Δ As (ms := ms) args) :
    IsAtoms args := by
  match h with
  | .nil => exact .nil
  | .cons ha _ hs => exact .cons ha hs.formed
termination_by structural h

theorem BranchesTyping.formed {Γ n Δ ps ms bs A}
    (h : BranchesTyping Γ (n := n) Δ ps (ms := ms) bs A) : IsBranches ps bs := by
  match h with
  | .nil => exact .nil
  | .cons hb hs => exact .cons hb.formed hs.formed
termination_by structural h
end

/-- The finite domain of the free-variable environment; shadowing does not change membership. -/
def Context.domain (Γ : Context) : Fset := supp (Γ.map Prod.fst)

theorem Context.lookup_mem {Γ : Context} {x A} (h : Γ.lookup x = some A) :
    x ∈ Γ.domain := by
  induction Γ with
  | nil => simp at h
  | cons p Γ ih =>
      obtain ⟨y, B⟩ := p
      by_cases he : x = y
      · subst x; exact .unionL .single
      · exact .unionR (ih (by simpa [List.lookup, beq_eq_false_iff_ne.mpr he] using h))

mutual
/-- S-Scope: typing accounts for every free source variable, at any binder depth. -/
theorem Typing.scope {Γ n Δ t A} (ht : Typing Γ (n := n) Δ t A) : supp t ⊆ Γ.domain := by
  match ht with
  | .bound _ => exact Fset.empty_subset
  | .free hx => exact Fset.single_subset_iff.mpr (Context.lookup_mem hx)
  | .integer _ | .boolean _ | .unit | .identifier _ | .nil => exact Fset.empty_subset
  | .funE hb | .fixE hb | .sexp_int _ hb | .sexp_bool _ hb | .sexp_id _ hb | .async hb =>
      exact Fset.union_subset hb.scope Fset.empty_subset
  | .pair _ _ ha hb | .arith _ _ _ ha hb | .eq _ _ _ ha hb | .lt _ _ ha hb | .letE ha hb =>
      exact Fset.union_subset ha.scope (Fset.union_subset hb.scope Fset.empty_subset)
  | .app _ _ hf ha hs => exact Fset.union_subset hf.scope (Fset.union_subset ha.scope hs.scope)
  | .ifE _ hg hy hn =>
      exact Fset.union_subset hg.scope (Fset.union_subset hy.scope (Fset.union_subset hn.scope Fset.empty_subset))
  | .matchE _ ha hs _ => exact Fset.union_subset ha.scope hs.scope
termination_by structural ht

/-- S-Scope for branches; pattern-bound indices are excluded from free support. -/
theorem BranchTyping.scope {Γ n Δ p b A} (ht : BranchTyping Γ (n := n) Δ p b A) :
    supp b ⊆ Γ.domain := by
  match ht with
  | .int hb | .bool hb | .id hb | .nil hb | .pair hb | .wildcard hb =>
      exact Fset.union_subset hb.scope Fset.empty_subset
termination_by structural ht

private theorem ArgsTyping.scope {Γ n Δ As ms args} (ht : ArgsTyping Γ (n := n) Δ As (ms := ms) args) :
    supp args ⊆ Γ.domain := by
  match ht with
  | .nil => exact Fset.empty_subset
  | .cons _ ha hs => exact Fset.union_subset ha.scope hs.scope
termination_by structural ht

private theorem BranchesTyping.scope {Γ n Δ ps ms bs A}
    (ht : BranchesTyping Γ (n := n) Δ ps (ms := ms) bs A) : supp bs ⊆ Γ.domain := by
  match ht with
  | .nil => exact Fset.empty_subset
  | .cons hb hs => exact Fset.union_subset hb.scope hs.scope
termination_by structural ht
end

-- Index identities and context transport beneath nested binders.
@[simp] private theorem shift_zero {n} (i : Fin n) : shiftIdx 0 i = i := by
  apply Fin.ext; simp [shiftIdx]

@[simp] private theorem insert_succ_zero {n} (i : Fin (n + 1)) :
    WSLN.insert i.succ 0 = 0 := by
  apply Fin.ext; simp [insert_val]

@[simp] private theorem insert_succ_succ {n} (i : Fin (n + 1)) (j : Fin n) :
    insert i.succ j.succ = (insert i j).succ := by
  apply Fin.ext
  by_cases h : j.val < i.val <;> simp [insert_val, h]

@[simp] private theorem remove_succ_zero {n} (i : Fin (n + 1)) (h : i.succ ≠ 0) :
    remove i.succ 0 h = 0 := by
  apply Fin.ext; simp [remove_val]

private theorem remove_succ_succ {n} (i j : Fin (n + 1)) (h : i ≠ j) :
    remove i.succ j.succ (fun e => h (Fin.succ_inj.mp e)) = (remove i j h).succ := by
  apply Fin.ext
  have hne : i.val ≠ j.val := fun e => h (Fin.ext e)
  by_cases hlt : j.val < i.val
  · simp [remove_val, hlt]
  · simp only [remove_val, Fin.val_succ, Nat.add_lt_add_iff_right, if_neg hlt]
    omega

@[simp] private theorem shift_succ {n} (k : Nat) (i : Fin n) :
    shiftIdx (k + 1) i = (shiftIdx k i).succ := by
  apply Fin.ext; simp [shiftIdx]; omega

theorem pushMany_weaken (As : List Ty) {m n} {Δ : Fin m → Ty} {Δ' : Fin n → Ty}
    (h : m ≤ n) (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) :
    ∀ i, pushMany As Δ' (Fin.castLE (Nat.add_le_add_right h As.length) i) = pushMany As Δ i := by
  induction As with
  | nil => exact hΔ
  | cons A As ih =>
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact ih j

private theorem pushMany_close (As : List Ty) {m n A} {Δ : Fin m → Ty} {Δ' : Fin n → Ty}
    (i : Fin n) (e : n = m + 1) (hi : Δ' i = A)
    (hΔ : ∀ j, Δ' (Fin.cast e.symm (insert (Fin.cast e i) j)) = Δ j) :
    pushMany As Δ' (shiftIdx As.length i) = A ∧
    ∀ j, pushMany As Δ'
      (Fin.cast (by omega : n + As.length = m + As.length + 1).symm
        (insert (Fin.cast (by omega) (shiftIdx As.length i)) j)) = pushMany As Δ j := by
  subst n
  induction As with
  | nil => simpa [pushMany] using And.intro hi hΔ
  | cons C As ih =>
      constructor
      · simpa [pushMany, push] using ih.1
      · intro j
        refine Fin.cases ?_ (fun k => ?_) j
        · simp [pushMany, push]
        · simpa [pushMany, push] using ih.2 k

theorem pushMany_open (As : List Ty) {m n} {Δ : Fin m → Ty} {Δ' : Fin n → Ty}
    (i : Fin m) (e : m = n + 1)
    (hΔ : ∀ j (h : i ≠ j), Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    pushMany As Δ (shiftIdx As.length i) = Δ i ∧
    ∀ j (h : shiftIdx As.length i ≠ j), pushMany As Δ'
      (remove (Fin.cast (by omega : m + As.length = n + As.length + 1) (shiftIdx As.length i))
        (Fin.cast (by omega) j) (cast_ne (by omega) h)) = pushMany As Δ j := by
  subst m
  induction As with
  | nil => simpa [pushMany] using And.intro (rfl : Δ i = Δ i) hΔ
  | cons C As ih =>
      constructor
      · simpa [pushMany, push] using ih.1
      · intro j
        refine Fin.cases ?_ (fun k h => ?_) j
        · intro h; simp [pushMany, push]
        · have hne : shiftIdx As.length i ≠ k := by
            intro eq
            apply h
            simpa using congrArg Fin.succ eq
          simp only [List.length_cons, pushMany, shift_succ, Fin.cast_succ_eq]
          rw [remove_succ_succ _ _ (cast_ne (by omega : n + 1 + As.length = n + As.length + 1) hne)]
          exact ih.2 k hne

-- Scope weakening preserves the types of all previously available indices.
mutual
theorem Typing.weaken {Γ m Δ t A} (ht : Typing Γ (n := m) Δ t A)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : Typing Γ Δ' (t.weaken n h) A := by
  match ht with
  | .bound i => rw [← hΔ i]; exact .bound _
  | .free hx => exact .free hx
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

theorem BranchTyping.weaken {Γ m Δ p b A} (ht : BranchTyping Γ (n := m) Δ p b A)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : BranchTyping Γ Δ' p (b.weaken n h) A := by
  match ht with
  | .int hb => exact .int (hb.weaken _ (pushMany_weaken [.int] h hΔ))
  | .bool hb => exact .bool (hb.weaken _ (pushMany_weaken [.bool] h hΔ))
  | .id hb => exact .id (hb.weaken _ (pushMany_weaken [.id] h hΔ))
  | .nil hb => exact .nil (hb.weaken h hΔ)
  | .pair hb => exact .pair (hb.weaken _ (pushMany_weaken [.sexp, .sexp] h hΔ))
  | .wildcard hb => exact .wildcard (hb.weaken h hΔ)
termination_by structural ht

theorem ArgsTyping.weaken {Γ m Δ As ms args} (ht : ArgsTyping Γ (n := m) Δ As (ms := ms) args)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : ArgsTyping Γ Δ' As (args.weaken n h) := by
  match ht with
  | .nil => exact .nil
  | .cons ha ht hs => exact .cons (ha.weaken h) (ht.weaken h hΔ) (hs.weaken h hΔ)
termination_by structural ht

theorem BranchesTyping.weaken {Γ m Δ ps ms bs A}
    (ht : BranchesTyping Γ (n := m) Δ ps (ms := ms) bs A)
    {n : Nat} (h : m ≤ n) {Δ' : Fin n → Ty}
    (hΔ : ∀ i, Δ' (Fin.castLE h i) = Δ i) : BranchesTyping Γ Δ' ps (bs.weaken n h) A := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.weaken h hΔ) (hs.weaken h hΔ)
termination_by structural ht
end

mutual
/-- Simultaneous atom substitution, respecting the types assigned by Γ. -/
theorem Typing.subst {Γ n Δ t A} (ht : Typing Γ (n := n) Δ t A)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType Γ' (σ x) B) : Typing Γ' Δ (σ * t) A := by
  match ht with
  | .bound i => exact .bound i
  | .free hx => exact (hσ _ _ hx).weaken (Nat.zero_le n) (fun i => Fin.elim0 i)
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

theorem BranchTyping.subst {Γ n Δ p b A} (ht : BranchTyping Γ (n := n) Δ p b A)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType Γ' (σ x) B) : BranchTyping Γ' Δ p (σ * b) A := by
  match ht with
  | .int hb => exact .int (hb.subst ha hσ)
  | .bool hb => exact .bool (hb.subst ha hσ)
  | .id hb => exact .id (hb.subst ha hσ)
  | .nil hb => exact .nil (hb.subst ha hσ)
  | .pair hb => exact .pair (hb.subst ha hσ)
  | .wildcard hb => exact .wildcard (hb.subst ha hσ)
termination_by structural ht

theorem ArgsTyping.subst {Γ n Δ As ms args} (ht : ArgsTyping Γ (n := n) Δ As (ms := ms) args)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType Γ' (σ x) B) : ArgsTyping Γ' Δ As (σ * args) := by
  match ht with
  | .nil => exact .nil
  | .cons hp ht hs => exact .cons (hp.subst ha) (ht.subst ha hσ) (hs.subst ha hσ)
termination_by structural ht

theorem BranchesTyping.subst {Γ n Δ ps ms bs A} (ht : BranchesTyping Γ (n := n) Δ ps (ms := ms) bs A)
    {Γ' : Context} {σ : Sb signature} (ha : ∀ x, IsAtom (σ x))
    (hσ : ∀ x B, Γ.lookup x = some B → HasType Γ' (σ x) B) : BranchesTyping Γ' Δ ps (σ * bs) A := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.subst ha hσ) (hs.subst ha hσ)
termination_by structural ht
end

/-- S-Weakening: extend Γ while preserving its successful lookups.
    Unlike scope weakening, this leaves the term and its bound indices unchanged. -/
theorem Typing.gamma_weaken {Γ n Δ t A} (ht : Typing Γ (n := n) Δ t A)
    {Γ' : Context} (hΓ : ∀ x B, Γ.lookup x = some B → Γ'.lookup x = some B) :
    Typing Γ' Δ t A := by
  simpa only [sbUnit] using ht.subst (σ := Sb.id) (fun x => IsAtom.free x)
    (fun x B hx => Typing.free (hΓ x B hx))

/-- S-Weakening for branches, derived from identity atom substitution. -/
theorem BranchTyping.gamma_weaken {Γ n Δ p b A} (ht : BranchTyping Γ (n := n) Δ p b A)
    {Γ' : Context} (hΓ : ∀ x B, Γ.lookup x = some B → Γ'.lookup x = some B) :
    BranchTyping Γ' Δ p b A := by
  simpa only [sbUnit] using ht.subst (σ := Sb.id) (fun x => IsAtom.free x)
    (fun x B hx => Typing.free (hΓ x B hx))

mutual
/-- Move a named variable from Γ to its chosen slot in Δ. -/
theorem Typing.close {Γ x A m Δ t B} (ht : Typing ((x, A) :: Γ) (n := m) Δ t B)
    {n : Nat} (i : Fin n) (e : n = m + 1) {Δ' : Fin n → Ty}
    (hi : Δ' i = A)
    (hΔ : ∀ j, Δ' (Fin.cast e.symm (insert (Fin.cast e i) j)) = Δ j) :
    Typing Γ Δ' (cls x i t e) B := by
  subst n
  match ht with
  | .bound j => rw [← hΔ j]; exact .bound _
  | .free (x := y) hy =>
      by_cases h : x = y
      · subst y
        simp only [var, cls_atom_eq]
        have hA := List.lookup_cons_self.symm.trans hy
        have hAB := Option.some.inj hA
        rw [← hAB, ← hi]
        exact .bound i
      · rw [show var y = Trm.atom y from rfl, cls_atom_ne i rfl h]
        exact .free (by simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm h)] using hy)
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier j => exact .identifier j
  | .funE (first := first) (rest := rest) (result := result) hb =>
      have hc := pushMany_close (first :: rest) i rfl hi hΔ
      simpa only [Source.funE, cls_op, clsArg] using
        Typing.funE (hb.close (shiftIdx _ i) (by omega) hc.1 hc.2)
  | .fixE (first := first) (rest := rest) (result := result) hb =>
      have hc := pushMany_close (.arrow first rest result :: first :: rest) i rfl hi hΔ
      simpa only [Source.fixE, cls_op, clsArg] using
        Typing.fixE (hb.close (shiftIdx _ i) (by omega) hc.1 hc.2)
  | .sexp_int hp ht =>
      simpa only [Source.sexp_int, cls_op, clsArg, shift_zero] using
        Typing.sexp_int (hp.close x i rfl) (ht.close i rfl hi hΔ)
  | .sexp_bool hp ht =>
      simpa only [Source.sexp_bool, cls_op, clsArg, shift_zero] using
        Typing.sexp_bool (hp.close x i rfl) (ht.close i rfl hi hΔ)
  | .sexp_id hp ht =>
      simpa only [Source.sexp_id, cls_op, clsArg, shift_zero] using
        Typing.sexp_id (hp.close x i rfl) (ht.close i rfl hi hΔ)
  | .nil => exact .nil
  | .pair hp hq hp' hq' =>
      simpa only [Source.pair, cls_op, clsArg, shift_zero] using
        Typing.pair (hp.close x i rfl) (hq.close x i rfl) (hp'.close i rfl hi hΔ) (hq'.close i rfl hi hΔ)
  | .app hf hp htf htp hs =>
      simpa only [Source.app, cls_op, clsArg, shift_zero] using
        Typing.app (hf.close x i rfl) (hp.close x i rfl)
          (htf.close i rfl hi hΔ) (htp.close i rfl hi hΔ) (hs.close i rfl hi hΔ)
  | .arith hop hp hq hp' hq' =>
      simpa only [Source.operation, cls_op, clsArg, shift_zero] using
        Typing.arith hop (hp.close x i rfl) (hq.close x i rfl) (hp'.close i rfl hi hΔ) (hq'.close i rfl hi hΔ)
  | .eq hA hp hq hp' hq' =>
      simpa only [Source.operation, cls_op, clsArg, shift_zero] using
        Typing.eq hA (hp.close x i rfl) (hq.close x i rfl) (hp'.close i rfl hi hΔ) (hq'.close i rfl hi hΔ)
  | .lt hp hq hp' hq' =>
      simpa only [Source.operation, cls_op, clsArg, shift_zero] using
        Typing.lt (hp.close x i rfl) (hq.close x i rfl) (hp'.close i rfl hi hΔ) (hq'.close i rfl hi hΔ)
  | .ifE hg ht hy hn =>
      simpa only [Source.ifE, cls_op, clsArg, shift_zero] using
        Typing.ifE (hg.close x i rfl) (ht.close i rfl hi hΔ) (hy.close i rfl hi hΔ) (hn.close i rfl hi hΔ)
  | .matchE hp ht hs hf =>
      simpa only [Source.matchE, cls_op, clsArg, shift_zero] using
        Typing.matchE (hp.close x i rfl) (ht.close i rfl hi hΔ) (hs.close i rfl hi hΔ) hf
  | .async hb =>
      simpa only [Source.async, cls_op, clsArg, shift_zero] using
        Typing.async (hb.close i rfl hi hΔ)
  | .letE (A := C) hr hb =>
      have hc := pushMany_close [C] i rfl hi hΔ
      simpa only [Source.letE, cls_op, clsArg, shift_zero] using
        Typing.letE (hr.close i rfl hi hΔ) (hb.close (shiftIdx 1 i) rfl hc.1 hc.2)
termination_by structural ht

theorem BranchTyping.close {Γ x A m Δ p b B} (ht : BranchTyping ((x, A) :: Γ) (n := m) Δ p b B)
    {n : Nat} (i : Fin n) (e : n = m + 1) {Δ' : Fin n → Ty}
    (hi : Δ' i = A)
    (hΔ : ∀ j, Δ' (Fin.cast e.symm (insert (Fin.cast e i) j)) = Δ j) :
    BranchTyping Γ Δ' p (cls x i b e) B := by
  subst n
  match ht with
  | .int hb =>
      have hc := pushMany_close [.int] i rfl hi hΔ
      simpa only [Source.branch, Pattern.arity, cls_op, clsArg, shift_zero] using
        BranchTyping.int (hb.close (shiftIdx 1 i) rfl hc.1 hc.2)
  | .bool hb =>
      have hc := pushMany_close [.bool] i rfl hi hΔ
      simpa only [Source.branch, Pattern.arity, cls_op, clsArg, shift_zero] using
        BranchTyping.bool (hb.close (shiftIdx 1 i) rfl hc.1 hc.2)
  | .id hb =>
      have hc := pushMany_close [.id] i rfl hi hΔ
      simpa only [Source.branch, Pattern.arity, cls_op, clsArg, shift_zero] using
        BranchTyping.id (hb.close (shiftIdx 1 i) rfl hc.1 hc.2)
  | .nil hb =>
      simpa only [Source.branch, Pattern.arity, cls_op, clsArg, shift_zero] using
        BranchTyping.nil (hb.close i rfl hi hΔ)
  | .pair hb =>
      have hc := pushMany_close [.sexp, .sexp] i rfl hi hΔ
      simpa only [Source.branch, Pattern.arity, cls_op, clsArg, shift_zero] using
        BranchTyping.pair (hb.close (shiftIdx 2 i) rfl hc.1 hc.2)
  | .wildcard hb =>
      simpa only [Source.branch, Pattern.arity, cls_op, clsArg, shift_zero] using
        BranchTyping.wildcard (hb.close i rfl hi hΔ)
termination_by structural ht

theorem ArgsTyping.close {Γ x A m Δ As ms args} (ht : ArgsTyping ((x, A) :: Γ) (n := m) Δ As (ms := ms) args)
    {n : Nat} (i : Fin n) (e : n = m + 1) {Δ' : Fin n → Ty}
    (hi : Δ' i = A)
    (hΔ : ∀ j, Δ' (Fin.cast e.symm (insert (Fin.cast e i) j)) = Δ j) :
    ArgsTyping Γ Δ' As (clsArg x i args e) := by
  subst n
  match ht with
  | .nil => exact .nil
  | .cons hp ht hs =>
      simpa only [clsArg, shift_zero] using
        ArgsTyping.cons (hp.close x i rfl) (ht.close i rfl hi hΔ) (hs.close i rfl hi hΔ)
termination_by structural ht

theorem BranchesTyping.close {Γ x A m Δ ps ms bs B} (ht : BranchesTyping ((x, A) :: Γ) (n := m) Δ ps (ms := ms) bs B)
    {n : Nat} (i : Fin n) (e : n = m + 1) {Δ' : Fin n → Ty}
    (hi : Δ' i = A)
    (hΔ : ∀ j, Δ' (Fin.cast e.symm (insert (Fin.cast e i) j)) = Δ j) :
    BranchesTyping Γ Δ' ps (clsArg x i bs e) B := by
  subst n
  match ht with
  | .nil => exact .nil
  | .cons hb hs =>
      simpa only [clsArg, shift_zero] using BranchesTyping.cons (hb.close i rfl hi hΔ) (hs.close i rfl hi hΔ)
termination_by structural ht
end

mutual
/-- Replace a bound slot by a well-typed atom, preserving the other slot types. -/
theorem Typing.open {Γ m Δ t B} (ht : Typing Γ (n := m) Δ t B)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom a) (hta : HasType Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    Typing Γ Δ' (opn i a t e) B := by
  match ht with
  | .bound j =>
      by_cases h : i = j
      · subst j
        rw [opn_var_eq]
        exact hta.weaken (Nat.zero_le n) (fun k => Fin.elim0 k)
      · rw [opn_var_ne a e h, ← hΔ j h]
        exact .bound _
  | .free hx => exact .free hx
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier j => exact .identifier j
  | .funE (first := first) (rest := rest) (result := result) hb =>
      have ho := pushMany_open (first :: rest) i e hΔ
      simpa only [Source.funE, opn_op, opnArg] using
        Typing.funE (hb.open (shiftIdx _ i) (by omega) ha (by simpa only [ho.1] using hta) ho.2)
  | .fixE (first := first) (rest := rest) (result := result) hb =>
      have ho := pushMany_open (.arrow first rest result :: first :: rest) i e hΔ
      simpa only [Source.fixE, opn_op, opnArg] using
        Typing.fixE (hb.open (shiftIdx _ i) (by omega) ha (by simpa only [ho.1] using hta) ho.2)
  | .sexp_int hp ht =>
      simpa only [Source.sexp_int, opn_op, opnArg, shift_zero] using
        Typing.sexp_int (hp.open i ha e) (ht.open i e ha hta hΔ)
  | .sexp_bool hp ht =>
      simpa only [Source.sexp_bool, opn_op, opnArg, shift_zero] using
        Typing.sexp_bool (hp.open i ha e) (ht.open i e ha hta hΔ)
  | .sexp_id hp ht =>
      simpa only [Source.sexp_id, opn_op, opnArg, shift_zero] using
        Typing.sexp_id (hp.open i ha e) (ht.open i e ha hta hΔ)
  | .nil => exact .nil
  | .pair hp hq hp' hq' =>
      simpa only [Source.pair, opn_op, opnArg, shift_zero] using
        Typing.pair (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .app hf hp htf htp hs =>
      simpa only [Source.app, opn_op, opnArg, shift_zero] using
        Typing.app (hf.open i ha e) (hp.open i ha e)
          (htf.open i e ha hta hΔ) (htp.open i e ha hta hΔ) (hs.open i e ha hta hΔ)
  | .arith hop hp hq hp' hq' =>
      simpa only [Source.operation, opn_op, opnArg, shift_zero] using
        Typing.arith hop (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .eq hA hp hq hp' hq' =>
      simpa only [Source.operation, opn_op, opnArg, shift_zero] using
        Typing.eq hA (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .lt hp hq hp' hq' =>
      simpa only [Source.operation, opn_op, opnArg, shift_zero] using
        Typing.lt (hp.open i ha e) (hq.open i ha e) (hp'.open i e ha hta hΔ) (hq'.open i e ha hta hΔ)
  | .ifE hg ht hy hn =>
      simpa only [Source.ifE, opn_op, opnArg, shift_zero] using
        Typing.ifE (hg.open i ha e) (ht.open i e ha hta hΔ) (hy.open i e ha hta hΔ) (hn.open i e ha hta hΔ)
  | .matchE hp ht hs hf =>
      simpa only [Source.matchE, opn_op, opnArg, shift_zero] using
        Typing.matchE (hp.open i ha e) (ht.open i e ha hta hΔ) (hs.open i e ha hta hΔ) hf
  | .async hb =>
      simpa only [Source.async, opn_op, opnArg, shift_zero] using
        Typing.async (hb.open i e ha hta hΔ)
  | .letE (A := C) hr hb =>
      have ho := pushMany_open [C] i e hΔ
      simpa only [Source.letE, opn_op, opnArg, shift_zero] using
        Typing.letE (hr.open i e ha hta hΔ)
          (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
termination_by structural ht

theorem BranchTyping.open {Γ m Δ p b B} (ht : BranchTyping Γ (n := m) Δ p b B)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom a) (hta : HasType Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    BranchTyping Γ Δ' p (opn i a b e) B := by
  match ht with
  | .int hb =>
      have ho := pushMany_open [.int] i e hΔ
      simpa only [Source.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.int (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
  | .bool hb =>
      have ho := pushMany_open [.bool] i e hΔ
      simpa only [Source.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.bool (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
  | .id hb =>
      have ho := pushMany_open [.id] i e hΔ
      simpa only [Source.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.id (hb.open (n := n + 1) (shiftIdx 1 i) (by omega) ha (by simpa [push] using hta) ho.2)
  | .nil hb =>
      simpa only [Source.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.nil (hb.open i e ha hta hΔ)
  | .pair hb =>
      have ho := pushMany_open [.sexp, .sexp] i e hΔ
      simpa only [Source.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.pair (hb.open (n := n + 2) (shiftIdx 2 i) (by omega) ha
          (by simpa [push, show 2 = 1 + 1 from rfl] using hta) ho.2)
  | .wildcard hb =>
      simpa only [Source.branch, Pattern.arity, opn_op, opnArg, shift_zero] using
        BranchTyping.wildcard (hb.open i e ha hta hΔ)
termination_by structural ht

theorem ArgsTyping.open {Γ m Δ As ms args} (ht : ArgsTyping Γ (n := m) Δ As (ms := ms) args)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom a) (hta : HasType Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    ArgsTyping Γ Δ' As (opnArg i a args e) := by
  match ht with
  | .nil => exact .nil
  | .cons hp ht hs =>
      simpa only [opnArg, shift_zero] using
        ArgsTyping.cons (hp.open i ha e) (ht.open i e ha hta hΔ) (hs.open i e ha hta hΔ)
termination_by structural ht

theorem BranchesTyping.open {Γ m Δ ps ms bs B} (ht : BranchesTyping Γ (n := m) Δ ps (ms := ms) bs B)
    {n : Nat} (i : Fin m) (e : m = n + 1) {a : RawTerm 0}
    (ha : IsAtom a) (hta : HasType Γ a (Δ i)) {Δ' : Fin n → Ty}
    (hΔ : ∀ j (h : i ≠ j),
      Δ' (remove (Fin.cast e i) (Fin.cast e j) (cast_ne e h)) = Δ j) :
    BranchesTyping Γ Δ' ps (opnArg i a bs e) B := by
  match ht with
  | .nil => exact .nil
  | .cons hb hs =>
      simpa only [opnArg, shift_zero] using BranchesTyping.cons (hb.open i e ha hta hΔ) (hs.open i e ha hta hΔ)
termination_by structural ht
end

-- A single replacement has the required type at every free-name lookup.
private theorem single_typed {Γ x A a} (hta : HasType Γ a A) :
    ∀ y B, ((x, A) :: Γ).lookup y = some B → HasType Γ (((x ≔ a) : Sb signature) y) B := by
  intro y B hy
  by_cases h : x = y
  · subst y
    have : A = B := by simpa using hy
    subst B
    simpa using hta
  · rw [Sb.single_neq a h]
    exact .free (by simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr (Ne.symm h)] using hy)

/-- S-Substitution for term subjects in the locally nameless representation. -/
theorem substitution {Γ x A t B a} (ht : HasType ((x, A) :: Γ) t B)
    (ha : IsAtom a) (hta : HasType Γ a A) : HasType Γ ((x ≔ a) * t) B :=
  ht.subst (atom_substitution x ha) (single_typed hta)

/-- The branch-subject clause of S-Substitution. -/
theorem branch_substitution {Γ x A p b B a} (ht : HasBranchType ((x, A) :: Γ) p b B)
    (ha : IsAtom a) (hta : HasType Γ a A) : HasBranchType Γ p ((x ≔ a) * b) B :=
  ht.subst (atom_substitution x ha) (single_typed hta)

/-- T-Let with the paper's named environment update and the existing let_ constructor. -/
theorem typing_let {Γ x rhs body A B} (hr : HasType Γ rhs A)
    (hb : HasType ((x, A) :: Γ) body B) : HasType Γ (let_ x rhs body) B :=
  .letE hr (hb.close ⟨0, by omega⟩ rfl rfl (fun j => Fin.elim0 j))

/-- Instantiate slot zero, retaining the other bound slots and their types. -/
theorem Typing.conc {Γ n Δ A body B} (hb : Typing Γ (n := n + 1) (push A Δ) body B)
    {a : RawTerm 0} (ha : IsAtom a) (hta : HasType Γ a A) : Typing Γ Δ (body.conc a) B := by
  apply hb.open (0 : Fin (n + 1)) rfl ha (by simpa [push] using hta)
  intro j
  refine Fin.cases ?_ (fun k h => ?_) j
  · intro h; exact False.elim (h rfl)
  · have hr : remove (0 : Fin (n + 1)) k.succ h = k := by
      apply Fin.ext
      simp [remove_val]
    simp only [Fin.cast_refl, id_eq, hr, push, Fin.cases_succ]

/-- Ordered multi-binder instantiation; each atom has the type of its slot. -/
theorem Typing.instantiate {Γ args Δ body B} (hb : Typing Γ (n := args.length) Δ body B)
    (ha : ∀ i : Fin args.length, IsAtom args[i] ∧ HasType Γ args[i] (Δ i)) :
    HasType Γ (instantiate args body) B := by
  induction args with
  | nil =>
      have hΔ : Δ = Fin.elim0 := funext (fun i => Fin.elim0 i)
      simpa only [instantiate, hΔ] using hb
  | cons a rest ih =>
      have hΔ : push (Δ 0) (fun i => Δ i.succ) = Δ := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hb' : Typing Γ (push (Δ 0) (fun i => Δ i.succ)) body B := by
        rw [hΔ]; exact hb
      exact ih (hb'.conc (ha 0).1 (ha 0).2) (fun i => ha i.succ)

/-- Transport only the scope index; the syntax and assigned type are unchanged. -/
theorem Typing.castScope {Γ m Δ t A} (ht : Typing Γ (n := m) Δ t A) {n} (e : m = n) :
    Typing Γ (fun i => Δ (Fin.cast e.symm i)) (t.castScope e) A := by
  cases e; exact ht

-- T-App's pointwise premises supply exactly one type per actual argument.
private theorem args_types {Γ As args} (hs : ArgsTyping Γ Fin.elim0 As (toArgs args)) :
    ∃ e : 0 + As.length = args.length, ∀ i : Fin args.length,
      IsAtom args[i] ∧ HasType Γ args[i] (pushMany As Fin.elim0 (Fin.cast e.symm i)) := by
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
theorem ArgsTyping.instantiate {Γ As args body B} (hs : ArgsTyping Γ Fin.elim0 As (toArgs args))
    (hb : Typing Γ (pushMany As Fin.elim0) body B) (e : 0 + As.length = args.length) :
    HasType Γ (instantiate args (body.castScope e)) B := by
  obtain ⟨_, h⟩ := args_types hs
  exact (hb.castScope e).instantiate h

theorem BranchMember.typing {Γ b ms bs ps A} (h : BranchMember b (ms := ms) bs)
    (hs : BranchesTyping Γ Fin.elim0 ps bs A) : ∃ p, HasBranchType Γ p b A := by
  induction h generalizing ps with
  | here => cases hs with | cons hb _ => exact ⟨_, hb⟩
  | there _ ih => cases hs with | cons _ hs => exact ih hs

/-- The selected constructor branch returns its declared result type. -/
theorem MatchBranch.preservation {Γ v b result p A} (h : MatchBranch v b result)
    (hv : HasType Γ v .sexp) (hb : HasBranchType Γ p b A) : HasType Γ result A := by
  cases h with
  | int ha => cases hv with | sexp_int _ ht => cases hb with | int hbody => exact hbody.conc ha ht
  | bool ha => cases hv with | sexp_bool _ ht => cases hb with | bool hbody => exact hbody.conc ha ht
  | id ha => cases hv with | sexp_id _ ht => cases hb with | id hbody => exact hbody.conc ha ht
  | nil => cases hb with | nil ht => exact ht
  | pair ha hc =>
      cases hv with
      | pair _ _ hta htc => cases hb with | pair ht => exact (ht.conc ha hta).conc hc htc

/-- S-Preservation for all source §7 rules in the locally nameless representation. -/
theorem preservation {Γ t t' A} (ht : HasType Γ t A) (hs : Step t t') : HasType Γ t' A := by
  induction hs generalizing A with
  | search_let hs hb ih =>
      cases ht with
      | letE hr hbody => exact .letE (ih hr) hbody
  | beta arity hb hv hvs =>
      cases ht with
      | app _ _ hf ha has =>
          cases hf with
          | funE hbody => exact (ArgsTyping.cons (.value hv) ha has).instantiate hbody _
  | fix_beta arity hb hv hvs =>
      cases ht with
      | app _ _ hf ha has =>
          cases hf with
          | fixE hbody =>
              exact (ArgsTyping.cons (.value (.fixE _ _ _ hb)) (.fixE hbody)
                (.cons (.value hv) ha has)).instantiate hbody _
  | let_value hv hb =>
      cases ht with
      | letE hr hbody => exact hbody.conc (.value hv) hr
  | src_async _ => cases ht with | async hb => exact hb
  | match_constructor _ _ hm hc =>
      cases ht with
      | matchE _ hv hbs _ =>
          obtain ⟨_, hb⟩ := hm.typing hbs
          exact hc.preservation hv hb
  | match_wildcard _ _ _ _ _ hm =>
      cases ht with
      | matchE _ _ hbs _ =>
          obtain ⟨_, hb⟩ := hm.typing hbs
          cases hb with | wildcard hb => exact hb
  | add m n => cases ht; exact .integer (m + n)
  | sub m n => cases ht; exact .integer (m - n)
  | mul m n => cases ht; exact .integer (m * n)
  | eq_int_true _ => cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean true
  | eq_int_false _ => cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean false
  | eq_id_true _ => cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean true
  | eq_id_false _ => cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean false
  | lt_true _ => cases ht with
      | arith hop _ _ _ _ => simp at hop
      | lt _ _ _ _ => exact .boolean true
  | lt_false _ => cases ht with
      | arith hop _ _ _ _ => simp at hop
      | lt _ _ _ _ => exact .boolean false
  | if_true _ _ => cases ht with | ifE _ _ hy _ => exact hy
  | if_false _ _ => cases ht with | ifE _ _ _ hn => exact hn

theorem preservation_steps {Γ t t' A} (ht : HasType Γ t A) (hs : Steps t t') : HasType Γ t' A := by
  induction hs with
  | refl _ => exact ht
  | step h _ ih => exact ih (preservation ht h)

end SourceRuntime.Source

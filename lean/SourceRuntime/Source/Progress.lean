import SourceRuntime.Source.Typing

/-!
S-Progress and S-Safety for the source judgments in this representation.
Closed means typing under both empty contexts, not merely being a RawTerm 0.
The proof recurses on term size only for a let's RHS. The closed atoms inspected
by reduction rules are already values.
-/

namespace SourceRuntime.Source

open WSLN

private theorem closed_atom_value {a A} (ha : IsAtom a) (ht : HasType [] a A) :
    IsValue a := by
  cases ha with
  | bound i => exact Fin.elim0 i
  | free x => cases ht with | free h => simp at h
  | value hv => exact hv

private theorem canonical_int {a} (ha : IsAtom a) (ht : HasType [] a .int) :
    ∃ z, a = integer z := by
  have hv := closed_atom_value ha ht
  cases hv <;> cases ht
  exact ⟨_, rfl⟩

private theorem canonical_bool {a} (ha : IsAtom a) (ht : HasType [] a .bool) :
    ∃ b, a = boolean b := by
  have hv := closed_atom_value ha ht
  cases hv <;> cases ht
  exact ⟨_, rfl⟩

private theorem canonical_id {a} (ha : IsAtom a) (ht : HasType [] a .id) :
    ∃ i, a = identifier i := by
  have hv := closed_atom_value ha ht
  cases hv <;> cases ht
  exact ⟨_, rfl⟩

/-- The typed argument sequence has the required arity and consists of values. -/
private theorem arguments_values {k As} {args : RawArgs 0 k}
    (hs : ArgsTyping [] Fin.elim0 As args) :
    ∃ vs : List (RawTerm 0), ∃ e : vs.length = k,
      (e ▸ toArgs vs) = args ∧ vs.length = As.length ∧ ∀ v ∈ vs, IsValue v := by
  induction k generalizing As with
  | zero =>
      cases hs with
      | nil => exact ⟨[], rfl, rfl, rfl, by simp⟩
  | succ k ih =>
      cases hs with
      | cons ha ht hs =>
          obtain ⟨vs, e, he, arity, hv⟩ := ih hs
          cases e
          cases he
          refine ⟨_ :: vs, rfl, rfl, by simp [arity], ?_⟩
          intro v h
          rcases List.mem_cons.mp h with rfl | h
          · exact closed_atom_value ha ht
          · exact hv v h

private theorem application_step {k A As B fn first} {rest : RawArgs 0 k}
    (hf : IsAtom fn) (ha : IsAtom first) (htf : HasType [] fn (.arrow A As B))
    (hta : HasType [] first A) (hs : ArgsTyping [] Fin.elim0 As rest) :
    ∃ result, Step (app fn first rest) result := by
  obtain ⟨vs, e, he, arity, hv⟩ := arguments_values hs
  cases e
  cases he
  have hfn := closed_atom_value hf htf
  have harg := closed_atom_value ha hta
  cases hfn <;> cases htf
  case funE hb => exact ⟨_, .beta arity hb.formed harg hv⟩
  case fixE hb => exact ⟨_, .fix_beta arity hb.formed harg hv⟩

/-- A pattern recorded by IsBranches has an actual branch in the same sequence. -/
private theorem branch_member {ps ms p} {bs : Arg signature 0 ms}
    (hs : IsBranches ps bs) (hp : p ∈ ps) :
    ∃ b, BranchMember b bs ∧ IsBranch p b := by
  induction ps generalizing ms with
  | nil => simp at hp
  | cons q ps ih =>
      cases hs with
      | cons hb hs =>
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨_, .here, hb⟩
          · obtain ⟨b, hm, hb⟩ := ih hs hp
            exact ⟨b, .there hm, hb⟩

/-- A closed sexp has a constructor head and can instantiate a branch of that head. -/
private theorem canonical_sexp {v} (hv : IsValue v) (ht : HasType [] v .sexp) :
    ∃ p, constructorHead v = some p ∧
      ∀ body : RawTerm (0 + p.arity), ∃ result, MatchBranch v (branch p body) result := by
  cases hv <;> cases ht
  case sexp_int ha _ => exact ⟨.int, rfl, fun _ => ⟨_, .int ha⟩⟩
  case sexp_bool ha _ => exact ⟨.bool, rfl, fun _ => ⟨_, .bool ha⟩⟩
  case sexp_id ha _ => exact ⟨.id, rfl, fun _ => ⟨_, .id ha⟩⟩
  case nil => exact ⟨.nil, rfl, fun _ => ⟨_, .nil⟩⟩
  case pair => exact ⟨.pair, rfl, fun _ => ⟨_, .pair (by assumption) (by assumption)⟩⟩

private theorem match_step {k ps v} {bs : RawArgs 0 k}
    (ha : IsAtom v) (ht : HasType [] v .sexp) (hs : IsBranches ps bs)
    (hf : MatchPatterns ps) : ∃ result, Step (matchE v bs) result := by
  have hv := closed_atom_value ha ht
  obtain ⟨p, head, select⟩ := canonical_sexp hv ht
  by_cases hp : p ∈ ps
  · obtain ⟨b, hm, hb⟩ := branch_member hs hp
    cases hb with
    | branch _ =>
        obtain ⟨result, hc⟩ := select _
        exact ⟨result, .match_constructor hs hf hm hc⟩
  · obtain ⟨b, hm, hb⟩ := branch_member hs (List.mem_of_getLast? hf.2.2.1)
    cases hb with
    | branch _ => exact ⟨_, .match_wildcard hv head hp hs hf hm⟩

/-- S-Progress: a well-typed closed source term is a value or has a successor. -/
theorem progress {t A} (ht : HasType [] t A) :
    IsValue t ∨ ∃ t', Step t t' := by
  match ht with
  | .bound i => exact Fin.elim0 i
  | .free h => simp at h
  | .integer z => exact Or.inl (.integer z)
  | .boolean b => exact Or.inl (.boolean b)
  | .unit => exact Or.inl .unit
  | .identifier i => exact Or.inl (.identifier i)
  | .funE hb => exact Or.inl (.funE _ _ _ hb.formed)
  | .fixE hb => exact Or.inl (.fixE _ _ _ hb.formed)
  | .sexp_int ha _ => exact Or.inl (.sexp_int ha)
  | .sexp_bool ha _ => exact Or.inl (.sexp_bool ha)
  | .sexp_id ha _ => exact Or.inl (.sexp_id ha)
  | .nil => exact Or.inl .nil
  | .pair ha hb _ _ => exact Or.inl (.pair ha hb)
  | .app hf ha htf hta hs => exact Or.inr (application_step hf ha htf hta hs)
  | .arith hop ha hb hta htb =>
      obtain ⟨m, rfl⟩ := canonical_int ha hta
      obtain ⟨n, rfl⟩ := canonical_int hb htb
      rcases hop with rfl | rfl | rfl
      · exact Or.inr ⟨_, .add m n⟩
      · exact Or.inr ⟨_, .sub m n⟩
      · exact Or.inr ⟨_, .mul m n⟩
  | .eq hA ha hb hta htb =>
      rcases hA with rfl | rfl
      · obtain ⟨m, rfl⟩ := canonical_int ha hta
        obtain ⟨n, rfl⟩ := canonical_int hb htb
        by_cases h : m = n
        · exact Or.inr ⟨_, .eq_int_true h⟩
        · exact Or.inr ⟨_, .eq_int_false h⟩
      · obtain ⟨i, rfl⟩ := canonical_id ha hta
        obtain ⟨j, rfl⟩ := canonical_id hb htb
        by_cases h : i = j
        · exact Or.inr ⟨_, .eq_id_true h⟩
        · exact Or.inr ⟨_, .eq_id_false h⟩
  | .lt ha hb hta htb =>
      obtain ⟨m, rfl⟩ := canonical_int ha hta
      obtain ⟨n, rfl⟩ := canonical_int hb htb
      by_cases h : m < n
      · exact Or.inr ⟨_, .lt_true h⟩
      · exact Or.inr ⟨_, .lt_false h⟩
  | .ifE hg htg hy hn =>
      obtain ⟨b, rfl⟩ := canonical_bool hg htg
      cases b with
      | false => exact Or.inr ⟨_, .if_false hy.formed hn.formed⟩
      | true => exact Or.inr ⟨_, .if_true hy.formed hn.formed⟩
  | .letE hr hb =>
      rcases progress hr with hv | ⟨rhs', hs⟩
      · exact Or.inr ⟨_, .let_value hv hb.formed⟩
      · exact Or.inr ⟨_, .search_let hs hb.formed⟩
  | .matchE ha hta hs hf => exact Or.inr (match_step ha hta hs.formed hf)
  | .async hb => exact Or.inr ⟨_, .src_async hb.formed⟩
termination_by sizeOf t
decreasing_by
  simp [letE, sizeOf, Trm._sizeOf_1]
  omega

/-- S-Safety: every reachable term keeps its type, and a terminal one is a value. -/
theorem safety {t t' A} (ht : HasType [] t A) (hs : Steps t t') :
    HasType [] t' A ∧ ((¬ ∃ u, Step t' u) → IsValue t') := by
  have ht' := preservation_steps ht hs
  refine ⟨ht', ?_⟩
  intro terminal
  rcases progress ht' with hv | ⟨u, hu⟩
  · exact hv
  · exact False.elim (terminal ⟨u, hu⟩)

end SourceRuntime.Source

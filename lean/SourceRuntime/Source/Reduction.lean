import SourceRuntime.Source.Binding

/-!
Source-calculus.md §7: all eighteen sequential rule schemas.
MatchBranch expands the five constructor instances of Match-Constructor.
BranchMember selects an existing branch; MatchPatterns supplies the distinct-head
and final-wildcard conditions. The only search rule is Search-Let.
-/

namespace SourceRuntime.Source

open WSLN Adequacy

/-- Select an occurrence in the displayed branch sequence. -/
inductive BranchMember (b : RawTerm 0) : {ms : List Nat} → Arg signature 0 ms → Prop where
  | here {ms rest} : BranchMember b (.cons (ms := ms) (m := 0) b rest)
  | there {ms head rest} : BranchMember b (ms := ms) rest →
      BranchMember b (.cons (m := 0) head rest)

/-- Constructor heads are fixed syntax; literals and function values have none. -/
def constructorHead {n} : RawTerm n → Option Pattern
  | .op .sexp_int _ => some .int
  | .op .sexp_bool _ => some .bool
  | .op .sexp_id _ => some .id
  | .op .nil _ => some .nil
  | .op .pair _ => some .pair
  | _ => none

/-- Instantiate the fields of K in the selected K branch. Fields need only be atoms. -/
inductive MatchBranch : RawTerm 0 → RawTerm 0 → RawTerm 0 → Prop where
  | int {a body} : IsAtom a → MatchBranch (sexp_int a) (branch .int body) (body.conc a)
  | bool {a body} : IsAtom a → MatchBranch (sexp_bool a) (branch .bool body) (body.conc a)
  | id {a body} : IsAtom a → MatchBranch (sexp_id a) (branch .id body) (body.conc a)
  | nil {body} : MatchBranch nil (branch .nil body) body
  | pair {a b body} : IsAtom a → IsAtom b →
      MatchBranch (pair a b) (branch .pair body) ((body.conc a).conc b)

/-- Formation premises restrict raw trees to the grammar, independently of typing. -/
inductive Step : RawTerm 0 → RawTerm 0 → Prop where
  | search_let {rhs rhs' : RawTerm 0} {body : RawTerm 1} :
      Step rhs rhs' → IsTerm body → Step (letE rhs body) (letE rhs' body)
  | beta {A As B} {body : RawTerm (0 + (As.length + 1))} {v vs} (arity : vs.length = As.length) :
      IsTerm body → IsValue v → (∀ a ∈ vs, IsValue a) →
      Step (app (funE A As B body) v (toArgs vs))
        (instantiate (v :: vs) (body.castScope (by simp [arity])))
  | fix_beta {A As B} {body : RawTerm (0 + (As.length + 2))} {v vs} (arity : vs.length = As.length) :
      IsTerm body → IsValue v → (∀ a ∈ vs, IsValue a) →
      Step (app (fixE A As B body) v (toArgs vs))
        (instantiate (fixE A As B body :: v :: vs) (body.castScope (by simp [arity])))
  | let_value {v : RawTerm 0} {body : RawTerm 1} :
      IsValue v → IsTerm body → Step (letE v body) (body.conc v)
  | src_async {body} : IsTerm body → Step (async body) body
  | match_constructor {k ps scrutinee b result} {bs : RawArgs 0 k} :
      IsBranches ps bs → MatchPatterns ps → BranchMember b bs →
      MatchBranch scrutinee b result → Step (matchE scrutinee bs) result
  | match_wildcard {k ps p scrutinee body} {bs : RawArgs 0 k} :
      IsValue scrutinee → constructorHead scrutinee = some p → p ∉ ps →
      IsBranches ps bs → MatchPatterns ps → BranchMember (branch .wildcard body) bs →
      Step (matchE scrutinee bs) body
  | add (m n : Int) : Step (add (integer m) (integer n)) (integer (m + n))
  | sub (m n : Int) : Step (operation .sub (integer m) (integer n)) (integer (m - n))
  | mul (m n : Int) : Step (operation .mul (integer m) (integer n)) (integer (m * n))
  | eq_int_true {m n : Int} : m = n → Step (operation .eq (integer m) (integer n)) (boolean true)
  | eq_int_false {m n : Int} : m ≠ n → Step (operation .eq (integer m) (integer n)) (boolean false)
  | eq_id_true {i j : Id} : i = j → Step (operation .eq (identifier i) (identifier j)) (boolean true)
  | eq_id_false {i j : Id} : i ≠ j → Step (operation .eq (identifier i) (identifier j)) (boolean false)
  | lt_true {m n : Int} : m < n → Step (operation .lt (integer m) (integer n)) (boolean true)
  | lt_false {m n : Int} : ¬ m < n → Step (operation .lt (integer m) (integer n)) (boolean false)
  | if_true {yes no} : IsTerm yes → IsTerm no → Step (ifE (boolean true) yes no) yes
  | if_false {yes no} : IsTerm yes → IsTerm no → Step (ifE (boolean false) yes no) no

/-- The reflexive-transitive closure from the end of source §7. -/
inductive Steps : RawTerm 0 → RawTerm 0 → Prop where
  | refl {t} : IsTerm t → Steps t t
  | step {t u v} : Step t u → Steps u v → Steps t v

/-- WSLN's opening of a closed binder is capture-avoiding substitution. -/
theorem let_step (x : WSLN.Atom) {v body : RawTerm 0}
    (hv : IsValue v) (hb : IsTerm body) :
    Step (let_ x v body) ((x ≔ v) * body) := by
  rw [← concAbs x body v]
  exact Step.let_value hv (hb.close x ⟨0, by omega⟩ rfl)

/-- The displayed beta rule uses a single simultaneous substitution on the named body. -/
theorem beta_named (first : WSLN.Atom × Ty) (rest : List (WSLN.Atom × Ty))
    (B : Ty) (body : RawTerm 0) (σ : Sb signature)
    (distinct : (first.1 :: rest.map Prod.fst).Nodup) (hb : IsTerm body)
    (hv : ∀ x ∈ first.1 :: rest.map Prod.fst, IsValue (σ x))
    (outside : ∀ x, x ∉ first.1 :: rest.map Prod.fst → σ x = var x) :
    Step (app (fun_ first rest B body distinct) (σ first.1) (toArgs ((rest.map Prod.fst).map σ)))
      (σ * body) := by
  let names := first.1 :: rest.map Prod.fst
  let vs := (rest.map Prod.fst).map σ
  have e : names.length = 0 + ((rest.map Prod.snd).length + 1) := by simp [names]
  have f : 0 + ((rest.map Prod.snd).length + 1) = (σ first.1 :: vs).length := by simp [vs]
  have hs := Step.beta (A := first.2) (B := B) (by simp [vs] : vs.length = (rest.map Prod.snd).length)
    ((hb.closeMany names).castScope e) (hv first.1 (by simp)) (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact hv x (by simp [hx]))
  have he := congrArg (instantiate (σ first.1 :: vs)) (castScope_trans e f (closeMany names body))
  rw [he, instantiate_closeMany names body σ outside (by rfl)] at hs
  exact hs

/-- Fix-beta supplies self and the parameters together; self is not substituted afterwards. -/
theorem fix_beta_named (self : WSLN.Atom) (first : WSLN.Atom × Ty)
    (rest : List (WSLN.Atom × Ty)) (B : Ty) (body : RawTerm 0) (σ : Sb signature)
    (distinct : (self :: first.1 :: rest.map Prod.fst).Nodup) (hb : IsTerm body)
    (hself : σ self = fix_ self first rest B body distinct)
    (hv : ∀ x ∈ first.1 :: rest.map Prod.fst, IsValue (σ x))
    (outside : ∀ x, x ∉ self :: first.1 :: rest.map Prod.fst → σ x = var x) :
    Step (app (fix_ self first rest B body distinct) (σ first.1) (toArgs ((rest.map Prod.fst).map σ)))
      (σ * body) := by
  let names := self :: first.1 :: rest.map Prod.fst
  let vs := (rest.map Prod.fst).map σ
  let recursive := fix_ self first rest B body distinct
  have e : names.length = 0 + ((rest.map Prod.snd).length + 2) := by simp [names]
  have f : 0 + ((rest.map Prod.snd).length + 2) = (recursive :: σ first.1 :: vs).length := by simp [vs]
  have hs := Step.fix_beta (A := first.2) (B := B)
    (by simp [vs] : vs.length = (rest.map Prod.snd).length)
    ((hb.closeMany names).castScope e) (hv first.1 (by simp)) (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact hv x (by simp [hx]))
  change Step (app recursive (σ first.1) (toArgs vs))
    (instantiate (recursive :: σ first.1 :: vs) (((closeMany names body).castScope e).castScope f)) at hs
  have he := congrArg (instantiate (recursive :: σ first.1 :: vs))
    (castScope_trans e f (closeMany names body))
  rw [he, instantiate_closeMany names body σ outside (by simp [names, vs, hself, recursive])] at hs
  exact hs

theorem BranchMember.formed {b ms bs ps} (h : BranchMember b (ms := ms) bs)
    (hs : IsBranches ps bs) : ∃ p, IsBranch p b := by
  induction h generalizing ps with
  | here => cases hs with | cons hb _ => exact ⟨_, hb⟩
  | there _ ih => cases hs with | cons _ hs => exact ih hs

theorem MatchBranch.formed {v b result} (h : MatchBranch v b result)
    {p} (hbranch : IsBranch p b) : IsValue v ∧ IsTerm result := by
  cases h with
  | int ha => cases hbranch with | branch ht => exact ⟨.sexp_int ha, ht.conc ha⟩
  | bool ha => cases hbranch with | branch ht => exact ⟨.sexp_bool ha, ht.conc ha⟩
  | id ha => cases hbranch with | branch ht => exact ⟨.sexp_id ha, ht.conc ha⟩
  | nil => cases hbranch with | branch ht => exact ⟨.nil, ht⟩
  | pair ha hb =>
      cases hbranch with
      | branch ht => exact ⟨.pair ha hb, (ht.open ⟨0, by decide⟩ ha rfl).conc hb⟩

/-- Both ends of every source step satisfy the source grammar. -/
theorem Step.formed {t t' : RawTerm 0} (h : Step t t') : IsTerm t ∧ IsTerm t' := by
  induction h with
  | search_let _ hb ih => exact ⟨.letE ih.1 hb, .letE ih.2 hb⟩
  | beta arity hb hv hs =>
      exact ⟨.app (.value (.funE _ _ _ hb)) (.value hv)
        (.toArgs (fun a h => .value (hs a h))),
        (hb.castScope _).instantiate _ (by
          intro a h; cases h with
          | head => exact .value hv
          | tail _ h => exact .value (hs a h))⟩
  | fix_beta arity hb hv hs =>
      exact ⟨.app (.value (.fixE _ _ _ hb)) (.value hv)
        (.toArgs (fun a h => .value (hs a h))),
        (hb.castScope _).instantiate _ (by
          intro a h; cases h with
          | head => exact .value (.fixE _ _ _ hb)
          | tail _ h => cases h with
            | head => exact .value hv
            | tail _ h => exact .value (hs a h))⟩
  | let_value hv hb => exact ⟨.letE (.atom (.value hv)) hb, hb.conc (.value hv)⟩
  | src_async hb => exact ⟨.async hb, hb⟩
  | match_constructor hs hf hm hc =>
      obtain ⟨_, hb⟩ := hm.formed hs
      have hv := hc.formed hb
      exact ⟨.matchE (.value hv.1) hs hf, hv.2⟩
  | match_wildcard hv _ _ hs hf hm =>
      obtain ⟨_, hb⟩ := hm.formed hs
      cases hb with | branch ht => exact ⟨.matchE (.value hv) hs hf, ht⟩
  | add m n => exact ⟨.add (.value (.integer m)) (.value (.integer n)), .atom (.value (.integer _))⟩
  | sub m n => exact ⟨.operation _ (.value (.integer m)) (.value (.integer n)), .atom (.value (.integer _))⟩
  | mul m n => exact ⟨.operation _ (.value (.integer m)) (.value (.integer n)), .atom (.value (.integer _))⟩
  | eq_int_true _ => exact ⟨.operation _ (.value (.integer _)) (.value (.integer _)), .atom (.value (.boolean _))⟩
  | eq_int_false _ => exact ⟨.operation _ (.value (.integer _)) (.value (.integer _)), .atom (.value (.boolean _))⟩
  | eq_id_true _ => exact ⟨.operation _ (.value (.identifier _)) (.value (.identifier _)), .atom (.value (.boolean _))⟩
  | eq_id_false _ => exact ⟨.operation _ (.value (.identifier _)) (.value (.identifier _)), .atom (.value (.boolean _))⟩
  | lt_true _ => exact ⟨.operation _ (.value (.integer _)) (.value (.integer _)), .atom (.value (.boolean _))⟩
  | lt_false _ => exact ⟨.operation _ (.value (.integer _)) (.value (.integer _)), .atom (.value (.boolean _))⟩
  | if_true hy hn => exact ⟨.ifE (.value (.boolean true)) hy hn, hy⟩
  | if_false hy hn => exact ⟨.ifE (.value (.boolean false)) hy hn, hn⟩

theorem value_irreducible {v t : RawTerm 0} (hv : IsValue v) : ¬ Step v t := by
  intro h
  cases hv <;> cases h

/-- The existing sequential closure with its number of steps exposed for induction. -/
inductive StepsN : Nat → RawTerm 0 → RawTerm 0 → Prop where
  | refl {t} : IsTerm t → StepsN 0 t t
  | step {k t u v} : Step t u → StepsN k u v → StepsN (k + 1) t v

theorem Steps.exists_length {t v} (h : Steps t v) : ∃ k, StepsN k t v := by
  induction h with
  | refl ht => exact ⟨0, .refl ht⟩
  | step hs _ ih => obtain ⟨k, hk⟩ := ih; exact ⟨k + 1, .step hs hk⟩

/-- A let-to-value path evaluates its RHS, takes Let once, then evaluates the body.
    Both component paths are strictly shorter than the original path. -/
theorem StepsN.let_inv {k rhs body v} (h : StepsN k (letE rhs body) v) (hv : IsValue v) :
    ∃ w i j, IsValue w ∧ StepsN i rhs w ∧ StepsN j (body.conc w) v ∧ k = i + 1 + j := by
  generalize he : letE rhs body = start at h
  induction h generalizing rhs body with
  | refl ht => rw [← he] at hv; cases hv
  | @step k start mid v hs rest ih =>
      subst start
      cases hs with
      | search_let hr hb =>
          obtain ⟨w, i, j, hw, h₁, h₂, hk⟩ := ih hv rfl
          exact ⟨w, i + 1, j, hw, .step hr h₁, h₂, by omega⟩
      | let_value hw hb =>
          exact ⟨_, 0, k, hw, .refl (.atom (.value hw)), rest, by omega⟩

/-- Async contributes exactly the first source step; its operand follows in the tail. -/
theorem StepsN.async_inv {k body v} (h : StepsN k (async body) v) (hv : IsValue v) :
    ∃ j, k = j + 1 ∧ StepsN j body v := by
  cases h with
  | refl => cases hv
  | step hs rest => cases hs with | src_async _ => exact ⟨_, rfl, rest⟩

/-- Concatenate finite sequential evaluations. -/
theorem Steps.trans {t u v} (h : Steps t u) (h' : Steps u v) : Steps t v := by
  induction h with
  | refl => exact h'
  | step hs _ ih => exact .step hs (ih h')

/-- Repeated Search-Let retains the same body throughout the RHS evaluation. -/
theorem Steps.search_let {rhs rhs' body} (h : Steps rhs rhs') (hb : IsTerm body) :
    Steps (letE rhs body) (letE rhs' body) := by
  induction h with
  | refl ht => exact .refl (.letE ht hb)
  | step hs _ ih => exact .step (.search_let hs hb) ih

private theorem BranchMember.pattern {b ms bs ps p}
    (h : BranchMember b (ms := ms) bs) (hs : IsBranches ps bs) (hb : IsBranch p b) : p ∈ ps := by
  induction h generalizing ps with
  | here => cases hs with | cons hb' _ => cases hb; cases hb'; exact List.mem_cons_self
  | there _ ih => cases hs with | cons _ hs => exact List.mem_cons_of_mem _ (ih hs)

private theorem BranchMember.unique {b ms bs ps p b'}
    (h : BranchMember b (ms := ms) bs) (hs : IsBranches ps bs) (hd : ps.Nodup)
    (hb : IsBranch p b) (h' : BranchMember b' bs) (hb' : IsBranch p b') : b = b' := by
  induction h generalizing ps b' with
  | here =>
      cases hs with
      | cons head tail =>
          cases head
          cases hb
          cases h' with
          | here => rfl
          | there member => exact False.elim ((List.nodup_cons.mp hd).1 (member.pattern tail hb'))
  | there member ih =>
      cases hs with
      | cons head tail =>
          cases h' with
          | here =>
              cases head
              cases hb'
              exact False.elim ((List.nodup_cons.mp hd).1 (member.pattern tail hb))
          | there member' => exact ih tail (List.nodup_cons.mp hd).2 member' hb'

private theorem MatchBranch.head {v b r p} (h : MatchBranch v b r) (hb : IsBranch p b) :
    constructorHead v = some p := by
  cases h <;> cases hb <;> rfl

private theorem MatchBranch.unique {v b r r'} (h : MatchBranch v b r) (h' : MatchBranch v b r') :
    r = r' := by
  cases h <;> cases h' <;> rfl

-- Decode only the zero-binder argument spine, to compare applications even
-- when their operand counts were introduced by different rule derivations.
private def operands : {k : Nat} → RawArgs 0 k → List (RawTerm 0)
  | 0, .nil => []
  | _ + 1, .cons a rest => a :: operands rest

private theorem operands_toArgs (as : List (RawTerm 0)) : operands (toArgs as) = as := by
  induction as with
  | nil => rfl
  | cons a rest ih => exact congrArg (a :: ·) ih

private def appOperands : RawTerm 0 → List (RawTerm 0)
  | .op o args => match o with
    | .app k => operands (k := k + 2) args
    | _ => []
  | _ => []

/-- Equal applications have the same ordered operands, including their argument counts. -/
theorem app_inj {f g a b : RawTerm 0} {as bs : List (RawTerm 0)}
    (h : app f a (toArgs as) = app g b (toArgs bs)) : f = g ∧ a = b ∧ as = bs := by
  have e := congrArg appOperands h
  change f :: a :: operands (toArgs as) = g :: b :: operands (toArgs bs) at e
  simpa only [operands_toArgs, List.cons.injEq] using e

/-- S-Determinacy: a source step has one target, without a typing or closedness premise. -/
theorem Step.deterministic {t u v} (h : Step t u) (h' : Step t v) : u = v := by
  induction h generalizing v with
  | search_let step hb ih =>
      cases h' with
      | search_let step' _ => rw [ih step']
      | let_value hv _ => exact False.elim (value_irreducible hv step)
  | let_value hv hb =>
      cases h' with
      | search_let step _ => exact False.elim (value_irreducible hv step)
      | let_value => rfl
  | beta arity hb hv hs =>
      generalize he : app _ _ (toArgs _) = start at h'
      cases h' with
      | beta =>
          obtain ⟨hf, rfl, rfl⟩ := app_inj he
          cases hf
          rfl
      | fix_beta => obtain ⟨hf, _⟩ := app_inj he; cases hf
      | _ => cases he
  | fix_beta arity hb hv hs =>
      generalize he : app _ _ (toArgs _) = start at h'
      cases h' with
      | fix_beta =>
          obtain ⟨hf, rfl, rfl⟩ := app_inj he
          cases hf
          rfl
      | beta => obtain ⟨hf, _⟩ := app_inj he; cases hf
      | _ => cases he
  | match_constructor hs hp member matched =>
      cases h' with
      | match_constructor hs' hp' member' matched' =>
          obtain ⟨p, hb⟩ := member.formed hs
          obtain ⟨q, hb'⟩ := member'.formed hs
          have eqn := Option.some.inj ((matched.head hb).symm.trans (matched'.head hb'))
          subst q
          have eqb := member.unique hs hp.2.2.2 hb member' hb'
          subst eqb
          exact matched.unique matched'
      | match_wildcard hv head absent hs' hp' member' =>
          obtain ⟨p, hb⟩ := member.formed hs'
          have eqn := Option.some.inj ((matched.head hb).symm.trans head)
          subst p
          exact False.elim (absent (member.pattern hs' hb))
  | match_wildcard hv head absent hs hp member =>
      cases h' with
      | match_constructor hs' hp' member' matched' =>
          obtain ⟨p, hb⟩ := member'.formed hs
          have eqn := Option.some.inj ((matched'.head hb).symm.trans head)
          subst p
          exact False.elim (absent (member'.pattern hs hb))
      | match_wildcard hv' head' absent' hs' hp' member' =>
          obtain ⟨_, hb⟩ := member.formed hs
          obtain ⟨_, hb'⟩ := member'.formed hs
          cases hb
          cases hb'
          have eqn := member.unique hs hp.2.2.2 (.branch (by assumption)) member' (.branch (by assumption))
          cases eqn
          rfl
  | src_async => cases h'; rfl
  | add | sub | mul | eq_int_true | eq_int_false | eq_id_true | eq_id_false | lt_true | lt_false
  | if_true | if_false => cases h' <;> first | rfl | contradiction

/-- Two finite source evaluations to values have the same result. -/
theorem Steps.value_unique {t v w} (h : Steps t v) (hv : IsValue v)
    (h' : Steps t w) (hw : IsValue w) : v = w := by
  induction h generalizing w with
  | refl =>
      cases h' with
      | refl => rfl
      | step step _ => exact False.elim (value_irreducible hv step)
  | step step rest ih =>
      cases h' with
      | refl => exact False.elim (value_irreducible hw step)
      | step step' rest' =>
          cases step.deterministic step'
          exact ih hv rest' hw

end SourceRuntime.Source

import SourceRuntime.Runtime.Typing

/-!
Runtime §§6–7. LocalStep records a rule derivation by its six display components;
State.LocalStep restricts its endpoints to the formed State carrier.
Step interleaves either that focus step or one selected mapping entry.
ArgMember only encodes membership in WSLN's operand spine (branches or arguments).
-/

namespace SourceRuntime.Runtime
open WSLN
open Source (Ty Id Prim Pattern MatchPatterns)

inductive ArgMember (a : RawTerm 0) : {ms : List Nat} → Arg signature 0 ms → Prop where
  | here {ms rest} : ArgMember a (.cons (ms := ms) (m := 0) a rest)
  | there {ms head rest} : ArgMember a (ms := ms) rest → ArgMember a (.cons (m := 0) head rest)

def constructorHead {n} : RawTerm n → Option Pattern
  | .op (.source .sexp_int) _ => some .int
  | .op (.source .sexp_bool) _ => some .bool
  | .op (.source .sexp_id) _ => some .id
  | .op (.source .nil) _ => some .nil
  | .op (.source .pair) _ => some .pair
  | _ => none

inductive MatchBranch (U : ActiveNames) : RawTerm 0 → RawTerm 0 → RawTerm 0 → Prop where
  | int {a body} : IsAtom U a → MatchBranch U (sexp_int a) (branch .int body) (body.conc a)
  | bool {a body} : IsAtom U a → MatchBranch U (sexp_bool a) (branch .bool body) (body.conc a)
  | id {a body} : IsAtom U a → MatchBranch U (sexp_id a) (branch .id body) (body.conc a)
  | nil {body} : MatchBranch U nil (branch .nil body) body
  | pair {a b body} : IsAtom U a → IsAtom U b →
      MatchBranch U (pair a b) (branch .pair body) ((body.conc a).conc b)

inductive LocalStep (sig : Signature) (mu : Mapping) :
    RawTerm 0 → Signature → Mapping → RawTerm 0 → Prop where
  | search_let {rhs rhs' : RawTerm 0} {body : RawTerm 1} {sig' mu'} :
      (¬ ∃ (k : Nat) (fn first : RawTerm 0) (rest : RawArgs 0 k) (p : FName) (mapped : RawTerm 0),
        rhs = app fn first rest ∧
        (fn = future p ∨ first = future p ∨ ArgMember (future p) rest) ∧
        mu[p]? = some mapped ∧ ¬ IsValue (domain sig) mapped) →
      LocalStep sig mu rhs sig' mu' rhs' → IsTerm (domain sig) body →
      LocalStep sig mu (letE rhs body) sig' mu' (letE rhs' body)
  | beta {A As B} {body : RawTerm (0 + (As.length + 1))} {v vs}
      (arity : vs.length = As.length) :
      IsTerm (domain sig) body → IsValue (domain sig) v → (∀ a ∈ vs, IsValue (domain sig) a) →
      LocalStep sig mu (app (funE A As B body) v (toArgs vs)) sig mu
        (instantiate (v :: vs) (body.castScope (by simp [arity])))
  | fix_beta {A As B} {body : RawTerm (0 + (As.length + 2))} {v vs}
      (arity : vs.length = As.length) :
      IsTerm (domain sig) body → IsValue (domain sig) v → (∀ a ∈ vs, IsValue (domain sig) a) →
      LocalStep sig mu (app (fixE A As B body) v (toArgs vs)) sig mu
        (instantiate (fixE A As B body :: v :: vs) (body.castScope (by simp [arity])))
  | let_value {v : RawTerm 0} {body : RawTerm 1} :
      IsValue (domain sig) v → IsTerm (domain sig) body →
      LocalStep sig mu (letE v body) sig mu (body.conc v)
  | match_constructor {k ps scrutinee b result} {bs : RawArgs 0 k} :
      IsBranches (domain sig) ps bs → MatchPatterns ps → ArgMember b bs →
      MatchBranch (domain sig) scrutinee b result → LocalStep sig mu (matchE scrutinee bs) sig mu result
  | match_wildcard {k ps p scrutinee body} {bs : RawArgs 0 k} :
      IsValue (domain sig) scrutinee → constructorHead scrutinee = some p → p ∉ ps →
      IsBranches (domain sig) ps bs → MatchPatterns ps → ArgMember (branch .wildcard body) bs →
      LocalStep sig mu (matchE scrutinee bs) sig mu body
  | add (m n : Int) : LocalStep sig mu (operation .add (integer m) (integer n)) sig mu (integer (m + n))
  | sub (m n : Int) : LocalStep sig mu (operation .sub (integer m) (integer n)) sig mu (integer (m - n))
  | mul (m n : Int) : LocalStep sig mu (operation .mul (integer m) (integer n)) sig mu (integer (m * n))
  | eq_int_true {m n : Int} : m = n → LocalStep sig mu (operation .eq (integer m) (integer n)) sig mu (boolean true)
  | eq_int_false {m n : Int} : m ≠ n → LocalStep sig mu (operation .eq (integer m) (integer n)) sig mu (boolean false)
  | eq_id_true {i j : Id} : i = j → LocalStep sig mu (operation .eq (identifier i) (identifier j)) sig mu (boolean true)
  | eq_id_false {i j : Id} : i ≠ j → LocalStep sig mu (operation .eq (identifier i) (identifier j)) sig mu (boolean false)
  | lt_true {m n : Int} : m < n → LocalStep sig mu (operation .lt (integer m) (integer n)) sig mu (boolean true)
  | lt_false {m n : Int} : ¬ m < n → LocalStep sig mu (operation .lt (integer m) (integer n)) sig mu (boolean false)
  | if_true {yes no} : IsTerm (domain sig) yes → IsTerm (domain sig) no →
      LocalStep sig mu (ifE (boolean true) yes no) sig mu yes
  | if_false {yes no} : IsTerm (domain sig) yes → IsTerm (domain sig) no →
      LocalStep sig mu (ifE (boolean false) yes no) sig mu no
  | spawn_async {body A q} : HasType sig [] body A → q ∉ domain sig →
      LocalStep sig mu (async body) (sig.insert q A) (mu.insert q body) (future q)
  | deref_app {k w first} {p : FName} {rest : RawArgs 0 k} :
      mu[p]? = some w → IsValue (domain sig) w →
      LocalStep sig mu (app (future p) first rest) sig mu (app w first rest)
  | deref_op_left {w op b} {p : FName} : mu[p]? = some w → IsValue (domain sig) w →
      LocalStep sig mu (operation op (future p) b) sig mu (operation op w b)
  | deref_op_right {w op b} {p : FName} : mu[p]? = some w → IsValue (domain sig) w →
      LocalStep sig mu (operation op b (future p)) sig mu (operation op b w)
  | deref_if {w yes no} {p : FName} : mu[p]? = some w → IsValue (domain sig) w →
      LocalStep sig mu (ifE (future p) yes no) sig mu (ifE w yes no)
  | deref_match {k w} {p : FName} {bs : RawArgs 0 k} : mu[p]? = some w → IsValue (domain sig) w →
      LocalStep sig mu (matchE (future p) bs) sig mu (matchE w bs)
  | spawn_app {k fn first} {rest : RawArgs 0 k} {body : RawTerm 1} {A q} :
      (∃ (p : FName) (mapped : RawTerm 0),
        (fn = future p ∨ first = future p ∨ ArgMember (future p) rest) ∧
        mu[p]? = some mapped ∧ ¬ IsValue (domain sig) mapped) →
      HasType sig [] (app fn first rest) A → q ∉ domain sig → IsTerm (domain sig) body →
      LocalStep sig mu (letE (app fn first rest) body) (sig.insert q A)
        (mu.insert q (app fn first rest)) (letE (future q) body)

abbrev State.LocalStep (s t : State) :=
  Runtime.LocalStep s.signature s.mapping s.focus t.signature t.mapping t.focus

/-- Select another formed term under the same signature and mapping. -/
def State.withFocus (s : State) (t : RawTerm 0) (ht : IsTerm (domain s.signature) t) : State :=
  { s with focus := t, focus_formed := ht }

inductive Step : State → State → Prop where
  | focus {s t} : s.LocalStep t → Step s t
  | future {s t u : State} {p : FName} {body : RawTerm 0}
      (hp : s.mapping[p]? = some body) :
      (s.withFocus body (s.entries_formed p body hp)).LocalStep t →
      u.signature = t.signature → u.focus = s.focus → u.mapping = t.mapping.insert p t.focus →
      Step s u

inductive Steps : State → State → Prop where
  | refl {s} : Steps s s
  | step {s t u} : Step s t → Steps t u → Steps s u

/-- A local rule changes neither map or extends both at the same fresh name. -/
theorem LocalStep.extension {sig mu t sig' mu' t'} (h : LocalStep sig mu t sig' mu' t') :
    (sig' = sig ∧ mu' = mu) ∨
    ∃ q A body, q ∉ domain sig ∧ sig' = sig.insert q A ∧ mu' = mu.insert q body ∧
      IsTerm (domain sig) body := by
  induction h with
  | search_let _ _ _ ih => exact ih
  | spawn_async ht hf => exact .inr ⟨_, _, _, hf, rfl, rfl, ht.formed⟩
  | spawn_app _ ht hf _ => exact .inr ⟨_, _, _, hf, rfl, rfl, ht.formed⟩
  | _ => exact .inl ⟨rfl, rfl⟩

theorem LocalStep.sigma_extends {sig mu t sig' mu' t'} (h : LocalStep sig mu t sig' mu' t') :
    sig.Extends sig' := by
  rcases h.extension with ⟨rfl, _⟩ | ⟨q, A, _, hf, rfl, _⟩
  · exact fun _ _ hp => hp
  · exact Signature.extends_insert A hf

theorem value_irreducible {sig mu v sig' mu' t} (hv : IsValue (domain sig) v) :
    ¬ LocalStep sig mu v sig' mu' t := by
  intro h
  cases hv <;> cases h

/-- R-Final-Irreducible uses finality alone, independently of State-Ok. -/
theorem State.Final.irreducible {s t : State} (hs : s.Final) : ¬ Step s t := by
  intro h
  cases h with
  | focus h => exact value_irreducible hs.focus h
  | future hp h _ _ _ => exact value_irreducible (hs.entries _ _ hp) h

end SourceRuntime.Runtime

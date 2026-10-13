import Adequacy

/-!
Source-calculus.md, §§2--5: types, syntax and binding formation.
WSLN supplies binding trees and substitution; the predicates below restrict those
trees to our value, atom, and term productions. They do not express source typing.
-/

namespace SourceRuntime.Source

open WSLN

inductive Ty where
  | int | bool | unit | id | sexp
  /-- The first parameter makes the argument sequence nonempty (§2). -/
  | arrow (first : Ty) (rest : List Ty) (result : Ty)

/-- As in OCaml Common_syntax.Id, identifier literals are strings, not variables. -/
abbrev Id := String

inductive Prim where
  | add | sub | mul | eq | lt

/-- Pattern shapes, as in OCaml Syntax.pattern; names live in the branch binder. -/
inductive Pattern where
  | int | bool | id | nil | pair | wildcard
  deriving DecidableEq

def Pattern.arity : Pattern → Nat
  | .int | .bool | .id => 1
  | .nil | .wildcard => 0
  | .pair => 2

/-- Source §3.2: one to five constructor branches, then exactly one wildcard.
    Nodup makes every earlier pattern a distinct constructor head. -/
def MatchPatterns (ps : List Pattern) : Prop :=
  2 ≤ ps.length ∧ ps.length ≤ 6 ∧ ps.getLast? = some .wildcard ∧ ps.Nodup

inductive Op where
  | integer : Int → Op
  | boolean : Bool → Op
  | unit
  | identifier : Id → Op
  | funE (first : Ty) (rest : List Ty) (result : Ty)
  | fixE (first : Ty) (rest : List Ty) (result : Ty)
  | sexp_int | sexp_bool | sexp_id
  | nil
  | pair
  | operation : Prim → Op
  | app (restCount : Nat)
  | ifE
  | letE
  | branch (pattern : Pattern)
  | matchE (branchCount : Nat)
  | async

def signature : Sig where
  Op := Op
  ar
    | .integer _ | .boolean _ | .unit | .identifier _ | .nil => []
    | .sexp_int | .sexp_bool | .sexp_id | .async => [0]
    | .pair | .operation _ => [0, 0]
    | .ifE => [0, 0, 0]
    | .letE => [0, 1]
    | .funE _ rest _ => [rest.length + 1]
    | .fixE _ rest _ => [rest.length + 2]
    | .app k => List.replicate (k + 2) 0
    | .branch p => [p.arity]
    | .matchE k => 0 :: List.replicate k 0

/-- The index counts enclosing binders. Raw trees may violate our grammar. -/
abbrev RawTerm (n : Nat) := Trm signature n
abbrev NamedTerm := Adequacy.NomTrm signature

/-- A sequence of nonbinding operands, using WSLN's argument representation. -/
abbrev RawArgs (n k : Nat) := Arg signature n (List.replicate k 0)

def var {n : Nat} (x : WSLN.Atom) : RawTerm n := .atom x
def integer {n : Nat} (z : Int) : RawTerm n := .op (.integer z) .nil
def boolean {n : Nat} (b : Bool) : RawTerm n := .op (.boolean b) .nil
def unit {n : Nat} : RawTerm n := .op .unit .nil
def identifier {n : Nat} (i : Id) : RawTerm n := .op (.identifier i) .nil
def funE {n : Nat} (first : Ty) (rest : List Ty) (result : Ty)
    (body : RawTerm (n + (rest.length + 1))) : RawTerm n :=
  .op (.funE first rest result) (.cons body .nil)
def fixE {n : Nat} (first : Ty) (rest : List Ty) (result : Ty)
    (body : RawTerm (n + (rest.length + 2))) : RawTerm n :=
  .op (.fixE first rest result) (.cons body .nil)
def sexp_int {n : Nat} (a : RawTerm n) : RawTerm n := .op .sexp_int (.cons a .nil)
def sexp_bool {n : Nat} (a : RawTerm n) : RawTerm n := .op .sexp_bool (.cons a .nil)
def sexp_id {n : Nat} (a : RawTerm n) : RawTerm n := .op .sexp_id (.cons a .nil)
def nil {n : Nat} : RawTerm n := .op .nil .nil
def pair {n : Nat} (a b : RawTerm n) : RawTerm n :=
  .op .pair (.cons a (.cons b .nil))
def operation {n : Nat} (op : Prim) (a b : RawTerm n) : RawTerm n :=
  .op (.operation op) (.cons a (.cons b .nil))
def add {n : Nat} (a b : RawTerm n) : RawTerm n := operation .add a b
def app {n k : Nat} (fn first : RawTerm n) (rest : RawArgs n k) : RawTerm n :=
  .op (.app k) (.cons fn (.cons first rest))
def ifE {n : Nat} (guard yes no : RawTerm n) : RawTerm n :=
  .op .ifE (.cons guard (.cons yes (.cons no .nil)))
def letE {n : Nat} (rhs : RawTerm n) (body : RawTerm (n + 1)) : RawTerm n :=
  .op .letE (.cons rhs (.cons body .nil))
def branch {n : Nat} (p : Pattern) (body : RawTerm (n + p.arity)) : RawTerm n :=
  .op (.branch p) (.cons body .nil)
def matchE {n k : Nat} (scrutinee : RawTerm n) (branches : RawArgs n k) : RawTerm n :=
  .op (.matchE k) (.cons scrutinee branches)
def async {n : Nat} (body : RawTerm n) : RawTerm n := .op .async (.cons body .nil)

/-- Like Syntax.let_ in OCaml, close the chosen variable only in the body. -/
def let_ (x : WSLN.Atom) (rhs body : RawTerm 0) : RawTerm 0 :=
  letE rhs (x ． body)

mutual
inductive IsValue : {n : Nat} → RawTerm n → Prop where
  | integer {n} (z : Int) : IsValue (integer (n := n) z)
  | boolean {n} (b : Bool) : IsValue (boolean (n := n) b)
  | unit {n} : IsValue (unit (n := n))
  | identifier {n} (i : Id) : IsValue (identifier (n := n) i)
  | funE {n} (first : Ty) (rest : List Ty) (result : Ty)
      {body : RawTerm (n + (rest.length + 1))} :
      IsTerm body → IsValue (funE first rest result body)
  | fixE {n} (first : Ty) (rest : List Ty) (result : Ty)
      {body : RawTerm (n + (rest.length + 2))} :
      IsTerm body → IsValue (fixE first rest result body)
  | sexp_int {n} {a : RawTerm n} : IsAtom a → IsValue (sexp_int a)
  | sexp_bool {n} {a : RawTerm n} : IsAtom a → IsValue (sexp_bool a)
  | sexp_id {n} {a : RawTerm n} : IsAtom a → IsValue (sexp_id a)
  | nil {n} : IsValue (nil (n := n))
  | pair {n} {a b : RawTerm n} : IsAtom a → IsAtom b → IsValue (pair a b)

inductive IsAtom : {n : Nat} → RawTerm n → Prop where
  | bound {n} (i : Fin n) : IsAtom (.var i)
  | free {n} (x : WSLN.Atom) : IsAtom (var (n := n) x)
  | value {n} {v : RawTerm n} : IsValue v → IsAtom v

inductive IsTerm : {n : Nat} → RawTerm n → Prop where
  | atom {n} {a : RawTerm n} : IsAtom a → IsTerm a
  | app {n k} {fn first : RawTerm n} {rest : RawArgs n k} :
      IsAtom fn → IsAtom first → IsAtoms rest → IsTerm (app fn first rest)
  | operation {n} (op : Prim) {a b : RawTerm n} :
      IsAtom a → IsAtom b → IsTerm (operation op a b)
  | ifE {n} {guard yes no : RawTerm n} :
      IsAtom guard → IsTerm yes → IsTerm no → IsTerm (ifE guard yes no)
  | letE {n} {rhs : RawTerm n} {body : RawTerm (n + 1)} :
      IsTerm rhs → IsTerm body → IsTerm (letE rhs body)
  | matchE {n k ps} {a : RawTerm n} {branches : RawArgs n k} :
      IsAtom a → IsBranches ps branches → MatchPatterns ps → IsTerm (matchE a branches)
  | async {n} {body : RawTerm n} : IsTerm body → IsTerm (async body)

inductive IsBranch : Pattern → {n : Nat} → RawTerm n → Prop where
  | branch {n p} {body : RawTerm (n + p.arity)} :
      IsTerm body → IsBranch p (branch p body)

/-- Record each branch's pattern while checking its body. -/
inductive IsBranches : List Pattern → {n : Nat} → {ms : List Nat} → Arg signature n ms → Prop where
  | nil {n} : IsBranches [] (n := n) .nil
  | cons {n p ps ms} {b : RawTerm n} {rest : Arg signature n ms} :
      IsBranch p b → IsBranches ps rest → IsBranches (p :: ps) (.cons (m := 0) b rest)

/-- Every actual argument is an atom; the function position is checked separately. -/
inductive IsAtoms : {n : Nat} → {ms : List Nat} → Arg signature n ms → Prop where
  | nil {n} : IsAtoms (n := n) .nil
  | cons {n ms} {a : RawTerm n} {rest : Arg signature n ms} :
      IsAtom a → IsAtoms rest → IsAtoms (.cons (m := 0) a rest)
end

/-- Addition is one of the five primitive operations. -/
theorem IsTerm.add {n} {a b : RawTerm n} (ha : IsAtom a) (hb : IsAtom b) :
    IsTerm (add a b) := .operation .add ha hb

-- The mutual proofs follow the grammar; all operations on trees come from WSLN.
mutual
theorem IsValue.weaken {m n} {v : RawTerm m} (hv : IsValue v) (h : m ≤ n) :
    IsValue (v.weaken n h) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE first rest result hb =>
      exact .funE first rest result (hb.weaken (Nat.add_le_add_right h _))
  | .fixE first rest result hb =>
      exact .fixE first rest result (hb.weaken (Nat.add_le_add_right h _))
  | .sexp_int hp => exact .sexp_int (hp.weaken h)
  | .sexp_bool hp => exact .sexp_bool (hp.weaken h)
  | .sexp_id hp => exact .sexp_id (hp.weaken h)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.weaken h) (hb.weaken h)
termination_by structural hv

theorem IsAtom.weaken {m n} {a : RawTerm m} (ha : IsAtom a) (h : m ≤ n) :
    IsAtom (a.weaken n h) := by
  match ha with
  | .bound i => exact .bound (Fin.castLE h i)
  | .free x => exact .free x
  | .value hv => exact .value (hv.weaken h)
termination_by structural ha

theorem IsTerm.weaken {m n} {t : RawTerm m} (ht : IsTerm t) (h : m ≤ n) :
    IsTerm (t.weaken n h) := by
  match ht with
  | .atom ha => exact .atom (ha.weaken h)
  | .app hf ha hs => exact .app (hf.weaken h) (ha.weaken h) (hs.weaken h)
  | .operation op ha hb => exact .operation op (ha.weaken h) (hb.weaken h)
  | .ifE hg hy hn => exact .ifE (hg.weaken h) (hy.weaken h) (hn.weaken h)
  | .async hb => exact .async (hb.weaken h)
  | .letE hr hb => exact .letE (hr.weaken h) (hb.weaken (Nat.add_le_add_right h 1))
  | .matchE ha hs hf => exact .matchE (ha.weaken h) (hs.weaken h) hf
termination_by structural ht

theorem IsAtoms.weaken {m n ms} {args : Arg signature m ms} (hs : IsAtoms args) (h : m ≤ n) :
    IsAtoms (args.weaken n h) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.weaken h) (hs.weaken h)
termination_by structural hs

theorem IsBranch.weaken {m n p} {b : RawTerm m} (hb : IsBranch p b) (h : m ≤ n) :
    IsBranch p (b.weaken n h) := by
  match hb with
  | .branch ht => exact .branch (ht.weaken (Nat.add_le_add_right h _))
termination_by structural hb

theorem IsBranches.weaken {m n ps ms} {bs : Arg signature m ms}
    (hs : IsBranches ps bs) (h : m ≤ n) : IsBranches ps (bs.weaken n h) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.weaken h) (hs.weaken h)
termination_by structural hs

end

mutual
theorem IsValue.subst {n} {v : RawTerm n} (hv : IsValue v)
    {σ : Sb signature} (hσ : ∀ x, IsAtom (σ x)) : IsValue (σ * v) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE first rest result hb => exact .funE first rest result (hb.subst hσ)
  | .fixE first rest result hb => exact .fixE first rest result (hb.subst hσ)
  | .sexp_int hp => exact .sexp_int (hp.subst hσ)
  | .sexp_bool hp => exact .sexp_bool (hp.subst hσ)
  | .sexp_id hp => exact .sexp_id (hp.subst hσ)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.subst hσ) (hb.subst hσ)
termination_by structural hv

theorem IsAtom.subst {n} {a : RawTerm n} (ha : IsAtom a)
    {σ : Sb signature} (hσ : ∀ x, IsAtom (σ x)) : IsAtom (σ * a) := by
  match ha with
  | .bound i => exact .bound i
  | .free x => exact (hσ x).weaken (Nat.zero_le n)
  | .value hv => exact .value (hv.subst hσ)
termination_by structural ha

theorem IsTerm.subst {n} {t : RawTerm n} (ht : IsTerm t)
    {σ : Sb signature} (hσ : ∀ x, IsAtom (σ x)) : IsTerm (σ * t) := by
  match ht with
  | .atom ha => exact .atom (ha.subst hσ)
  | .app hf ha hs => exact .app (hf.subst hσ) (ha.subst hσ) (hs.subst hσ)
  | .operation op ha hb => exact .operation op (ha.subst hσ) (hb.subst hσ)
  | .ifE hg hy hn => exact .ifE (hg.subst hσ) (hy.subst hσ) (hn.subst hσ)
  | .async hb => exact .async (hb.subst hσ)
  | .letE hr hb => exact .letE (hr.subst hσ) (hb.subst hσ)
  | .matchE ha hs hf => exact .matchE (ha.subst hσ) (hs.subst hσ) hf
termination_by structural ht

theorem IsAtoms.subst {n ms} {args : Arg signature n ms} (hs : IsAtoms args)
    {σ : Sb signature} (hσ : ∀ x, IsAtom (σ x)) : IsAtoms (σ * args) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.subst hσ) (hs.subst hσ)
termination_by structural hs

theorem IsBranch.subst {n p} {b : RawTerm n} (hb : IsBranch p b)
    {σ : Sb signature} (hσ : ∀ x, IsAtom (σ x)) : IsBranch p (σ * b) := by
  match hb with
  | .branch ht => exact .branch (ht.subst hσ)
termination_by structural hb

theorem IsBranches.subst {n ps ms} {bs : Arg signature n ms} (hs : IsBranches ps bs)
    {σ : Sb signature} (hσ : ∀ x, IsAtom (σ x)) : IsBranches ps (σ * bs) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.subst hσ) (hs.subst hσ)
termination_by structural hs

end

/-- A single atom replacement is an instance of the simultaneous operation. -/
theorem atom_substitution (x : WSLN.Atom) {a : RawTerm 0} (ha : IsAtom a) :
    ∀ y, IsAtom (((x ≔ a) : Sb signature) y) := by
  intro y
  by_cases h : x = y
  · subst y; simpa using ha
  · rw [Sb.single_neq a h]; exact .free y

mutual
theorem IsValue.close {m n} {v : RawTerm m} (hv : IsValue v)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsValue (cls x i v e) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE first rest result hb =>
      exact .funE first rest result (hb.close x (shiftIdx (rest.length + 1) i) (by omega))
  | .fixE first rest result hb =>
      exact .fixE first rest result (hb.close x (shiftIdx (rest.length + 2) i) (by omega))
  | .sexp_int hp => exact .sexp_int (hp.close x (shiftIdx 0 i) e)
  | .sexp_bool hp => exact .sexp_bool (hp.close x (shiftIdx 0 i) e)
  | .sexp_id hp => exact .sexp_id (hp.close x (shiftIdx 0 i) e)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.close x (shiftIdx 0 i) e) (hb.close x (shiftIdx 0 i) e)
termination_by structural hv

theorem IsAtom.close {m n} {a : RawTerm m} (ha : IsAtom a)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsAtom (cls x i a e) := by
  match ha with
  | .bound j => exact .bound _
  | .free y =>
      change IsAtom (if x = y then .var i else var y)
      split
      · exact .bound i
      · exact .free y
  | .value hv => exact .value (hv.close x i e)
termination_by structural ha

theorem IsTerm.close {m n} {t : RawTerm m} (ht : IsTerm t)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsTerm (cls x i t e) := by
  match ht with
  | .atom ha => exact .atom (ha.close x i e)
  | .app hf ha hs =>
      exact .app (hf.close x (shiftIdx 0 i) e) (ha.close x (shiftIdx 0 i) e) (hs.close x i e)
  | .operation op ha hb => exact .operation op (ha.close x (shiftIdx 0 i) e) (hb.close x (shiftIdx 0 i) e)
  | .ifE hg hy hn =>
      exact .ifE (hg.close x (shiftIdx 0 i) e)
        (hy.close x (shiftIdx 0 i) e) (hn.close x (shiftIdx 0 i) e)
  | .async hb => exact .async (hb.close x (shiftIdx 0 i) e)
  | .letE hr hb => exact .letE (hr.close x (shiftIdx 0 i) e) (hb.close x (shiftIdx 1 i) (by omega))
  | .matchE ha hs hf => exact .matchE (ha.close x (shiftIdx 0 i) e) (hs.close x i e) hf
termination_by structural ht

theorem IsAtoms.close {m n ms} {args : Arg signature m ms} (hs : IsAtoms args)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsAtoms (clsArg x i args e) := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.close x (shiftIdx 0 i) e) (hs.close x i e)
termination_by structural hs

theorem IsBranch.close {m n p} {b : RawTerm m} (hb : IsBranch p b)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsBranch p (cls x i b e) := by
  match hb with
  | .branch ht => exact .branch (ht.close x (shiftIdx p.arity i) (by omega))
termination_by structural hb

theorem IsBranches.close {m n ps ms} {bs : Arg signature m ms} (hs : IsBranches ps bs)
    (x : WSLN.Atom) (i : Fin n) (e : n = m + 1) : IsBranches ps (clsArg x i bs e) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.close x (shiftIdx 0 i) e) (hs.close x i e)
termination_by structural hs

end

theorem IsTerm.let_ (x : WSLN.Atom) {rhs body : RawTerm 0}
    (hr : IsTerm rhs) (hb : IsTerm body) : IsTerm (let_ x rhs body) :=
  .letE hr (hb.close x ⟨0, by omega⟩ rfl)

mutual
theorem IsValue.open {m n} {v : RawTerm m} (hv : IsValue v)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom a) (e : m = n + 1) :
    IsValue (opn i a v e) := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .funE first rest result hb =>
      exact .funE first rest result (hb.open (shiftIdx (rest.length + 1) i) ha (by omega))
  | .fixE first rest result hb =>
      exact .fixE first rest result (hb.open (shiftIdx (rest.length + 2) i) ha (by omega))
  | .sexp_int hp => exact .sexp_int (hp.open (shiftIdx 0 i) ha e)
  | .sexp_bool hp => exact .sexp_bool (hp.open (shiftIdx 0 i) ha e)
  | .sexp_id hp => exact .sexp_id (hp.open (shiftIdx 0 i) ha e)
  | .nil => exact .nil
  | .pair hb hc => exact .pair (hb.open (shiftIdx 0 i) ha e) (hc.open (shiftIdx 0 i) ha e)
termination_by structural hv

theorem IsAtom.open {m n} {b : RawTerm m} (hb : IsAtom b)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom a) (e : m = n + 1) :
    IsAtom (opn i a b e) := by
  match hb with
  | .bound j =>
      rw [opn_var]
      split
      · exact ha.weaken (Nat.zero_le n)
      · exact .bound _
  | .free x => exact .free x
  | .value hv => exact .value (hv.open i ha e)
termination_by structural hb

theorem IsTerm.open {m n} {t : RawTerm m} (ht : IsTerm t)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom a) (e : m = n + 1) :
    IsTerm (opn i a t e) := by
  match ht with
  | .atom hb => exact .atom (hb.open i ha e)
  | .app hf hb hs =>
      exact .app (hf.open (shiftIdx 0 i) ha e) (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e)
  | .operation op hb hc => exact .operation op (hb.open (shiftIdx 0 i) ha e) (hc.open (shiftIdx 0 i) ha e)
  | .ifE hg hy hn =>
      exact .ifE (hg.open (shiftIdx 0 i) ha e)
        (hy.open (shiftIdx 0 i) ha e) (hn.open (shiftIdx 0 i) ha e)
  | .async hb => exact .async (hb.open (shiftIdx 0 i) ha e)
  | .letE hr hb => exact .letE (hr.open (shiftIdx 0 i) ha e) (hb.open (shiftIdx 1 i) ha (by omega))
  | .matchE hb hs hf => exact .matchE (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e) hf
termination_by structural ht

theorem IsAtoms.open {m n ms} {args : Arg signature m ms} (hs : IsAtoms args)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom a) (e : m = n + 1) :
    IsAtoms (opnArg i a args e) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e)
termination_by structural hs

theorem IsBranch.open {m n p} {b : RawTerm m} (hb : IsBranch p b)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom a) (e : m = n + 1) :
    IsBranch p (opn i a b e) := by
  match hb with
  | .branch ht => exact .branch (ht.open (shiftIdx p.arity i) ha (by omega))
termination_by structural hb

theorem IsBranches.open {m n ps ms} {bs : Arg signature m ms} (hs : IsBranches ps bs)
    (i : Fin m) {a : RawTerm 0} (ha : IsAtom a) (e : m = n + 1) :
    IsBranches ps (opnArg i a bs e) := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.open (shiftIdx 0 i) ha e) (hs.open i ha e)
termination_by structural hs

end

theorem IsTerm.conc {body : RawTerm 1} (hb : IsTerm body)
    {a : RawTerm 0} (ha : IsAtom a) : IsTerm (body.conc a) :=
  hb.open ⟨0, by omega⟩ ha rfl

-- The library permits this replacement, but it leaves our source grammar.
theorem arbitrary_substitution_leaves_grammar :
    ¬ IsTerm (n := 0) (((0 ≔ letE (integer 2) i0) : Sb signature) * add (var 0) (integer 1)) := by
  change ¬ IsTerm (add (letE (integer 2) i0) (integer 1))
  intro ht
  cases ht with
  | atom ha => cases ha with | value hv => cases hv
  | operation _ ha _ => cases ha with | value hv => cases hv

end SourceRuntime.Source

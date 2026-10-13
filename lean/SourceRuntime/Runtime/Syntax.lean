import SourceRuntime.Source.Syntax
import Std.Data.ExtTreeSet

/-!
Runtime-calculus.md §§1–2.2: phrases formed at a finite active-name set U.
Source operator labels retain their arities, but all children are runtime trees.
WSLN binds source variables; future names are separate, nullary operators.
Formation at U checks future scope, not source-variable closure or typing.
-/

namespace SourceRuntime.Runtime

open WSLN
open Source (Ty Id Prim Pattern MatchPatterns)

/-- An explicit future name, distinct from WSLN variable names and Id literals.
    The index is arbitrary precision, as in OCaml FName; it does not allocate a name. -/
structure FName where
  index : Nat
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq

instance : Std.LawfulEqCmp (compareOn FName.index) where
  eq_of_compare {a b} h := by
    have h' : a.index = b.index := Std.LawfulEqOrd.eq_of_compare h
    cases a; cases b; cases h'; rfl

/-- Finite sets from Lean's standard library; membership compares future indices. -/
abbrev ActiveNames := Std.ExtTreeSet FName (compareOn FName.index)

inductive Op where
  | source : Source.Op → Op
  | future : FName → Op

def signature : Sig where
  Op := Op
  ar
    | .source op => Source.signature.ar op
    | .future _ => []

/-- n counts source-variable binders; active future names are checked separately. -/
abbrev RawTerm (n : Nat) := Trm signature n
abbrev RawArgs (n k : Nat) := Arg signature n (List.replicate k 0)

def var {n : Nat} (x : WSLN.Atom) : RawTerm n := .atom x
def integer {n : Nat} (z : Int) : RawTerm n := .op (.source (.integer z)) .nil
def boolean {n : Nat} (b : Bool) : RawTerm n := .op (.source (.boolean b)) .nil
def unit {n : Nat} : RawTerm n := .op (.source .unit) .nil
def identifier {n : Nat} (i : Id) : RawTerm n := .op (.source (.identifier i)) .nil
def future {n : Nat} (p : FName) : RawTerm n := .op (.future p) .nil
def funE {n : Nat} (first : Ty) (rest : List Ty) (result : Ty)
    (body : RawTerm (n + (rest.length + 1))) : RawTerm n :=
  .op (.source (.funE first rest result)) (.cons body .nil)
def fixE {n : Nat} (first : Ty) (rest : List Ty) (result : Ty)
    (body : RawTerm (n + (rest.length + 2))) : RawTerm n :=
  .op (.source (.fixE first rest result)) (.cons body .nil)
def sexp_int {n : Nat} (a : RawTerm n) : RawTerm n := .op (.source .sexp_int) (.cons a .nil)
def sexp_bool {n : Nat} (a : RawTerm n) : RawTerm n := .op (.source .sexp_bool) (.cons a .nil)
def sexp_id {n : Nat} (a : RawTerm n) : RawTerm n := .op (.source .sexp_id) (.cons a .nil)
def nil {n : Nat} : RawTerm n := .op (.source .nil) .nil
def pair {n : Nat} (a b : RawTerm n) : RawTerm n :=
  .op (.source .pair) (.cons a (.cons b .nil))
def operation {n : Nat} (op : Prim) (a b : RawTerm n) : RawTerm n :=
  .op (.source (.operation op)) (.cons a (.cons b .nil))
def app {n k : Nat} (fn first : RawTerm n) (rest : RawArgs n k) : RawTerm n :=
  .op (.source (.app k)) (.cons fn (.cons first rest))
def ifE {n : Nat} (guard yes no : RawTerm n) : RawTerm n :=
  .op (.source .ifE) (.cons guard (.cons yes (.cons no .nil)))
def letE {n : Nat} (rhs : RawTerm n) (body : RawTerm (n + 1)) : RawTerm n :=
  .op (.source .letE) (.cons rhs (.cons body .nil))
def branch {n : Nat} (p : Pattern) (body : RawTerm (n + p.arity)) : RawTerm n :=
  .op (.source (.branch p)) (.cons body .nil)
def matchE {n k : Nat} (scrutinee : RawTerm n) (branches : RawArgs n k) : RawTerm n :=
  .op (.source (.matchE k)) (.cons scrutinee branches)
def async {n : Nat} (body : RawTerm n) : RawTerm n := .op (.source .async) (.cons body .nil)

/-- Only the body binds x. WSLN abstraction leaves all future names fixed. -/
def let_ (x : WSLN.Atom) (rhs body : RawTerm 0) : RawTerm 0 :=
  letE rhs (x ． body)

mutual
inductive IsValue (U : ActiveNames) : {n : Nat} → RawTerm n → Prop where
  | integer {n} (z : Int) : IsValue U (integer (n := n) z)
  | boolean {n} (b : Bool) : IsValue U (boolean (n := n) b)
  | unit {n} : IsValue U (unit (n := n))
  | identifier {n} (i : Id) : IsValue U (identifier (n := n) i)
  | future {n p} : p ∈ U → IsValue U (future (n := n) p)
  | funE {n} (first : Ty) (rest : List Ty) (result : Ty)
      {body : RawTerm (n + (rest.length + 1))} :
      IsTerm U body → IsValue U (funE first rest result body)
  | fixE {n} (first : Ty) (rest : List Ty) (result : Ty)
      {body : RawTerm (n + (rest.length + 2))} :
      IsTerm U body → IsValue U (fixE first rest result body)
  | sexp_int {n} {a : RawTerm n} : IsAtom U a → IsValue U (sexp_int a)
  | sexp_bool {n} {a : RawTerm n} : IsAtom U a → IsValue U (sexp_bool a)
  | sexp_id {n} {a : RawTerm n} : IsAtom U a → IsValue U (sexp_id a)
  | nil {n} : IsValue U (nil (n := n))
  | pair {n} {a b : RawTerm n} : IsAtom U a → IsAtom U b → IsValue U (pair a b)

inductive IsAtom (U : ActiveNames) : {n : Nat} → RawTerm n → Prop where
  | bound {n} (i : Fin n) : IsAtom U (.var i)
  | free {n} (x : WSLN.Atom) : IsAtom U (var (n := n) x)
  | value {n} {v : RawTerm n} : IsValue U v → IsAtom U v

inductive IsTerm (U : ActiveNames) : {n : Nat} → RawTerm n → Prop where
  | atom {n} {a : RawTerm n} : IsAtom U a → IsTerm U a
  | app {n k} {fn first : RawTerm n} {rest : RawArgs n k} :
      IsAtom U fn → IsAtom U first → IsAtoms U rest → IsTerm U (app fn first rest)
  | operation {n} (op : Prim) {a b : RawTerm n} :
      IsAtom U a → IsAtom U b → IsTerm U (operation op a b)
  | ifE {n} {guard yes no : RawTerm n} :
      IsAtom U guard → IsTerm U yes → IsTerm U no → IsTerm U (ifE guard yes no)
  | letE {n} {rhs : RawTerm n} {body : RawTerm (n + 1)} :
      IsTerm U rhs → IsTerm U body → IsTerm U (letE rhs body)
  | matchE {n k ps} {a : RawTerm n} {branches : RawArgs n k} :
      IsAtom U a → IsBranches U ps branches → MatchPatterns ps → IsTerm U (matchE a branches)
  | async {n} {body : RawTerm n} : IsTerm U body → IsTerm U (async body)

inductive IsBranch (U : ActiveNames) : Pattern → {n : Nat} → RawTerm n → Prop where
  | branch {n p} {body : RawTerm (n + p.arity)} :
      IsTerm U body → IsBranch U p (branch p body)

inductive IsBranches (U : ActiveNames) :
    List Pattern → {n : Nat} → {ms : List Nat} → Arg signature n ms → Prop where
  | nil {n} : IsBranches U [] (n := n) .nil
  | cons {n p ps ms} {b : RawTerm n} {rest : Arg signature n ms} :
      IsBranch U p b → IsBranches U ps rest → IsBranches U (p :: ps) (.cons (m := 0) b rest)

inductive IsAtoms (U : ActiveNames) : {n : Nat} → {ms : List Nat} → Arg signature n ms → Prop where
  | nil {n} : IsAtoms U (n := n) .nil
  | cons {n ms} {a : RawTerm n} {rest : Arg signature n ms} :
      IsAtom U a → IsAtoms U rest → IsAtoms U (.cons (m := 0) a rest)
end

/-- RVal-Future is exactly membership in the active-name set. -/
@[simp] theorem future_value_iff {U n p} : IsValue U (future (n := n) p) ↔ p ∈ U := by
  constructor
  · intro h; cases h with | future hp => exact hp
  · exact IsValue.future

/-- Source-variable substitution never substitutes for a future name (§3). -/
@[simp] theorem subst_future {n} (σ : Sb signature) (p : FName) :
    σ * future (n := n) p = future p := rfl

-- Parameter proliferation (§2.2): enlarging U leaves the phrase itself unchanged.
mutual
theorem IsValue.mono {U U' n} {v : RawTerm n} (hv : IsValue U v)
    (h : ∀ p, p ∈ U → p ∈ U') : IsValue U' v := by
  match hv with
  | .integer z => exact .integer z
  | .boolean b => exact .boolean b
  | .unit => exact .unit
  | .identifier i => exact .identifier i
  | .future hp => exact .future (h _ hp)
  | .funE first rest result hb => exact .funE first rest result (hb.mono h)
  | .fixE first rest result hb => exact .fixE first rest result (hb.mono h)
  | .sexp_int ha => exact .sexp_int (ha.mono h)
  | .sexp_bool ha => exact .sexp_bool (ha.mono h)
  | .sexp_id ha => exact .sexp_id (ha.mono h)
  | .nil => exact .nil
  | .pair ha hb => exact .pair (ha.mono h) (hb.mono h)
termination_by structural hv

theorem IsAtom.mono {U U' n} {a : RawTerm n} (ha : IsAtom U a)
    (h : ∀ p, p ∈ U → p ∈ U') : IsAtom U' a := by
  match ha with
  | .bound i => exact .bound i
  | .free x => exact .free x
  | .value hv => exact .value (hv.mono h)
termination_by structural ha

theorem IsTerm.mono {U U' n} {t : RawTerm n} (ht : IsTerm U t)
    (h : ∀ p, p ∈ U → p ∈ U') : IsTerm U' t := by
  match ht with
  | .atom ha => exact .atom (ha.mono h)
  | .app hf ha hs => exact .app (hf.mono h) (ha.mono h) (hs.mono h)
  | .operation op ha hb => exact .operation op (ha.mono h) (hb.mono h)
  | .ifE hg hy hn => exact .ifE (hg.mono h) (hy.mono h) (hn.mono h)
  | .letE hr hb => exact .letE (hr.mono h) (hb.mono h)
  | .matchE ha hs hf => exact .matchE (ha.mono h) (hs.mono h) hf
  | .async hb => exact .async (hb.mono h)
termination_by structural ht

theorem IsBranch.mono {U U' n p} {b : RawTerm n} (hb : IsBranch U p b)
    (h : ∀ q, q ∈ U → q ∈ U') : IsBranch U' p b := by
  match hb with
  | .branch ht => exact .branch (ht.mono h)
termination_by structural hb

theorem IsBranches.mono {U U' n ps ms} {bs : Arg signature n ms} (hs : IsBranches U ps bs)
    (h : ∀ p, p ∈ U → p ∈ U') : IsBranches U' ps bs := by
  match hs with
  | .nil => exact .nil
  | .cons hb hs => exact .cons (hb.mono h) (hs.mono h)
termination_by structural hs

theorem IsAtoms.mono {U U' n ms} {args : Arg signature n ms} (hs : IsAtoms U args)
    (h : ∀ p, p ∈ U → p ∈ U') : IsAtoms U' args := by
  match hs with
  | .nil => exact .nil
  | .cons ha hs => exact .cons (ha.mono h) (hs.mono h)
termination_by structural hs
end

end SourceRuntime.Runtime

import SourceRuntime.Source.Typing

/-!
Named binder rules for source §6, derived from the locally nameless typing rules.
The displayed context Γ,x₁:A₁,...,xₖ:Aₖ is represented by the reverse of the
parameter list followed by Γ: each later update is at the front of List.lookup.
These bridges use the existing fun_, fix_ and branch_ constructors.
-/

namespace SourceRuntime.Source
open WSLN Adequacy

private theorem cast_abs {m n} (e : m = n) (x : WSLN.Atom) (body : RawTerm m) :
    (x ． body).castScope (congrArg (· + 1) e) = (x ． (body.castScope e)) := by
  cases e; rfl

/-- Move every displayed binding from Γ into its corresponding ordered slot. -/
theorem Typing.closeMany {Γ body B} (parameters : List (WSLN.Atom × Ty))
    (ht : HasType (parameters.reverse ++ Γ) body B) :
    Typing Γ (pushMany (parameters.map Prod.snd) Fin.elim0)
      ((closeMany (parameters.map Prod.fst) body).castScope (by simp)) B := by
  induction parameters generalizing Γ with
  | nil => simpa [closeMany, pushMany, Trm.castScope] using ht
  | cons p ps ih =>
      obtain ⟨x, A⟩ := p
      have hr : HasType (ps.reverse ++ (x, A) :: Γ) body B := by
        simpa [List.reverse_cons, List.append_assoc] using ht
      have htail := ih hr
      have hclose := htail.close (0 : Fin (0 + (ps.map Prod.snd).length + 1)) rfl
        (Δ' := push A (pushMany (ps.map Prod.snd) Fin.elim0)) rfl (by
          intro j
          have hj : insert (0 : Fin (0 + (ps.map Prod.snd).length + 1)) j = j.succ := by
            apply Fin.ext; simp [insert_val]
          simpa [push] using congrArg (push A (pushMany (ps.map Prod.snd) Fin.elim0)) hj)
      simp only [List.map_cons, List.length_cons, Source.closeMany, pushMany]
      rw [cast_abs (by simp : (ps.map Prod.fst).length = 0 + (ps.map Prod.snd).length)]
      exact hclose

theorem typing_fun_ {Γ body} (first : WSLN.Atom × Ty) (rest : List (WSLN.Atom × Ty)) (B : Ty)
    (distinct : (first.1 :: rest.map Prod.fst).Nodup)
    (ht : HasType ((first :: rest).reverse ++ Γ) body B) :
    HasType Γ (fun_ first rest B body distinct) (.arrow first.2 (rest.map Prod.snd) B) := by
  apply Typing.funE
  simpa only [List.map_cons] using ht.closeMany (first :: rest)

theorem typing_fix_ {Γ body} (self : WSLN.Atom) (first : WSLN.Atom × Ty)
    (rest : List (WSLN.Atom × Ty)) (B : Ty)
    (distinct : (self :: first.1 :: rest.map Prod.fst).Nodup)
    (ht : HasType (((self, .arrow first.2 (rest.map Prod.snd) B) :: first :: rest).reverse ++ Γ) body B) :
    HasType Γ (fix_ self first rest B body distinct) (.arrow first.2 (rest.map Prod.snd) B) := by
  apply Typing.fixE
  simpa only [List.map_cons] using ht.closeMany ((self, .arrow first.2 (rest.map Prod.snd) B) :: first :: rest)

/-- The six branch rules' fixed field types, in pattern order. -/
def Pattern.fieldTypes : Pattern → List Ty
  | .int => [.int]
  | .bool => [.bool]
  | .id => [.id]
  | .pair => [.sexp, .sexp]
  | .nil | .wildcard => []

private theorem fieldTypes_length (p : Pattern) : p.fieldTypes.length = p.arity := by
  cases p <;> rfl

private theorem typing_cast_types {Γ As Bs body A}
    (ht : Typing Γ (pushMany As Fin.elim0) body A) (e : As = Bs) :
    Typing Γ (pushMany Bs Fin.elim0)
      (body.castScope (congrArg (fun ts : List Ty => 0 + ts.length) e)) A := by
  cases e; exact ht

theorem typing_branch_ {Γ body B} (p : Pattern) (parameters : List (WSLN.Atom × Ty))
    (fields : parameters.map Prod.snd = p.fieldTypes)
    (distinct : (parameters.map Prod.fst).Nodup)
    (ht : HasType (parameters.reverse ++ Γ) body B) :
    HasBranchType Γ p (branch_ p (parameters.map Prod.fst) body
      (by have h := congrArg List.length fields; simpa [fieldTypes_length] using h) distinct) B := by
  have hb := typing_cast_types (ht.closeMany parameters) fields
  cases p with
  | int => apply BranchTyping.int; simpa only [Pattern.fieldTypes, pushMany, castScope_trans] using hb
  | bool => apply BranchTyping.bool; simpa only [Pattern.fieldTypes, pushMany, castScope_trans] using hb
  | id => apply BranchTyping.id; simpa only [Pattern.fieldTypes, pushMany, castScope_trans] using hb
  | nil => apply BranchTyping.nil; simpa only [Pattern.fieldTypes, pushMany, castScope_trans] using hb
  | pair => apply BranchTyping.pair; simpa only [Pattern.fieldTypes, pushMany, castScope_trans] using hb
  | wildcard => apply BranchTyping.wildcard; simpa only [Pattern.fieldTypes, pushMany, castScope_trans] using hb

end SourceRuntime.Source

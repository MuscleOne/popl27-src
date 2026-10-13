import SourceRuntime.Runtime.Reduction

/-!
R-Local-Preservation and R-State-Preservation, including finite executions.
The local proof retains the chosen focus type and both mapping invariants.
Interleave-Future writes into the returned mapping, preserving fresh allocations.
-/

namespace SourceRuntime.Runtime
open WSLN
open Source (Ty)

theorem ArgMember.typing {sig Γ b ms bs ps A} (h : ArgMember b (ms := ms) bs)
    (hs : BranchesTyping sig Γ Fin.elim0 ps bs A) : ∃ p, HasBranchType sig Γ p b A := by
  induction h generalizing ps with
  | here => cases hs with | cons hb _ => exact ⟨_, hb⟩
  | there _ ih => cases hs with | cons _ hs => exact ih hs

/-- The selected constructor branch returns its declared result type. -/
theorem MatchBranch.preservation {sig Γ v b result p A} (h : MatchBranch (domain sig) v b result)
    (hv : HasType sig Γ v .sexp) (hb : HasBranchType sig Γ p b A) : HasType sig Γ result A := by
  cases h with
  | int ha => cases hv with | sexp_int _ ht => cases hb with | int hbody => exact hbody.conc ha ht
  | bool ha => cases hv with | sexp_bool _ ht => cases hb with | bool hbody => exact hbody.conc ha ht
  | id ha => cases hv with | sexp_id _ ht => cases hb with | id hbody => exact hbody.conc ha ht
  | nil => cases hb with | nil ht => exact ht
  | pair ha hc =>
      cases hv with
      | pair _ _ hta htc => cases hb with | pair ht => exact (ht.conc ha hta).conc hc htc

-- Both new maps receive the same key; old entry types survive signature extension.
private theorem allocate_typed {sig : Signature} {mu : Mapping} {q : FName} {body A}
    (hd : domain mu = domain sig)
    (hm : ∀ (p : FName) t B, mu[p]? = some t → sig[p]? = some B → HasType sig [] t B)
    (ht : HasType sig [] body A) (fresh : q ∉ domain sig) :
    domain (mu.insert q body) = domain (sig.insert q A) ∧
    ∀ (p : FName) t B, (mu.insert q body)[p]? = some t → (sig.insert q A)[p]? = some B →
      HasType (sig.insert q A) [] t B := by
  have he := Signature.extends_insert A fresh
  refine ⟨by simp only [domain_insert, hd], ?_⟩
  intro p t B hp hs
  by_cases h : q = p
  · subst p
    simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hp hs
    subst t; subst B
    exact ht.sigma_weaken he
  · simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, if_neg h] at hp hs
    exact (hm p t B hp hs).sigma_weaken he

/-- R-Local-Preservation, with the focus type and mapping premises explicit. -/
theorem LocalStep.preservation {sig mu t sig' mu' t'} (h : LocalStep sig mu t sig' mu' t')
    (hd : domain mu = domain sig)
    (hm : ∀ (p : FName) body B, mu[p]? = some body → sig[p]? = some B → HasType sig [] body B)
    {A} (ht : HasType sig [] t A) :
    domain mu' = domain sig' ∧ HasType sig' [] t' A ∧
    ∀ (p : FName) body B, mu'[p]? = some body → sig'[p]? = some B → HasType sig' [] body B := by
  induction h generalizing A with
  | search_let _ hs _ ih =>
      cases ht with
      | letE hr hb =>
          obtain ⟨hd', hr', hm'⟩ := ih hr
          exact ⟨hd', .letE hr' (hb.sigma_weaken hs.sigma_extends), hm'⟩
  | beta arity hb hv hvs =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | app _ _ hf ha has =>
          cases hf with
          | funE hbody => exact (ArgsTyping.cons (.value hv) ha has).instantiate hbody _
  | fix_beta arity hb hv hvs =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | app _ _ hf ha has =>
          cases hf with
          | fixE hbody =>
              exact (ArgsTyping.cons (.value (.fixE _ _ _ hb)) (.fixE hbody)
                (.cons (.value hv) ha has)).instantiate hbody _
  | let_value hv _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with | letE hr hb => exact hb.conc (.value hv) hr
  | match_constructor _ _ hmem hc =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | matchE _ hv hbs _ =>
          obtain ⟨_, hb⟩ := hmem.typing hbs
          exact hc.preservation hv hb
  | match_wildcard _ _ _ _ _ hmem =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | matchE _ _ hbs _ =>
          obtain ⟨_, hb⟩ := hmem.typing hbs
          cases hb with | wildcard hb => exact hb
  | add m n => refine ⟨hd, ?_, hm⟩; cases ht; exact .integer (m + n)
  | sub m n => refine ⟨hd, ?_, hm⟩; cases ht; exact .integer (m - n)
  | mul m n => refine ⟨hd, ?_, hm⟩; cases ht; exact .integer (m * n)
  | eq_int_true _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean true
  | eq_int_false _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean false
  | eq_id_true _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean true
  | eq_id_false _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ _ _ _ => simp at hop
      | eq _ _ _ _ _ => exact .boolean false
  | lt_true _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ _ _ _ => simp at hop
      | lt _ _ _ _ => exact .boolean true
  | lt_false _ =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ _ _ _ => simp at hop
      | lt _ _ _ _ => exact .boolean false
  | if_true _ _ => refine ⟨hd, ?_, hm⟩; cases ht with | ifE _ _ hy _ => exact hy
  | if_false _ _ => refine ⟨hd, ?_, hm⟩; cases ht with | ifE _ _ _ hn => exact hn
  | spawn_async hbody fresh =>
      cases ht with
      | async hb =>
          cases hbody.unique hb
          obtain ⟨hd', hm'⟩ := allocate_typed hd hm hbody fresh
          exact ⟨hd', .future (by simp), hm'⟩
  | spawn_app _ hApp fresh _ =>
      cases ht with
      | letE hr hb =>
          cases hApp.unique hr
          obtain ⟨hd', hm'⟩ := allocate_typed hd hm hApp fresh
          exact ⟨hd', .letE (.future (by simp))
            (hb.sigma_weaken (Signature.extends_insert _ fresh)), hm'⟩
  | deref_app hp hw =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | app _ ha hf ht hs => exact .app (.value hw) ha (hm _ _ _ hp (typing_future_iff.mp hf)) ht hs
  | deref_op_left hp hw =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop _ hb hf ht => exact .arith hop (.value hw) hb (hm _ _ _ hp (typing_future_iff.mp hf)) ht
      | eq hA _ hb hf ht => exact .eq hA (.value hw) hb (hm _ _ _ hp (typing_future_iff.mp hf)) ht
      | lt _ hb hf ht => exact .lt (.value hw) hb (hm _ _ _ hp (typing_future_iff.mp hf)) ht
  | deref_op_right hp hw =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | arith hop ha _ ht hf => exact .arith hop ha (.value hw) ht (hm _ _ _ hp (typing_future_iff.mp hf))
      | eq hA ha _ ht hf => exact .eq hA ha (.value hw) ht (hm _ _ _ hp (typing_future_iff.mp hf))
      | lt ha _ ht hf => exact .lt ha (.value hw) ht (hm _ _ _ hp (typing_future_iff.mp hf))
  | deref_if hp hw =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | ifE _ hf hy hn => exact .ifE (.value hw) (hm _ _ _ hp (typing_future_iff.mp hf)) hy hn
  | deref_match hp hw =>
      refine ⟨hd, ?_, hm⟩
      cases ht with
      | matchE _ hf hs hc => exact .matchE (.value hw) (hm _ _ _ hp (typing_future_iff.mp hf)) hs hc

/-- The local theorem restricted to the paper's formed state carrier. -/
theorem local_preservation {s t : State} (h : s.LocalStep t) (hs : s.Ok)
    {A} (ht : HasType s.signature [] s.focus A) : t.Ok ∧ HasType t.signature [] t.focus A := by
  obtain ⟨hd, ht', hm⟩ := h.preservation hs.domains hs.entries ht
  exact ⟨⟨hd, ⟨A, ht'⟩, hm⟩, ht'⟩

/-- R-State-Preservation covers both interleaving rules and retains the focus type. -/
theorem preservation {s u : State} (h : Step s u) (hs : s.Ok)
    {A} (ht : HasType s.signature [] s.focus A) : u.Ok ∧ HasType u.signature [] u.focus A := by
  cases h with
  | focus h => exact local_preservation h hs ht
  | @future t u p body hp h hsig hfocus hmap =>
      have hpin : p ∈ s.signature := mem_domain.mp (hs.domains ▸ mem_domain_of_lookup hp)
      have hpType := Std.ExtTreeMap.getElem?_eq_some_getElem hpin
      have hbody := hs.entries p body _ hp hpType
      have hselected : (s.withFocus body (s.entries_formed p body hp)).Ok :=
        ⟨hs.domains, ⟨_, hbody⟩, hs.entries⟩
      obtain ⟨htOk, hresult⟩ := local_preservation h hselected hbody
      have he := h.sigma_extends
      have hpType' := he p _ hpType
      have ht' : HasType u.signature [] u.focus A := by
        rw [hsig, hfocus]
        exact ht.sigma_weaken he
      refine ⟨⟨?_, ⟨A, ht'⟩, ?_⟩, ht'⟩
      · rw [hmap, hsig, domain_insert, htOk.domains]
        apply Std.ExtTreeSet.ext_mem
        intro q
        simp only [Std.ExtTreeSet.mem_insert, Std.LawfulEqCmp.compare_eq_iff_eq]
        constructor
        · rintro (rfl | hq)
          · exact mem_domain_of_lookup hpType'
          · exact hq
        · exact Or.inr
      · intro q value B hm hB
        rw [hmap] at hm
        rw [hsig] at hB ⊢
        by_cases heq : p = q
        · subst q
          simp only [Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq] at hm
          subst value
          cases Option.some.inj (hpType'.symm.trans hB)
          exact hresult
        · simp only [Std.ExtTreeMap.getElem?_insert, Std.LawfulEqCmp.compare_eq_iff_eq, if_neg heq] at hm
          exact htOk.entries q value B hm hB

theorem preservation_steps {s t : State} (h : Steps s t) (hs : s.Ok)
    {A} (ht : HasType s.signature [] s.focus A) : t.Ok ∧ HasType t.signature [] t.focus A := by
  induction h with
  | refl => exact ⟨hs, ht⟩
  | step h _ ih =>
      obtain ⟨hu, ht'⟩ := preservation h hs ht
      exact ih hu ht'

end SourceRuntime.Runtime

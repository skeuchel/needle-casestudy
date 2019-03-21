Require Export BoilerplateSemantics.
Set Implicit Arguments.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {t : Tm} {T1 T2} :
  Value t → Typing empty t (tarr T1 T2) →
  exists t' T1', t = abs T1' t'.
Proof.
  intros val_t wt_t.
  depind wt_t; try contradiction.
  exists t, T1; reflexivity.
Qed.

Lemma can_form_tall {t : Tm} {T} :
  Value t → Typing empty t (tall T) →
  exists t', t = tabs t'.
Proof.
  intros val_t wt_t.
  depind wt_t; try contradiction.
  exists t; auto.
Qed.

Lemma progress {Γ t U} (wt: Typing Γ t U) :
  Γ = empty → Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; simpl; eauto using red, redds'.
  induction wt using ind_typing with
  (P0 := fun Γ ds Δ wds => Γ = empty → ValueH ds ∨ ∃ ds', redds' ds ds');
    intros...
  - inversion l.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt as [v1|[t1' r1]]...
    dependent destruction d...
  - destruct IHwt as [vt|[t1' r1]]...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt using ind_typing
  with (P0 := fun Γ ds Δ wds => ∀ ds', redds' ds ds' → DTyping Γ ds' Δ);
    intros t' rd; inversion rd; subst; eauto using Typing, DTyping.
  - dependent destruction wt1; eauto using subst_evar_typing.
  - dependent destruction wt; eauto using subst_etvar_typing.
  - dependent destruction d; auto.
  - dependent destruction d; eauto.
    rewrite (DTyping_bind_lengthExt d).
    rewrite extend_append in *.
    eapply T_Let; eauto using subst_evar_dtyping, subst_evar_typing_ind,
                  subst_evar, weaken_subst_evar.
Qed.

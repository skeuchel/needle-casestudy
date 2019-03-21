Require Export BoilerplateSemantics.
Set Implicit Arguments.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tarr T1 T2)) :
  ∃ t2, t = abs T1 t2.
Proof.
  depind wt; try contradiction; exists t; reflexivity.
Qed.

Lemma can_form_tall {Γ t T} (v: Value t) (wt: Typing Γ t (tall T)) :
  ∃ t1, t = tabs t1.
Proof.
  depind wt; try contradiction; exists t; reflexivity.
Qed.

Lemma can_form_texist {Γ t T} (v: Value t) (wt: Typing Γ t (texist T)) :
  ∃ T11 t12, t = pack T11 t12 (texist T).
Proof.
  depind wt; try contradiction; exists U, t2; reflexivity.
Qed.

Lemma progress {t U} (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof with try (subst; eauto using red).
  depind wt; simpl; auto.
  - inversion H.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt as [v1|[t1' r1]]...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct (can_form_texist v1 wt1) as [? [? ?]]...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - dependent destruction wt1; eauto using subst_evar_typing.
  - dependent destruction wt; eauto using subst_etvar_typing.
  - inversion wt1; subst; clear wt1.
    rewrite tsubstTm_substTm0_comm.
    rewrite tsubstTm_tshiftTm_reflection.
    eapply subst_evar_typing; eauto.
    rewrite <- (tsubstTy_tshiftTy_reflection T11 T2).
    eapply subst_etvar_typing; eauto.
Qed.

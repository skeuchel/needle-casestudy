Require Import Coq.omega.Omega.
Require Export BoilerplateSemantics.
Set Implicit Arguments.

(******************************************************************************)
(* Reflexivity, transitivity and narrowing                                    *)
(******************************************************************************)

Lemma sub_refl {Γ T} (wfT: wfTy Γ T) : Sub Γ T T.
Proof.
  induction wfT; eauto using Sub.
Qed.

Inductive narrow : nat → Env → Env → Prop :=
  | nw_here {Γ T1 T2} :
      Sub Γ T2 T1 → narrow 0 (etvar Γ T1) (etvar Γ T2)
  | nw_evar {X Γ1 Γ2 T} :
      narrow X Γ1 Γ2 → narrow X (evar Γ1 T) (evar Γ2 T)
  | nw_etvar {X Γ1 Γ2 T} :
      narrow X Γ1 Γ2 → narrow (S X) (etvar Γ1 T) (etvar Γ2 T).
Hint Constructors narrow.

Lemma narrow_lookup_etvar_eq {X Γ1 Γ2} (nw : narrow X Γ1 Γ2) :
  ∃ T1 T2, lookup_etvar Γ1 X T1 ∧ lookup_etvar Γ2 X T2 ∧ Sub Γ2 T2 T1.
Proof with destruct_conjs; repeat split; eauto.
  induction nw; intros.
  - exists (tshiftTy O T1),(tshiftTy O T2)...
  - destruct IHnw as (T1 & T2 & ?); exists T1, T2...
  - destruct IHnw as (T1 & T2 & ?); exists (tshiftTy O T1),(tshiftTy O T2)...
Qed.

Lemma narrow_lookup_etvar_ne {X Γ1 Γ2} (nw: narrow X Γ1 Γ2) :
  ∀ {T1 Y}, X ≠ Y → lookup_etvar Γ1 Y T1 → lookup_etvar Γ2 Y T1.
Proof.
  induction nw; inversion 2; subst; simpl; intuition.
Qed.

Lemma narrow_wf_ty {X Γ1 Γ2} (nw : narrow X Γ1 Γ2) :
  ∀ {T}, wfTy Γ1 T → wfTy Γ2 T.
Proof.
  intros t wT; revert X Γ2 nw.
  induction wT; simpl; intros Y ? ?; eauto.
  - case (eq_nat_dec X Y); intros; subst; simpl.
    + pose proof (narrow_lookup_etvar_eq nw); destruct_conjs; eauto.
    + eauto using narrow_lookup_etvar_ne.
Qed.

Lemma narrow_wf_env {X Γ1 Γ2} (nw : narrow X Γ1 Γ2) : wf_env Γ1 → wf_env Γ2.
Proof.
  induction nw; inversion 1; subst; simpl; eauto using narrow_wf_ty.
Qed.

Definition Trans Q :=
  ∀ Γ S T, wf_env Γ → Sub Γ S Q → Sub Γ Q T → Sub Γ S T.

Definition Narrow Q :=
  ∀ Γ1 Γ2 Y, wf_env Γ1 → narrow Y Γ1 Γ2 →
    lookup_etvar Γ1 Y Q → ∀ S T, Sub Γ1 S T → Sub Γ2 S T.

Lemma trans_case Q
  (hypT : ∀ R, size R < size Q → Trans R)
  (hypN : ∀ R, size R < size Q → Narrow R) :
  Trans Q.
Proof with simpl; eauto; try omega.
  intros Γ S T wΓ subSQ subQT; revert T subQT.
  induction subSQ; intros; auto.
  - dependent destruction subQT; constructor; auto.
  - eapply SA_Trans_TVar; eauto.
  - dependent destruction subQT; simpl; constructor...
    + apply (hypT T1)...
    + apply (hypT T2)...
  - assert (wf_env (etvar Γ T1)) by eauto.
    assert (wfTy (etvar Γ T1) S2) by eauto.
    assert (wfTy (etvar Γ S1) S2) by eauto using replace_etvar_wfty.
    dependent destruction subQT; constructor...
    + apply (hypT T1)...
    + apply (hypT T2)...
      refine (hypN _ _ _ _ _ _ (nw_here subQT1) gb_here _ _ subSQ2);
        try rewrite tshift_preserves_size...
Qed.

Lemma narrow_case Q (hyp : ∀ (R : Ty), size R = size Q → Trans R) :
  Narrow Q.
Proof.
  intros Γ1 Γ2 Y wΓ nw gb U T subUT; revert Q hyp Γ2 Y wΓ nw gb.
  induction subUT; intros.
  - apply SA_Top; eauto using narrow_wf_ty.
  - eapply SA_Refl_TVar; eauto using narrow_wf_ty.
  - case (eq_nat_dec X Y); intros; subst.
    + destruct (narrow_lookup_etvar_eq nw) as [T1 [T2 [gb1 [gb2 sub]]]].
      pose proof (lookup_etvar_functional gb H).
      pose proof (lookup_etvar_functional gb gb1).
      apply (hyp U); repeat subst; eauto using narrow_wf_env.
      apply (SA_Trans_TVar gb2 sub); eauto.
    + apply (SA_Trans_TVar (U := U)); eauto.
      apply (narrow_lookup_etvar_ne nw); auto.
  - constructor; eauto.
  - constructor; eauto.
    refine (IHsubUT2 _ _ _ _ _ (nw_etvar nw) (gb_bound gb));
      try rewrite tshift_preserves_size; auto.
Qed.

Lemma trans_and_narrow Q : Trans Q ∧ Narrow Q.
Proof.
  induction Q using sizeind; intros; split.
  apply trans_case; apply H; auto.
  apply narrow_case; intros R eq.
  apply trans_case; rewrite eq; apply H; auto.
Qed.

Lemma sub_trans {Q Γ S T} (wΓ: wf_env Γ) : Sub Γ S Q → Sub Γ Q T → Sub Γ S T.
Proof.
  apply (trans_and_narrow); auto.
Qed.

Lemma narrow_sub {X Γ1 Γ2 S T} (wΓ1: wf_env Γ1) (nw: narrow X Γ1 Γ2) :
  Sub Γ1 S T → Sub Γ2 S T.
Proof.
  destruct (narrow_lookup_etvar_eq nw); destruct_conjs.
  eapply trans_and_narrow; eauto.
Qed.

Lemma narrow_lookup_evar {X Γ1 Γ2} (nw: narrow X Γ1 Γ2) :
  ∀ {T x}, lookup_evar Γ1 x T → lookup_evar Γ2 x T.
Proof.
  induction nw; inversion 1; subst; simpl; intuition.
Qed.

Lemma typing_narrow {Γ1 t T} (wΓ1: wf_env Γ1) (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, narrow X Γ1 Γ2 → Typing Γ2 t T.
Proof.
  induction wt; simpl; intros; econstructor;
    eauto using narrow_lookup_evar, narrow_sub, narrow_wf_ty.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {t T1 T2} (v: Value t) (wt: Typing empty t (tarr T1 T2)) :
  ∃ T1' t2, t = abs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; eauto; inversion H0.
Qed.

Lemma can_form_tall {t T1 T2} (v: Value t) (wt: Typing empty t (tall T1 T2)) :
  ∃ T1' t2, t = tabs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; eauto; inversion H0.
Qed.

Lemma progress {t U} (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; eauto using red.
  depind wt; simpl; auto.
  - inversion H.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma t_abs_inversion {Γ t T0 T1} (wΓ: wf_env Γ) (wt: Typing Γ (abs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tarr T2 T3) → Sub Γ T2 T1 ∧ Typing (evar Γ T1) t T3.
Proof.
  depind wt.
  - inversion 1; eauto using T_Sub.
  - eauto using sub_trans.
Qed.

Lemma t_tabs_inversion {Γ t S T} (wΓ: wf_env Γ) (wt: Typing Γ (tabs T t) S) :
  ∀ {S1 S2}, Sub Γ S (tall S1 S2) → Sub Γ S1 T ∧ Typing (etvar Γ S1) t S2.
Proof.
  depind wt.
  - inversion 1; subst; split; eauto using T_Sub, typing_narrow.
  - eauto using sub_trans.
Qed.

Lemma preservation {Γ t U} (wΓ: wf_env Γ) (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - destruct (t_abs_inversion wΓ wt1 (sub_refl (typing_wf wΓ wt1))).
    eauto using subst_evar_typing , T_Sub.
  - destruct (t_tabs_inversion wΓ wt (sub_refl (typing_wf wΓ wt))).
    refine (subst_etvar_typing _ H1 (tse_here _ H)); eauto.
Qed.

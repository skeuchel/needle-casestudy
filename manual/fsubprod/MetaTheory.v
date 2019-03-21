Require Import Coq.omega.Omega.
Require Export BoilerplateSemantics.

(******************************************************************************)
(* Reflexivity, transitivity and narrowing                                    *)
(******************************************************************************)

Lemma sub_refl {Γ T} (wfT: wfTy Γ T) : Sub Γ T T.
Proof.
  induction wfT; eauto using Sub.
Qed.

Inductive narrow : nat → Env → Env → Prop :=
  | nw_here {Γ T1 T2} :
      Sub Γ T2 T1 → narrow O (etvar Γ T1) (etvar Γ T2)
  | nw_evar {X Γ1 Γ2 T} :
      narrow X Γ1 Γ2 → narrow X (evar Γ1 T) (evar Γ2 T)
  | nw_etvar {X Γ1 Γ2 T} :
      narrow X Γ1 Γ2 → narrow (S X) (etvar Γ1 T) (etvar Γ2 T).
Hint Constructors narrow.

Lemma weaken_narrow Δ :
  ∀ {X Γ1 Γ2}, narrow X Γ1 Γ2 → narrow X (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  induction Δ; simpl; intros; try constructor; auto.
Qed.

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
  - dependent destruction subQT; simpl; constructor...
    + apply (hypT T1)...
    + apply (hypT T2)...
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
  - constructor; eauto.
Qed.

Lemma sizeind (P : Ty → Prop) (step: ∀ T, (∀ S, size S < size T → P S) → P T) :
  ∀ T, P T.
Proof.
  cut (forall n T, size T <= n → P T); eauto.
  induction n; intros; apply step; intros; try apply IHn; omega.
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

Lemma narrow_ptyping {Γ1 p T Δ} (wΓ1: wf_env Γ1) (wp: PTyping Γ1 p T Δ) :
  ∀ {X Γ2}, narrow X Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; simpl; intros; econstructor; eauto using narrow_wf_ty.
  - assert (wf_env (extend Γ Δ1)) by apply (ptyping_wf wΓ1 wp1).
    eapply IHwp2; eauto using weaken_narrow.
Qed.

Lemma narrow_lookup_evar {X Γ1 Γ2} (nw: narrow X Γ1 Γ2) :
  ∀ {T x}, lookup_evar Γ1 x T → lookup_evar Γ2 x T.
Proof.
  induction nw; inversion 1; subst; simpl; intuition.
Qed.

Lemma narrow_typing {Γ1 t T} (wΓ1: wf_env Γ1) (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, narrow X Γ1 Γ2 → Typing Γ2 t T.
Proof.
  induction wt; simpl; intros; econstructor;
  eauto using narrow_lookup_evar, narrow_sub, narrow_wf_ty, narrow_ptyping.
  - assert (wf_env (extend Γ Δ)) by apply (ptyping_wf wΓ1 H).
    eauto using weaken_narrow.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tvar {Γ t X} (v: Value t) (wt: Typing Γ t (tvar X)) : False.
Proof.
  depind wt; auto.
  depind H; eauto.
Qed.

Lemma can_form_tarr {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tarr T1 T2)) :
  ∃ T1' t2, t = abs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
Qed.

Lemma can_form_tall {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tall T1 T2)) :
  ∃ T1' t2, t = tabs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion H; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
Qed.

Lemma can_form_tprod {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tprod T1 T2)) :
  ∃ t1 t2, t = prod t1 t2 ∧ Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt; try contradiction.
  - exists t1, t2; auto.
  - inversion H; subst.
    + elimtype False; eauto using can_form_tvar.
    + destruct (IHwt S1 S2 v eq_refl) as (t1 & t2 & eq & wt1 & wt2).
      exists t1, t2; eauto using T_Sub.
Qed.

Lemma matching_defined {Γ p T1 Δ} (wp: PTyping Γ p T1 Δ) :
  ∀ {t1}, Value t1 → Typing Γ t1 T1 → ∀ t2, ∃ t2', Match p t1 t2 t2'.
Proof.
  induction wp; intros t1 v1 wt1 t2.
  - exists (substTm sub_here t1 t2).
    refine M_Var.
  - destruct (can_form_tprod v1 wt1) as (t11 & t12 & eq & wt11 & wt12); subst.
    destruct v1 as [v11 v12].
    apply (weaken_typing Δ1) in wt12.
    assert (val12' : Value (weakenTm t12 (lengthExt Δ1)))
       by (apply weaken_value; auto).
    destruct (IHwp2 (weakenTm t12 (lengthExt Δ1)) val12' wt12 t2) as [t2' m2].
    destruct (IHwp1 _ v11 wt11 t2') as [t2'' m1].
    rewrite <- (PTyping_bindPat_lengthExt wp1) in m2.
    exists t2''.
    exact (M_Prod m2 m1).
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
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct (matching_defined H v1 wt1 t2)...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma t_abs_inversion {Γ t T0 T1} (wΓ: wf_env Γ) (wt: Typing Γ (abs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tarr T2 T3) → Sub Γ T2 T1 ∧ Typing (evar Γ T1) t T3.
Proof.
  depind wt.
  - inversion 1; eauto using T_Sub, shift_evar_sub.
  - eauto using sub_trans.
Qed.

Lemma t_tabs_inversion {Γ t T0 T1} (wΓ: wf_env Γ) (wt: Typing Γ (tabs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tall T2 T3) → Sub Γ T2 T1 ∧ Typing (etvar Γ T2) t T3.
Proof.
  depind wt.
  - inversion 1; subst; split; eauto using T_Sub, narrow_typing.
  - eauto using sub_trans.
Qed.

Lemma t_prod_inversion {Γ t1 t2 T} (wΓ: wf_env Γ) (wt: Typing Γ (prod t1 t2) T) :
  ∀ {T1 T2}, Sub Γ T (tprod T1 T2) → Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt.
  - inversion 1; eauto using T_Sub, narrow_typing.
  - eauto using sub_trans.
Qed.

Lemma local_preservation_lett {p t1 t2 t2'} (m: Match p t1 t2 t2') :
  ∀ {Γ T1 T2 Δ}, wf_env Γ → PTyping Γ p T1 Δ → Typing Γ t1 T1 →
    Typing (extend Γ Δ) t2 T2 →
    Typing Γ t2' T2.
Proof.
  induction m; intros Γ T1 T2 Δ wΓ wp wt1 wt2.
  - dependent destruction wp; simpl in *.
    eauto using subst_evar_typing.
  - dependent destruction wp.
    destruct (t_prod_inversion wΓ wt1 (sub_refl (typing_wf wΓ wt1))).
    rewrite (PTyping_bindPat_lengthExt wp1) in IHm1.
    rewrite extend_append in wt2.
    eauto using weaken_typing.
Qed.

Lemma preservation {Γ t U} (wΓ: wf_env Γ) (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - destruct (t_abs_inversion wΓ wt1 (sub_refl (typing_wf wΓ wt1))).
    eauto using subst_evar_typing, T_Sub.
  - destruct (t_tabs_inversion wΓ wt (sub_refl (typing_wf wΓ wt))).
    assert (wf_env (etvar Γ T11)); eauto using subst_etvar_typing.
  - eauto using local_preservation_lett.
Qed.

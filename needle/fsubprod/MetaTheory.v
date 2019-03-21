Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export DeclarationEvaluation.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_value {t} :
  ∀ {c}, Value t → Value (shiftTm c t).
Proof.
  induction t; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma tshift_value {t} :
  ∀ {c}, Value t → Value (tshiftTm c t).
Proof.
  induction t; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u as [|[]]; simpl; auto using shift_value, tshift_value.
Qed.

(******************************************************************************)
(* Reflexivity, transitivity and narrowing                                    *)
(******************************************************************************)

Lemma sub_refl {Γ T} (wfT: wfTy (domainEnv Γ) T) : Sub Γ T T.
Proof.
  depind wfT; simpl; econstructor; eauto with wf.
Qed.

Lemma narrow_lookup_etvar_ne {Γ T1 T2 Δ} :
  ∀ {X U}, X ≠ (weakenIndexty I0 (domainEnv Δ)) →
    lookup_etvar (appendEnv (etvar Γ T1) Δ) X U →
    lookup_etvar (appendEnv (etvar Γ T2) Δ) X U.
Proof.
  induction Δ; inversion 2; isimpl; try constructor; isimpl; intuition.
  - apply IHΔ; congruence.
Qed.

Definition Trans Q :=
  ∀ Γ S T, Sub Γ S Q → Sub Γ Q T → Sub Γ S T.

Definition Narrow Q :=
  ∀ Γ Δ S T, Sub (appendEnv (etvar Γ Q) Δ) S T →
    ∀ R, Sub Γ R Q → Sub (appendEnv (etvar Γ R) Δ) S T.

Lemma trans_case Q
  (hypT : ∀ R, size_Ty R < size_Ty Q → Trans R)
  (hypN : ∀ R, size_Ty R < size_Ty Q → Narrow R) :
  Trans Q.
Proof with simpl; eauto with infra; try omega.
  intros Γ S T subSQ subQT; revert T subQT.
  induction subSQ; intros; auto.
  - dependent destruction subQT; constructor; auto.
  - eapply SA_Trans_TVar; eauto.
  - dependent destruction subQT; simpl; constructor; eauto with wf...
    + apply (hypT T1)...
    + apply (hypT T2)...
  - dependent destruction subQT; constructor; eauto with wf...
    + apply (hypT T1)...
    + apply (hypT T2)...
      refine (hypN T1 _ G2 empty _ _ subSQ2 _ subQT1)...
  - dependent destruction subQT; constructor; eauto with wf...
    + apply (hypT T1)...
    + apply (hypT T2)...
Qed.

Lemma narrow_case Q (hyp : ∀ (R : Ty), size_Ty R = size_Ty Q → Trans R) :
  Narrow Q.
Proof.
  intros Γ Δ U T subUT; depind subUT; intros R subQ.
  - apply SA_Top; isimpl; auto.
  - apply SA_Refl_TVar; isimpl; auto.
  - pose proof (Sub_wf_1 _ _ _ subQ) as wfQ.
    case (eq_index_dec X (weakenIndexty I0 (domainEnv Δ))); intros; subst.
    + pose proof (lookup_etvar_functional _ lk _ (weaken_lookup_etvar_here Δ wfQ)).
      (* The lookup position X is the one that is being narrowed, so U is in
         fact Q weakened and hence we can use transitivity for U.  U. We can
         derive the goal like this:

                               Γ ⊢ R<:Q
                             ------------- shift_etvar_sub
                             Γ,x<:R ⊢ R<:Q
                            --------------- weaken_sub
         (x<:R) ∈ Γ,x<:R,Δ  Γ,x<:R,Δ ⊢ R<:Q
         ---------------------------------- SA_Trans  -------------- IH
                   Γ,x<:R,Δ ⊢ x<:U                    Γ,x:R,Δ ⊢ U<:T
         ----------------------------------------------------------- hyp U
                                 Γ,x<:R,Δ ⊢ x<:T
      *)
      apply (hyp U); subst; isimpl; auto.
      eapply SA_Trans_TVar; isimpl; eauto using weaken_Sub with wf infra.
    (* Just push the narrowing into the subtyping part. *)
    + eapply SA_Trans_TVar; isimpl; eauto using narrow_lookup_etvar_ne.
  - constructor; auto.
  - constructor; auto; apply (IHsubUT2 (etvar Δ T1) _ Q); auto.
  - constructor; auto.
Qed.

Lemma sub_trans_and_narrow Q : Trans Q ∧ Narrow Q.
Proof.
  induction Q using (sizeind size_Ty); intros; split.
  - apply trans_case; apply H; auto.
  - apply narrow_case; intros R eq.
    apply trans_case; rewrite eq; apply H.
Qed.

Lemma sub_trans {Q Γ S T} : Sub Γ S Q → Sub Γ Q T → Sub Γ S T.
Proof.
  intros; eapply sub_trans_and_narrow; eauto.
Qed.

Lemma sub_narrow {Γ Δ Q R S T} (subQ: Sub Γ R Q) :
  Sub (appendEnv (etvar Γ Q) Δ) S T → Sub (appendEnv (etvar Γ R) Δ) S T.
Proof.
  intros; eapply sub_trans_and_narrow; eauto.
Qed.

Lemma lookup_evar_narrow {Γ Δ Q R} :
  ∀ {x T}, lookup_evar (appendEnv (etvar Γ Q) Δ) x T →
           lookup_evar (appendEnv (etvar Γ R) Δ) x T.
Proof.
  induction Δ; inversion 1; isimpl; constructor; isimpl; eauto with wf.
Qed.

Lemma ptyping_narrow {Γ} Δ {Q R p T pΔ} (subQ: Sub Γ R Q) :
  PTyping (appendEnv (etvar Γ Q) Δ) p T pΔ →
  PTyping (appendEnv (etvar Γ R) Δ) p T pΔ.
Proof.
  intro wt; depind wt; econstructor; isimpl; eauto.
  - specialize (IHwt2 Γ (appendEnv Δ G) Q); isimpl; auto.
Qed.

Lemma typing_narrow {Γ} Δ {Q R t T} (subQ: Sub Γ R Q) :
  Typing (appendEnv (etvar Γ Q) Δ) t T → Typing (appendEnv (etvar Γ R) Δ) t T.
Proof.
  intro wt; depind wt; eauto using Typing, lookup_evar_narrow, sub_narrow.
  - eapply T_Var; eauto using lookup_evar_narrow with infra.
  - eapply T_Abs; isimpl; eauto.
    refine (IHwt Γ (evar Δ T1) _ _ eq_refl); auto.
  - eapply T_Tabs; isimpl; eauto.
    refine (IHwt Γ (etvar _ _) _ _ eq_refl); auto.
  - specialize (IHwt2 Γ (appendEnv Δ G1) Q).
    eapply T_Let; isimpl; eauto using ptyping_narrow.
Qed.

Lemma typing_narrow0 {Γ Q R t T} (subQ: Sub Γ R Q) :
  Typing (etvar Γ Q) t T → Typing (etvar Γ R) t T.
Proof.
  apply (typing_narrow empty subQ).
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Instance obligation_Env_var_ty : Obligation_Env_var_ty.
Proof.
  constructor; intros; eapply SA_Trans_TVar; eauto using sub_refl with infra.
Qed.

Instance obligation_Env_reg_Sub : Obligation_Env_reg_Sub.
Proof.
  constructor; intros; simpl; eauto using sub_refl, sub_trans.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tvar {Γ t X} (v: Value t) (wt: Typing Γ t (tvar X)) : False.
Proof.
  depind wt; auto.
  depind jm17; eauto.
Qed.

Lemma can_form_tarr {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tarr T1 T2)) :
  ∃ T1' t2, t = abs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion jm17; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
Qed.

Lemma can_form_tall {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tall T1 T2)) :
  ∃ T1' t2, t = tabs T1' t2.
Proof.
  depind wt; try contradiction.
  - exists T1, t; reflexivity.
  - inversion jm17; subst; eauto.
    + elimtype False; eauto using can_form_tvar.
Qed.

Lemma can_form_tprod {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tprod T1 T2)) :
  ∃ t1 t2, t = prod t1 t2 ∧ Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt; try contradiction.
  - exists t1, t2; auto.
  - inversion jm17; subst.
    + elimtype False; eauto using can_form_tvar.
    + destruct (IHwt S1 S2 v eq_refl) as (t1 & t2 & eq & wt1 & wt2).
      exists t1, t2; eauto using T_Sub.
Qed.

Lemma matching_defined {Γ p T1 Δ} (wp: PTyping Γ p T1 Δ) :
  ∀ {t1}, Value t1 → Typing Γ t1 T1 → ∀ t2, ∃ t2', Match p t1 t2 t2'.
Proof.
  induction wp; intros t1 v1 wt1 t2; isimpl.
  - exists (substTm X0 t1 t2).
    refine M_Var.
  - destruct (can_form_tprod v1 wt1) as (t11 & t12 & eq & wt11 & wt12); subst.
    destruct v1 as [v11 v12].
    apply (weaken_Typing G) in wt12.
    assert (val12' : Value (weakenTm t12 (domainEnv G)))
      by (apply weaken_value; auto).
    rewrite <- (domain_PTyping_bindPat _ _ _ _  wp1) in *.
    destruct (IHwp2 (weakenTm t12 (domainEnv G)) val12' wt12 t2) as [t2' m2].
    destruct (IHwp1 _ v11 wt11 t2') as [t2'' m1].
    rewrite (domain_PTyping_bindPat _ _ _ _ wp1) in m2.
    exists t2''.
    exact (M_Prod m2 m1).
Qed.

Lemma progress {t U} (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; eauto using red.
  depind wt; simpl; auto.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct (matching_defined wtp v1 wt1 t2)...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma t_abs_inversion {Γ t T0 T1} (wt: Typing Γ (abs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tarr T2 T3) → Sub Γ T2 T1 ∧ Typing (evar Γ T1) t T3.
Proof.
  depind wt.
  - inversion 1; eauto using T_Sub, shift_evar_Sub with shift.
  - eauto using sub_trans.
Qed.

Lemma t_tabs_inversion {Γ t T0 T1} (wt: Typing Γ (tabs T1 t) T0) :
  ∀ {T2 T3}, Sub Γ T0 (tall T2 T3) → Sub Γ T2 T1 ∧ Typing (etvar Γ T2) t T3.
Proof.
  depind wt.
  - inversion 1; subst; split; eauto using T_Sub, typing_narrow0.
  - eauto using sub_trans.
Qed.

Lemma t_prod_inversion {Γ t1 t2 T} (wt: Typing Γ (prod t1 t2) T) :
  ∀ {T1 T2}, Sub Γ T (tprod T1 T2) → Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt.
  - inversion 1; eauto using T_Sub, typing_narrow0.
  - eauto using sub_trans.
Qed.

Lemma local_preservation_lett {p t1 t2 t2'} (m: Match p t1 t2 t2') :
  ∀ {Γ T1 T2 Δ}, PTyping Γ p T1 Δ → Typing Γ t1 T1 →
    Typing (appendEnv Γ Δ) t2 (weakenTy T2 (domainEnv Δ)) →
    Typing Γ t2' T2.
Proof.
  induction m; intros Γ T1 T2 Δ wp wt1 wt2; isimpl.
  - dependent destruction wp; simpl in *.
    eauto using subst_evar_Typing with infra.
  - dependent destruction wp.
    destruct (t_prod_inversion wt1 (sub_refl (Typing_wf_1 _ _ _ wt1))); isimpl.
    eapply IHm2; eauto. eapply IHm1; eauto.
    rewrite <- (domain_PTyping_bindPat _ _ _ _ wp1) in *.
    eauto using weaken_Typing.
Qed.

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - destruct (t_abs_inversion wt1 (sub_refl (Typing_wf_1 _ _ _ wt1))).
    eauto using subst_evar_Typing, T_Sub with subst typeclass_instances.
  - destruct (t_tabs_inversion wt (sub_refl (Typing_wf_1 _ _ _ wt))).
    eauto using subst_etvar_Typing, T_Sub with infra typeclass_instances.
  - eapply local_preservation_lett; eauto; isimpl.
    rewrite <- (domain_PTyping_bindPat _ _ _ _ wtp) in *; eauto.
Qed.

Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.
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

Lemma can_form_tprod {Γ t T1 T2} (v: Value t) (wt: Typing Γ t (tprod T1 T2)) :
  ∃ t1 t2, t = prod t1 t2 ∧ Typing Γ t1 T1 ∧ Typing Γ t2 T2.
Proof.
  depind wt; try contradiction; exists t1, t2; auto.
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

Lemma local_preservation_lett {p t1 t2 t2'} (m: Match p t1 t2 t2') :
  ∀ {Γ T1 T2 Δ}, PTyping Γ p T1 Δ → Typing Γ t1 T1 →
    Typing (appendEnv Γ Δ) t2 (weakenTy T2 (domainEnv Δ)) → Typing Γ t2' T2.
Proof.
  induction m; intros Γ T1 T2 Δ wp wt1 wt2; isimpl.
  - dependent destruction wp; simpl in *.
    eauto using subst_evar_Typing with infra.
  - dependent destruction wp. dependent destruction wt1. isimpl.
    eapply IHm2; eauto.
    eapply IHm1; eauto.
    rewrite <- (domain_PTyping_bindPat _ _ _ _ wp1) in *.
    eauto using weaken_Typing with infra.
Qed.

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - dependent destruction wt1; eauto using subst_evar_Typing with subst.
  - dependent destruction wt; eauto using subst_etvar_Typing with subst.
  - eapply local_preservation_lett; eauto; isimpl.
    rewrite <- (domain_PTyping_bindPat _ _ _ _ wtp) in *; eauto.
Qed.

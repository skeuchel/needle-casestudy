Require Export BoilerplateSyntax.
Require Export SpecSemantics.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_etvar_sub {Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Sub Γ2 (tshiftTy c U) (tshiftTy c V).
Proof.
  induction sub; simpl; econstructor; eauto.
Qed.
Hint Resolve shift_etvar_sub.

Lemma shift_evar_sub {Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Sub Γ2 U V.
Proof.
  induction sub; simpl; econstructor; eauto.
Qed.
Hint Resolve shift_evar_sub.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; intros;
    try rewrite tshiftTy_tsubstTy_comm; econstructor; eauto.
Qed.
Hint Resolve shift_etvar_typing.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; econstructor; eauto.
Qed.
Hint Resolve shift_evar_typing.

(******************************************************************************)
(* Substitution lemmas 1                                                      *)
(******************************************************************************)

Inductive subst_etvar (S: Ty) : nat → Env → Env → Prop :=
  | tse_here {Γ B} :
      wfTy Γ S → Sub Γ S B →
      subst_etvar S 0 (etvar Γ B) Γ
  | tse_evar {X Γ1 Γ2 T} :
      subst_etvar S X Γ1 Γ2 →
      subst_etvar S X (evar Γ1 T) (evar Γ2 (tsubstTy X S T))
  | tse_etvar {Γ1 Γ2 X T} :
      subst_etvar S X Γ1 Γ2 →
      subst_etvar S (1 + X) (etvar Γ1 T) (etvar Γ2 (tsubstTy X S T)).
Hint Constructors subst_etvar.

Lemma subst_etvar_lookup_etvar_wfty {S X Γ1 Γ2} (esub: subst_etvar S X Γ1 Γ2) :
  ∀ {Y T}, lookup_etvar Γ1 Y T → wfTy Γ2 (tsubstIndex X S Y).
Proof.
  induction esub; inversion 1; subst; simpl; eauto.
Qed.
Hint Resolve subst_etvar_lookup_etvar_wfty.

Lemma subst_etvar_wfty {S Γ1 T} (wfT: wfTy Γ1 T) :
  ∀ {X Γ2}, subst_etvar S X Γ1 Γ2 → wfTy Γ2 (tsubstTy X S T).
Proof.
  induction wfT; simpl; intros; try econstructor; eauto.
Qed.
Hint Resolve subst_etvar_wfty.

Lemma subst_etvar_wf_env {S X Γ1 Γ2} (esub: subst_etvar S X Γ1 Γ2) :
  wf_env Γ1 → wf_env Γ2.
Proof.
  induction esub; inversion 1; subst; simpl; eauto.
Qed.

(******************************************************************************)
(* Well-formedness                                                            *)
(******************************************************************************)

Ltac specIH :=
  match goal with
    | H: wf_env ?G, IH : wf_env ?G → _ |- _ =>
      specialize (IH H); destruct_conjs
  end.

Lemma sub_wf {Γ U V} (sub: Sub Γ U V) (wΓ: wf_env Γ)  :
  wfTy Γ U ∧ wfTy Γ V.
Proof.
  induction sub; repeat specIH; eauto.
  - assert (wf_env (etvar Γ T1)) by eauto; specIH.
    eauto using replace_etvar_wfty.
Qed.

Hint Extern 2 (wfTy _ _) =>
  match goal with
    | wG: wf_env ?G, sub: Sub ?G _ _ |- _ =>
      destruct (sub_wf sub wG); clear sub
  end.

Lemma typing_wf {Γ t T} (wΓ: wf_env Γ) (wt: Typing Γ t T) : wfTy Γ T.
Proof.
  induction wt; simpl; repeat specIH; try econstructor; eauto.
  - assert (wf_env (evar Γ T1)) by eauto; eauto using strengthen_evar_wfty.
Qed.

(******************************************************************************)
(* Substitution lemmas 2                                                      *)
(******************************************************************************)

Variable sub_refl : forall {Γ T} (wfT: wfTy Γ T), Sub Γ T T.
Variable sub_trans :
  forall {Q Γ S T} (wΓ: wf_env Γ), Sub Γ S Q → Sub Γ Q T → Sub Γ S T.

Inductive subst_evar (s: Tm) : Subst → Env → Env → Prop :=
  | se_here {Γ S} :
      Typing Γ s S →
      subst_evar s sub_here (evar Γ S) Γ
  | se_evar {x Γ1 Γ2 T} :
      subst_evar s x Γ1 Γ2 →
      subst_evar s (sub_var x) (evar Γ1 T) (evar Γ2 T)
  | se_etvar {x Γ1 Γ2 T} :
      subst_evar s x Γ1 Γ2 →
      subst_evar s (sub_bound x) (etvar Γ1 T) (etvar Γ2 T).
Hint Constructors subst_evar.

Lemma subst_evar_lookup_etvar {s X Γ1 Γ2} (esub: subst_evar s X Γ1 Γ2) :
  ∀ {Y T}, lookup_etvar Γ1 Y T → lookup_etvar Γ2 Y T.
Proof.
  induction esub; inversion 1; subst; simpl; eauto.
Qed.
Hint Resolve subst_evar_lookup_etvar.

Lemma subst_evar_wfty {s Γ1 T} (wfT: wfTy Γ1 T) :
  ∀ {X Γ2}, subst_evar s X Γ1 Γ2 → wfTy Γ2 T.
Proof.
  induction wfT; simpl; intros; econstructor; eauto.
Qed.
Hint Resolve subst_evar_wfty.

Lemma subst_etvar_lookup_etvar {S X Γ1 Γ2}
  (wΓ1: wf_env Γ1) (esub: subst_etvar S X Γ1 Γ2) :
  ∀ {Y T}, lookup_etvar Γ1 Y T → Sub Γ2 (tsubstIndex X S Y) (tsubstTy X S T).
Proof.
  induction esub; inversion wΓ1; inversion 1; subst; simpl; intros;
    try rewrite tsubstTy_tshiftTy_reflection;
    try rewrite tsubstTy_tshiftTy_comm; eauto using Sub, sub_refl.
Qed.

Lemma subst_etvar_sub {S Γ1 U V} (wΓ1: wf_env Γ1) (sub: Sub Γ1 U V) :
  ∀ {X Γ2}, subst_etvar S X Γ1 Γ2 → Sub Γ2 (tsubstTy X S U) (tsubstTy X S V).
Proof.
  induction sub; simpl; intros; try (econstructor; eauto; fail).
  - apply sub_refl; eauto using subst_etvar_lookup_etvar_wfty.
  - apply (sub_trans (Q := tsubstTy X0 S U));
      eauto using subst_etvar_wf_env, subst_etvar_lookup_etvar.
Qed.

Lemma subst_etvar_lookup_evar {S X Γ1 Γ2} (esub: subst_etvar S X Γ1 Γ2) :
  ∀ {x T}, lookup_evar Γ1 x T → lookup_evar Γ2 x (tsubstTy X S T).
Proof.
  induction esub; inversion 1; subst; simpl; intros;
    try rewrite tsubstTy_tshiftTy_reflection;
    try rewrite tsubstTy_tshiftTy_comm;
    try constructor; auto.
Qed.

Lemma subst_etvar_typing {S Γ1 t T} (wΓ1: wf_env Γ1) (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar S X Γ1 Γ2 → Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt; simpl; intros; try rewrite tsubstTy_tsubstTy_comm; econstructor;
    eauto using subst_etvar_lookup_evar, subst_etvar_wfty, subst_etvar_sub.
Qed.

Lemma subst_evar_sub {s Γ1 U V} (sub: Sub Γ1 U V) :
  ∀ {x Γ2}, subst_evar s x Γ1 Γ2 → Sub Γ2 U V.
Proof.
  induction sub; simpl; intros; try (econstructor; eauto; fail).
Qed.

Lemma subst_evar_lookup_evar {s x Γ1 Γ2} (sub: subst_evar s x Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x s y) T.
Proof.
  induction sub; inversion 1; subst; simpl; intros; eauto using T_Var.
Qed.

Lemma subst_evar_typing {s Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar s x Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; simpl; eauto using subst_evar_lookup_evar;
    econstructor; eauto using subst_evar_sub.
Qed.

Require Export SpecSemantics.
Require Export BoilerplateSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma PTyping_bindPat_lengthExt {Γ p T Δ} (wp: PTyping Γ p T Δ) :
  bindPat p = lengthExt Δ.
Proof.
  induction wp; simpl; try rewrite lengthExt_append; congruence.
Qed.

Lemma shift_evar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; econstructor; eauto.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; simpl; intros; try (econstructor; eauto; fail).
  - rewrite (PTyping_bindPat_lengthExt H).
    econstructor; eauto using shift_evar_ptyping.
Qed.

Lemma weaken_typing {Γ} Δ :
  ∀ {t T}, Typing Γ t T → Typing (extend Γ Δ) (weakenTm t (lengthExt Δ)) T.
Proof.
  induction Δ; simpl; eauto using shift_evar_typing.
Qed.

Lemma shift_value {t} :
  ∀ {c}, Value t → Value (shiftTm c t).
Proof.
  induction t; simpl; intros; try contradiction; destruct_conjs; auto.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u; simpl; auto using shift_value.
Qed.


(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Inductive subst_evar (Γ: Env) (U : Ty) : nat → Env → Env → Prop :=
  | subst_evar_here :
      subst_evar Γ U 0 (evar Γ U) Γ
  | subst_evar_there_evar {Γ1 Γ2 : Env} {x T} :
      subst_evar Γ U x     Γ1           Γ2 →
      subst_evar Γ U (S x) (evar Γ1 T) (evar Γ2 T).
Hint Constructors subst_evar.

Lemma weaken_subst_evar {Γ U} (Δ : Ext) :
  ∀ {x Γ1 Γ2},
    subst_evar Γ U x Γ1 Γ2 →
    subst_evar Γ U (lengthExt Δ + x) (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_subst_evar.

Lemma subst_evar_ptyping {Γ s S} (wts: Typing Γ s S)
  {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {x Γ2}, subst_evar Γ S x Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; simpl; econstructor; eauto.
Qed.

Lemma subst_evar_lookup_evar {Γ s S} (wt: Typing Γ s S)
  {x Γ1 Γ2} (esub: subst_evar Γ S x Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x s y) T.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_evar_typing.
Qed.

Lemma subst_evar_typing {Γ s S Γ1 t T} (wts: Typing Γ s S) (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar Γ S x Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; simpl; intros; eauto using subst_evar_lookup_evar;
    try (econstructor; eauto; fail).
  - rewrite (PTyping_bindPat_lengthExt H).
    eapply T_Let; eauto using subst_evar_ptyping.
Qed.

Require Export BoilerplateSyntax.
Require Export SpecSemantics.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma PTyping_bindPat_lengthExt {Γ p T Δ} (wp: PTyping Γ p T Δ) :
  bindPat p = lengthExt Δ.
Proof.
  induction wp; isimpl; try rewrite lengthExt_append; congruence.
Qed.

Lemma shift_etvar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → PTyping Γ2 p (tshiftTy c T) (tshiftExt c Δ).
Proof.
  induction wp; isimpl; econstructor; eauto.
Qed.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; isimpl; econstructor; eauto using shift_etvar_ptyping.
Qed.

Lemma shift_evar_ptyping {Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; econstructor; eauto.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; isimpl; try (econstructor; eauto; fail).
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

Inductive subst_etvar : nat → Ty → Env → Env → Prop :=
  | tse_here {Γ T} :
      wfTy Γ T → subst_etvar 0 T (etvar Γ) Γ
  | tse_var {Γ1 Γ2 T' T X} :
      subst_etvar X T' Γ1 Γ2 →
      subst_etvar X T' (evar Γ1 T) (evar Γ2 (tsubstTy X T' T))
  | tse_bound {Γ1 Γ2 X T'} :
      subst_etvar X T' Γ1 Γ2 →
      subst_etvar (S X) T' (etvar Γ1) (etvar Γ2).
Hint Constructors subst_etvar.

Lemma weaken_subst_etvar {T} (Δ : Ext) :
  ∀ {x Γ1 Γ2},
    subst_etvar x T Γ1 Γ2 →
    subst_etvar x T (extend Γ1 Δ) (extend Γ2 (tsubstExt x T Δ)).
Proof.
  induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_subst_etvar.

Lemma subst_etvar_lookup_etvar {X T' Γ1 Γ2} (esub: subst_etvar X T' Γ1 Γ2) :
  ∀ {Y}, lookup_etvar Γ1 Y → wfTy Γ2 (tsubstIndex X T' Y).
Proof.
  induction esub; inversion 1; simpl; eauto.
Qed.

Lemma subst_etvar_wfty {Γ1 T' T} (wT: wfTy Γ1 T) :
  ∀ {X Γ2}, subst_etvar X T' Γ1 Γ2 → wfTy Γ2 (tsubstTy X T' T).
Proof.
  induction wT; simpl; eauto using subst_etvar_lookup_etvar.
Qed.
Hint Resolve subst_etvar_wfty.

Lemma subst_etvar_lookup_evar  {X T' Γ1 Γ2} (esub: subst_etvar X T' Γ1 Γ2) :
  ∀ {x T}, lookup_evar Γ1 x T → lookup_evar Γ2 x (tsubstTy X T' T).
Proof.
  induction esub; inversion 1; isimpl; eauto.
Qed.
Hint Resolve subst_etvar_lookup_evar.

Inductive subst_evar : Subst → Tm → Env → Env → Prop :=
  | se_here {Γ s S} :
      Typing Γ s S → subst_evar sub_here s (evar Γ S) Γ
  | se_var {Γ1 Γ2 T s x} :
      subst_evar x s Γ1 Γ2 →
      subst_evar (sub_var x) s (evar Γ1 T) (evar Γ2 T)
  | se_bound {Γ1 Γ2 x s} :
      subst_evar x s Γ1 Γ2 →
      subst_evar (sub_bound x) s (etvar Γ1) (etvar Γ2).
Hint Constructors subst_evar.

Lemma weaken_subst_evar {t} (Δ : Ext) :
  ∀ {x Γ1 Γ2},
    subst_evar x t Γ1 Γ2 →
    subst_evar (weakenSubst (lengthExt Δ) x) t (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_subst_evar.

Lemma subst_evar_lookup_etvar {x s Γ1 Γ2} (esub: subst_evar x s Γ1 Γ2) :
  ∀ {Y}, lookup_etvar Γ1 Y → lookup_etvar Γ2 Y.
Proof.
  induction esub; inversion 1; simpl; eauto.
Qed.

Lemma subst_evar_wftyp {Γ1 T} (wT: wfTy Γ1 T) :
  ∀ {x s Γ2}, subst_evar x s Γ1 Γ2 → wfTy Γ2 T.
Proof.
  induction wT; simpl; eauto using subst_evar_lookup_etvar.
Qed.
Hint Resolve subst_evar_wftyp.

Lemma subst_etvar_ptyping {S Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {X Γ2}, subst_etvar X S Γ1 Γ2 →
    PTyping Γ2 p (tsubstTy X S T) (tsubstExt X S Δ).
Proof.
  induction wp; isimpl; econstructor; eauto.
Qed.

Lemma subst_etvar_typing {S Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar X S Γ1 Γ2 → Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt; isimpl; econstructor; eauto using subst_etvar_ptyping.
Qed.

Lemma subst_evar_lookup_evar {x t Γ1 Γ2} (esub: subst_evar x t Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x t y) T.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_evar_typing, shift_etvar_typing.
Qed.

Lemma subst_evar_ptyping {s Γ1 p T Δ} (wp: PTyping Γ1 p T Δ) :
  ∀ {x Γ2}, subst_evar x s Γ1 Γ2 → PTyping Γ2 p T Δ.
Proof.
  induction wp; econstructor; eauto.
Qed.

Lemma subst_evar_typing {s Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar x s Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; isimpl; eauto using subst_evar_lookup_evar; econstructor;
    try rewrite (PTyping_bindPat_lengthExt H); eauto using subst_evar_ptyping.
Qed.

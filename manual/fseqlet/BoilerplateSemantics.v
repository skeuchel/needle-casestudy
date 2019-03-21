Require Export SpecSemantics.
Require Export BoilerplateSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma DTyping_bind_lengthExt {Γ ds Δ} (wd : DTyping Γ ds Δ) :
  bind ds = lengthExt Δ.
Proof.
  induction wd; simpl; auto.
  - rewrite IHwd, lengthExt_append; simpl.
    reflexivity.
Qed.

Lemma shift_etvar_typing {Γ1 t T} (wt : Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ1 ds Δ wtd =>
           ∀ {c Γ2}, shift_etvar c Γ1 Γ2 →
             DTyping Γ2 (tshiftDecls c ds) (tshiftExt c Δ)); simpl; intros;
    try rewrite tshiftTy_tsubstTy_comm;
    try rewrite tshiftExt_append; econstructor;
    eauto using shift_etvar_wftyp, shift_etvar_lookup_evar, weakenshift_etvar.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
 ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt using ind_typing with
  (P0 := fun Γ1 ds Δ wtd =>
           ∀ {c Γ2}, shift_evar c Γ1 Γ2 →
             DTyping Γ2 (shiftDecls c ds) Δ); simpl; intros;
    econstructor; try erewrite DTyping_bind_lengthExt;
    eauto using shift_evar_lookup_evar, shift_evar_wftyp, weakenshift_evar.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

Inductive subst_etvar : nat → Ty → Env → Env → Prop :=
  | tse_here {Γ : Env} {T} :
      wfTy Γ T →
      subst_etvar O T (etvar Γ) Γ
  | tse_var {Γ1 : Env} {Γ2 : Env} {T' T} {X} :
      subst_etvar X T' Γ1 Γ2 →
      subst_etvar X T' (evar Γ1 T) (evar Γ2 (tsubstTy X T' T))
  | tse_etvar {Γ1 : Env} {Γ2 : Env} {X T'} :
      subst_etvar X T' Γ1 Γ2 →
      subst_etvar (S X) T' (etvar Γ1) (etvar Γ2).
Hint Constructors subst_etvar.

Lemma weaken_subst_etvar {Γ1 Γ2 : Env} {Δ : Ext} {X T'} :
  subst_etvar X T' Γ1 Γ2 →
  subst_etvar X T' (extend Γ1 Δ) (extend Γ2 (tsubstExt X T' Δ)).
Proof.
  revert X T' Γ1 Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_subst_etvar.

Lemma subst_etvar_lookup_etvar {Γ1 Γ2 : Env} {X T' Y} :
  subst_etvar X T' Γ1 Γ2 → lookup_etvar Γ1 Y →
  wfTy Γ2 (tsubstIndex X T' Y).
Proof.
  intros esub gb; revert Γ2 X esub.
  induction gb; intros; dependent destruction esub; simpl;
    auto using wf_tvar, weakening_etvar_wftyp, weakening_var_wftyp.
Qed.
Hint Resolve subst_etvar_lookup_etvar.


Lemma subst_etvar_wftyp_ind {Γ1 Γ2 : Env} {X T' T} :
  subst_etvar X T' Γ1 Γ2 → wfTy Γ1 T → wfTy Γ2 (tsubstTy X T' T).
Proof.
  intros esub st; revert Γ2 X T' esub.
  induction st; simpl; intros; eauto using wfTy, subst_etvar_lookup_etvar.
Qed.

Lemma subst_etvar_lookup_evar {Γ1 : Env} {Γ2 : Env} {X x T' T} :
  subst_etvar X T' Γ1 Γ2 → lookup_evar Γ1 x T →
  lookup_evar Γ2 x (tsubstTy X T' T).
Proof.
  intros sube gv; revert x T gv.
  induction sube; intros; dependent destruction gv; simpl;
    try rewrite tsubstTy_tshiftTy_reflection;
    try rewrite tsubstTy_tshiftTy_comm; try constructor; auto.
Qed.

Inductive subst_evar : Subst → Tm → Env → Env → Prop :=
  | se_here {Γ : Env} {t T} :
      Typing Γ t T →
      subst_evar sub_here t (evar Γ T) Γ
  | se_var {Γ1 Γ2 : Env} {T t} {x} :
      subst_evar x t Γ1 Γ2 →
      subst_evar (sub_var x) t (evar Γ1 T) (evar Γ2 T)
  | se_etvar {Γ1 Γ2 : Env} {x} {t} :
      subst_evar x t Γ1 Γ2 →
      subst_evar (sub_tvar x) t (etvar Γ1) (etvar Γ2).
Hint Constructors subst_evar.

Lemma weaken_subst_evar {Γ1 Γ2 : Env} {Δ : Ext} {x} {t} :
  subst_evar x t Γ1 Γ2 →
  subst_evar (weakenSubst (lengthExt Δ) x) t (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  revert x Γ1 Γ2.
  induction Δ; simpl; intros; try constructor; auto.
Qed.

Lemma subst_evar_lookup_etvar {Γ1 Γ2 : Env} {x t Y} :
  subst_evar x t Γ1 Γ2 → lookup_etvar Γ1 Y → lookup_etvar Γ2 Y.
Proof.
  intros sube gv; revert Y gv.
  induction sube; intros; dependent destruction gv; simpl;
    try constructor; auto.
Qed.

Lemma subst_evar_wftyp_ind {Γ1 Γ2 : Env} {x t T} :
  subst_evar x t Γ1 Γ2 → wfTy Γ1 T → wfTy Γ2 T.
Proof.
  intros esub st; revert Γ2 x t esub.
  induction st; simpl; eauto using subst_evar_lookup_etvar, wfTy.
Qed.

Lemma subst_evar_lookup_evar {Γ1 Γ2 : Env} {x t y T} :
  subst_evar x t Γ1 Γ2 → lookup_evar Γ1 y T → Typing Γ2 (substIndex x t y) T.
Proof.
  intros esub gv; revert Γ2 x esub.
  induction gv; intros; dependent destruction esub; simpl;
    eauto using T_Var, shift_evar_typing, shift_etvar_typing.
Qed.

Lemma subst_evar_typing_dtyping_ind :
  ∀ Γ1,
  (∀ {t T} (wt : Typing Γ1 t T),
    ∀ {x t' Γ2}, subst_evar x t' Γ1 Γ2 →
                 Typing Γ2 (substTm x t' t) T) ∧
  (∀ {ds Δ} (wtd : DTyping Γ1 ds Δ),
    ∀ {x t' Γ2}, subst_evar x t' Γ1 Γ2 →
                 DTyping Γ2 (substDecls x t' ds) Δ).
Proof.
  apply ind_typing_dtyping; simpl; intros; eauto using subst_evar_lookup_evar;
    try rewrite (DTyping_bind_lengthExt d); econstructor;
    eauto using subst_evar_wftyp_ind, weaken_subst_evar.
Qed.

Lemma subst_evar_typing_ind {Γ1 t T} (wt : Typing Γ1 t T) :
  ∀ {x t' Γ2}, subst_evar x t' Γ1 Γ2 → Typing Γ2 (substTm x t' t) T.
Proof. apply subst_evar_typing_dtyping_ind; auto. Qed.

Lemma subst_evar_typing {Γ : Env} {s S t T} :
  Typing Γ s S → Typing (evar Γ S) t T → Typing Γ (substTm sub_here s t) T.
Proof.
  intros wt_s wt_t; apply (subst_evar_typing_ind wt_t).
  constructor; auto.
Qed.

Lemma subst_evar_dtyping {Γ : Env} {s S ds Δ} :
  Typing Γ s S → DTyping (evar Γ S) ds Δ →
  DTyping Γ (substDecls sub_here s ds) Δ.
Proof.
  intros wt_s wt_ds.
  apply (proj2 (subst_evar_typing_dtyping_ind _) _ _ wt_ds).
  constructor; auto.
Qed.

Lemma subst_etvar_typing_dtyping_ind :
  ∀ Γ1,
  (∀ {t T} (wt : Typing Γ1 t T),
    ∀ {X T' Γ2}, subst_etvar X T' Γ1 Γ2 →
                 Typing Γ2 (tsubstTm X T' t) (tsubstTy X T' T)) /\
  (∀ {ds Δ} (wtd : DTyping Γ1 ds Δ),
    ∀ {X T' Γ2}, subst_etvar X T' Γ1 Γ2 →
                 DTyping Γ2 (tsubstDecls X T' ds) (tsubstExt X T' Δ)).
Proof.
  apply ind_typing_dtyping; simpl; intros;
    try rewrite tsubstTy_tsubstTy_comm;
    try rewrite tsubstExt_append; econstructor;
    eauto using subst_etvar_lookup_evar, subst_etvar_wftyp_ind.
Qed.

Lemma subst_etvar_typing :
  (∀ {Γ1 t T} (wt : Typing Γ1 t T),
    ∀ {X T' Γ2}, subst_etvar X T' Γ1 Γ2 →
                 Typing Γ2 (tsubstTm X T' t) (tsubstTy X T' T)).
Proof.
  apply subst_etvar_typing_dtyping_ind.
Qed.

Require Export BoilerplateSyntax.
Require Export SpecSemantics.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; intros; try (isimpl; econstructor; eauto; fail); simpl.
  - specialize (IHwt c Γ2 H1).
    isimpl; constructor; eauto.
  - specialize (IHwt2 (S c) (evar (etvar Γ2) (tshiftTy (S c) T12))).
    isimpl; econstructor; eauto.
Qed.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; intros; isimpl; econstructor; eauto.
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

Inductive subst_evar : hnat → Tm → Env → Env → Prop :=
  | se_here {Γ s S} :
      Typing Γ s S → subst_evar hn0 s (evar Γ S) Γ
  | se_var {Γ1 Γ2 T s x} :
      subst_evar x s Γ1 Γ2 →
      subst_evar (hsm x) s (evar Γ1 T) (evar Γ2 T)
  | se_bound {Γ1 Γ2 x s} :
      subst_evar x s Γ1 Γ2 →
      subst_evar (hsy x) s (etvar Γ1) (etvar Γ2).
Hint Constructors subst_evar.

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

Lemma subst_etvar_typing {T' Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar X T' Γ1 Γ2 →
    Typing Γ2 (tsubstTm X T' t) (tsubstTy X T' T).
Proof.
  induction wt; intros; try (isimpl; econstructor; eauto; fail); simpl.
  - specialize (IHwt X Γ2 H1).
    isimpl; constructor; eauto.
  - specialize (IHwt2 (S X) (evar (etvar Γ2) (tsubstTy (S X) T' T12))).
    isimpl; econstructor; eauto.
Qed.

Lemma subst_evar_lookup_evar {x t Γ1 Γ2} (esub: subst_evar x t Γ1 Γ2) :
  ∀ {y U}, lookup_evar Γ1 y U → Typing Γ2 (substIndex x t y) U.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using T_Var, shift_etvar_typing, shift_evar_typing.
Qed.

Lemma subst_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {x t' Γ2}, subst_evar x t' Γ1 Γ2 → Typing Γ2 (substTm x t' t) T.
Proof.
  induction wt; simpl; eauto using subst_evar_lookup_evar; econstructor; eauto.
Qed.

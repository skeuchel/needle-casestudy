Require Export SpecSemantics.
Require Export BoilerplateSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_etvar_kinding {Γ1 T K} (wT: Kinding Γ1 T K) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Kinding Γ2 (tshiftTy c T) K.
Proof.
  induction wT; simpl; econstructor; eauto.
Qed.

Lemma shift_etvar_tyeq {Γ1 S T K} (eqST: TyEq Γ1 S T K) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → TyEq Γ2 (tshiftTy c S) (tshiftTy c T) K.
Proof.
  induction eqST; simpl; intros; try rewrite tshiftTy_tsubstTy_comm;
    eauto using TyEq, shift_etvar_kinding.
Qed.
Hint Resolve shift_etvar_tyeq.

Lemma shift_etvar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → Typing Γ2 (tshiftTm c t) (tshiftTy c T).
Proof.
  induction wt; simpl; intros; try rewrite tshiftTy_tsubstTy_comm;
    econstructor; eauto using shift_etvar_kinding.
Qed.
Hint Resolve shift_etvar_typing.

Lemma shift_etvar_tred {Γ1 T U K} (tr: TRed Γ1 T U K) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → TRed Γ2 (tshiftTy c T) (tshiftTy c U) K.
Proof.
  induction tr; simpl; intros; try rewrite tshiftTy_tsubstTy_comm;
    econstructor; eauto using shift_etvar_kinding.
Qed.
Hint Resolve shift_etvar_tred.

Lemma shift_evar_kinding {Γ1 T K} (wT: Kinding Γ1 T K) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Kinding Γ2 T K.
Proof.
  induction wT; simpl; econstructor; eauto.
Qed.

Lemma shift_evar_tyeq {Γ1 S T K} (eqST: TyEq Γ1 S T K) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → TyEq Γ2 S T K.
Proof.
  induction eqST; simpl; eauto using TyEq, shift_evar_kinding.
Qed.
Hint Resolve shift_evar_tyeq.

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; simpl; econstructor; eauto using shift_evar_kinding.
Qed.
Hint Resolve shift_evar_typing.

Lemma remove_var_kinding {Γ2 T K} (wT: Kinding Γ2 T K) :
  ∀ {c Γ1}, shift_evar c Γ1 Γ2 → Kinding Γ2 T K → Kinding Γ1 T K.
Proof.
  induction wT; econstructor; eauto using remove_var_lookup_etvar.
Qed.

Lemma strengthening_var_kinding {Γ T' T K} :
  Kinding (evar Γ T') T K → Kinding Γ T K.
Proof.
  eauto using remove_var_kinding.
Qed.

(******************************************************************************)
(* Substitution lemmas.                                                       *)
(******************************************************************************)

Inductive subst_etvar : nat → Ty → Env → Env → Prop :=
  | subst_etvar_here {Γ T K} :
      Kinding Γ T K →
      subst_etvar 0 T (etvar Γ K) Γ
  | subst_etvar_there_evar {Γ1 Γ2 T T' X} :
      subst_etvar X T Γ1 Γ2 →
      subst_etvar X T (evar Γ1 T') (evar Γ2 (tsubstTy X T T'))
  | subst_etvar_there_etvar {Γ1 Γ2 X T K} :
      subst_etvar X T Γ1 Γ2 →
      subst_etvar (S X) T (etvar Γ1 K) (etvar Γ2 K).
Hint Constructors subst_etvar.

Lemma subst_etvar_lookup_evar {X T Γ1 Γ2} (esub: subst_etvar X T Γ1 Γ2) :
  ∀ {x T'}, lookup_evar Γ1 x T' → lookup_evar Γ2 x (tsubstTy X T T').
Proof.
  induction esub; inversion 1; subst; simpl;
    try rewrite tsubstTy_tshiftTy_reflection;
    try rewrite tsubstTy_tshiftTy_comm; eauto.
Qed.
Hint Resolve subst_etvar_lookup_evar.

Inductive subst_evar : Trace → Tm → Env → Env → Prop :=
  | subst_evar_here {Γ t T} :
      Typing Γ t T →
      subst_evar I0 t (evar Γ T) Γ
  | subst_evar_there_evar {Γ1 Γ2 T t x} :
      subst_evar x t Γ1 Γ2 →
      subst_evar (IV x) t (evar Γ1 T) (evar Γ2 T)
  | subst_evar_there_etvar {Γ1 Γ2 K x t} :
      subst_evar x t Γ1 Γ2 →
      subst_evar (IT x) t (etvar Γ1 K) (etvar Γ2 K).
Hint Constructors subst_evar.

Lemma subst_evar_lookup_etvar {x t Γ1 Γ2} (esub: subst_evar x t Γ1 Γ2) :
  ∀ {X K}, lookup_etvar Γ1 X K → lookup_etvar Γ2 X K.
Proof.
  induction esub; inversion 1; subst; simpl; eauto.
Qed.
Hint Resolve subst_evar_lookup_etvar.

Lemma subst_etvar_lookup_etvar {X S Γ1 Γ2} (esub: subst_etvar X S Γ1 Γ2) :
  ∀ {Y K}, lookup_etvar Γ1 Y K → Kinding Γ2 (tsubstIndex X S Y) K.
Proof.
  induction esub; inversion 1; subst; simpl;
    eauto using K_TVar, shift_etvar_kinding, shift_evar_kinding.
Qed.

Lemma subst_etvar_kinding {S Γ1 T K} (wT: Kinding Γ1 T K) :
  ∀ {X Γ2}, subst_etvar X S Γ1 Γ2 → Kinding Γ2 (tsubstTy X S T) K.
Proof.
  induction wT; simpl; eauto using subst_etvar_lookup_etvar;
    econstructor; eauto.
Qed.

Lemma subst_etvar_tyeq {S Γ1 T U K} (q: TyEq Γ1 T U K) :
  ∀ {X Γ2}, subst_etvar X S Γ1 Γ2 → TyEq Γ2 (tsubstTy X S T) (tsubstTy X S U) K.
Proof.
  induction q; simpl; intros; try rewrite tsubstTy_tsubstTy_comm;
    eauto using TyEq, subst_etvar_kinding.
Qed.
Hint Resolve subst_etvar_tyeq.

Lemma subst_etvar_typing {S Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {X Γ2}, subst_etvar X S Γ1 Γ2 → Typing Γ2 (tsubstTm X S t) (tsubstTy X S T).
Proof.
  induction wt; simpl; intros; try rewrite tsubstTy_tsubstTy_comm;
    econstructor; eauto using subst_etvar_kinding.
Qed.
Hint Resolve subst_etvar_typing.

(******************************************************************************)
(* Typing substitution.                                                       *)
(******************************************************************************)

Lemma subst_evar_lookup_evar {x t Γ1 Γ2} (esub: subst_evar x t Γ1 Γ2) :
  ∀ {y T}, lookup_evar Γ1 y T → Typing Γ2 (substIndex x t y) T.
Proof.
  induction esub; inversion 1; subst; simpl; eauto using T_Var.
Qed.

Lemma subst_evar_kinding {s Γ1 T K} (wT: Kinding Γ1 T K) :
  ∀ {x Γ2}, subst_evar x s Γ1 Γ2 → Kinding Γ2 T K.
Proof.
  induction wT; simpl; econstructor; eauto.
Qed.

Lemma subst_evar_tyeq {s Γ1 T U K} (q: TyEq Γ1 T U K) :
 ∀ {x Γ2}, subst_evar x s Γ1 Γ2 → TyEq Γ2 T U K.
Proof.
  induction q; simpl; eauto using TyEq, subst_evar_kinding.
Qed.
Hint Resolve subst_evar_tyeq.

Lemma subst_evar_typing {s Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {x Γ2}, subst_evar x s Γ1 Γ2 → Typing Γ2 (substTm x s t) T.
Proof.
  induction wt; simpl; eauto using subst_evar_lookup_evar;
    econstructor; eauto using subst_evar_kinding.
Qed.
Hint Resolve subst_evar_typing.

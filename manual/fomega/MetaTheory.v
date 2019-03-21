Require Import Coq.omega.Omega.
Require Export BoilerplateSemantics.
Set Implicit Arguments.

(******************************************************************************)
(* Well-formedness                                                            *)
(******************************************************************************)

Lemma tyeq_kinding {Γ T U K} : TyEq Γ T U K → Kinding Γ T K ∧ Kinding Γ U K.
Proof.
  induction 1; destruct_conjs; repeat econstructor;
    eauto using subst_etvar_kinding.
Qed.

Lemma tyeq_kinding_left {Γ T U K} : TyEq Γ T U K → Kinding Γ T K.
Proof. apply tyeq_kinding. Qed.

Lemma tyeq_kinding_right {Γ T U K} : TyEq Γ T U K → Kinding Γ U K.
Proof. apply tyeq_kinding. Qed.

Lemma tred_tyeq {Γ S T K} : TRed Γ S T K → TyEq Γ S T K.
Proof.
  induction 1; try (econstructor; eauto using K_TVar; fail); eapply Q_Trans;
    [ eauto using Q_App, Q_Abs | eauto using Q_AppAbs, tyeq_kinding_right ].
Qed.

Lemma tredstar_tyeq {Γ S T K} : TRedStar Γ S T K → TyEq Γ S T K.
Proof.
  induction 1; try (econstructor; eauto; fail); eauto using Q_Trans, tred_tyeq.
Qed.

Hint Extern 2 (Kinding _ _ _) =>
  match goal with
    | H: TyEq     _ _ _ _ |- _ =>
      destruct (tyeq_kinding H); clear H
    | H: TRed     _ _ _ _ |- _ =>
      destruct (tyeq_kinding (tred_tyeq H)); clear H
    | H: TRedStar _ _ _ _ |- _ =>
      destruct (tyeq_kinding (tredstar_tyeq H)); clear H
  end.

Lemma tred_kinding_left {Γ T U K} : TRed Γ T U K → Kinding Γ T K.
Proof. eauto. Qed.

Lemma tred_kinding_right {Γ T U K} : TRed Γ T U K → Kinding Γ U K.
Proof. eauto. Qed.

(* Definition 30.3.18 *)
Inductive wf_env : Env → Prop :=
  | wf_empty                      : wf_env empty
  | wf_evar  {Γ T} (wΓ: wf_env Γ) : Kinding Γ T star → wf_env (evar Γ T)
  | wf_etvar {Γ K} (wΓ: wf_env Γ) : wf_env (etvar Γ K).

(* 30.3.19 *)
Lemma lookup_evar_kinding {Γ} (wΓ: wf_env Γ) :
  ∀ {x T}, lookup_evar Γ x T → Kinding Γ T star.
Proof.
  induction wΓ; inversion 1; subst; simpl;
    eauto using shift_etvar_kinding, shift_evar_kinding.
Qed.

Lemma typing_kinding {Γ t T} (wfΓ : wf_env Γ) (wt: Typing Γ t T) :
  Kinding Γ T star.
Proof.
  induction wt; eauto using lookup_evar_kinding;
    try (econstructor; eauto; fail).
  - constructor; auto.
    specialize (IHwt (wf_evar wfΓ H)).
    eauto using strengthening_var_kinding.
  - specialize (IHwt1 wfΓ).
    dependent destruction IHwt1; auto.
  - constructor; eauto using wf_env.
  - specialize (IHwt wfΓ).
    dependent destruction IHwt.
    eauto using subst_etvar_kinding.
Qed.

Lemma QR_Refl {Γ T K} (wT: Kinding Γ T K) : TRed Γ T T K.
Proof.
  induction wT; econstructor; eauto.
Qed.

Lemma QRS_Trans {Γ S T U K} :
  TRedStar Γ S T K → TRedStar Γ T U K → TRedStar Γ S U K.
Proof.
  intros P Q; revert S P; induction Q; simpl; eauto using QRS_Cons.
Qed.

Lemma QRS_Arrow1 {Γ S1 S2} (r: TRedStar Γ S1 S2 star) :
  ∀ {T}, Kinding Γ T star → TRedStar Γ (tarr S1 T) (tarr S2 T) star.
Proof.
  depind r; simpl; econstructor; eauto using QR_Refl, Kinding, TRed.
Qed.

Lemma QRS_Arrow2 {Γ T1 T2} (r: TRedStar Γ T1 T2 star) :
  ∀ {S}, Kinding Γ S star → TRedStar Γ (tarr S T1) (tarr S T2) star.
Proof.
  depind r; simpl; econstructor; eauto using QR_Refl, Kinding, TRed.
Qed.

Lemma QRS_Arrow {Γ S1 S2 T1 T2} :
  TRedStar Γ S1 S2 star → TRedStar Γ T1 T2 star →
  TRedStar Γ (tarr S1 T1) (tarr S2 T2) star.
Proof.
  intros; eapply QRS_Trans;
  [ eauto using QRS_Arrow1 | eauto using QRS_Arrow2 ].
Qed.

Lemma QRS_Abs {Γ K K2 S T} (r: TRedStar (etvar Γ K) S T K2) :
  TRedStar Γ (tabs K S) (tabs K T) (karr K K2).
Proof.
  depind r; econstructor; eauto using Kinding, TRed.
Qed.

Lemma QRS_App1 {Γ S T K K2} (r: TRedStar Γ S T (karr K K2)) :
  ∀ U, Kinding Γ U K → TRedStar Γ (tapp S U) (tapp T U) K2.
Proof.
  depind r; simpl; econstructor; eauto using QR_Refl, Kinding, TRed.
Qed.

Lemma QRS_App2 {Γ T U K K2} (r: TRedStar Γ T U K) :
  ∀ S, Kinding Γ S (karr K K2) → TRedStar Γ (tapp S T) (tapp S U) K2.
Proof.
  depind r; simpl; econstructor; eauto using QR_Refl, Kinding, TRed.
Qed.

Lemma QRS_App {Γ S1 T1 S2 T2 K K2} :
  TRedStar Γ S1 T1 (karr K K2) → TRedStar Γ S2 T2 K →
  TRedStar Γ (tapp S1 S2) (tapp T1 T2) K2.
Proof.
  intros; eapply QRS_Trans;
  [ eauto using QRS_App1 | eauto using QRS_App2 ].
Qed.

Lemma QRS_All {Γ K S T} (r: TRedStar (etvar Γ K) S T star) :
  TRedStar Γ (tall K S) (tall K T) star.
Proof.
  depind r; simpl; econstructor; eauto using Kinding, TRed.
Qed.

(******************************************************************************)
(* Confluence                                                                 *)
(******************************************************************************)

(* Lemma 30.3.6 *)
Inductive subst_tred : nat → Ty → Ty → Env → Env → Prop :=
  | sr_here {Γ T U K} :
      TRed Γ T U K → subst_tred 0 T U (etvar Γ K) Γ
  | sr_tvar {Γ1 Γ2 X T U K} :
      subst_tred X T U Γ1 Γ2 →
      subst_tred (S X) T U (etvar Γ1 K) (etvar Γ2 K).
Hint Constructors subst_tred.

Lemma subst_tred_index {Γ1 Γ2 X S1 S2} (esub: subst_tred X S1 S2 Γ1 Γ2) :
  ∀ {Y K}, lookup_etvar Γ1 Y K →
    TRed Γ2 (tsubstIndex X S1 Y) (tsubstIndex X S2 Y) K.
Proof.
  induction esub; inversion 1; subst; simpl; repeat constructor;
    eauto using shift_etvar_tred.
Qed.

(* Lemma 30.3.7 *)
Lemma subst_tred_tred {S1 S2 Γ1 T1 T2 K} (r: TRed Γ1 T1 T2 K) :
  ∀ {Y Γ2}, subst_tred Y S1 S2 Γ1 Γ2 →
    TRed Γ2 (tsubstTy Y S1 T1) (tsubstTy Y S2 T2) K.
Proof.
  induction r; simpl; intros; try rewrite tsubstTy_tsubstTy_comm;
    try econstructor; eauto using subst_tred_index.
Qed.

Fixpoint tred_complete (T : Ty) : Ty :=
  match T with
    | tvar X              => tvar X
    | tabs K T            => tabs K (tred_complete T)
    | tapp (tabs K T1) T2 => tsubstTy 0 (tred_complete T2) (tred_complete T1)
    | tapp T1 T2          => tapp (tred_complete T1) (tred_complete T2)
    | tarr T1 T2          => tarr (tred_complete T1) (tred_complete T2)
    | tall K T            => tall K (tred_complete T)
  end.

Lemma tred_triangle {Γ S T K} (r : TRed Γ S T K) : TRed Γ T (tred_complete S) K.
Proof with simpl; eauto using QR_Refl, TRed.
  induction r; intros...
  - dependent destruction r1...
    dependent destruction IHr1...
  - eauto using subst_tred_tred.
Qed.

(* Lemma 30.3.8 *)
Lemma tred_single_step_diamond :
  ∀ {Γ S T U K}, TRed Γ S T K → TRed Γ S U K →
    ∃ V, TRed Γ T V K ∧ TRed Γ U V K.
Proof.
  intros; exists (tred_complete S); eauto using tred_triangle.
Qed.

(* Lemma 30.3.9 *)
Lemma tred_strip {Γ S U K} (r: TRedStar Γ S U K) :
  ∀ V, TRed Γ S V K → ∃ W, TRed Γ U W K ∧ TRedStar Γ V W K.
Proof.
  induction r; simpl; intros V SV.
  - eauto using QRS_Nil.
  - destruct (IHr V SV) as (W & TV & VW).
    destruct (tred_single_step_diamond TV H) as (Z & UZ & VZ).
    eauto using QRS_Cons.
Qed.

Lemma tred_confluence {Γ S T V K} :
  TRedStar Γ S T K → TRedStar Γ S V K →
  ∃ W, TRedStar Γ T W K ∧ TRedStar Γ V W K.
Proof.
  intros ST; revert V; induction ST; intros V SV.
  - eauto using TRedStar.
  - destruct (IHST _ SV) as (W & TW & VW).
    destruct (tred_strip TW H) as (Z & WZ & UZ).
    eauto using QRS_Cons.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

(* Lemma 30.3.11 *)
Lemma teq_tred {Γ S T K} (eq : TyEq Γ S T K) :
  ∃ U, TRedStar Γ S U K ∧ TRedStar Γ T U K.
Proof.
  induction eq.
  - destruct_conjs; eauto using QRS_Arrow.
  - destruct_conjs; eauto using QRS_Abs.
  - destruct_conjs; eauto using QRS_App.
  - destruct_conjs; eauto using QRS_All.
  - exists (tsubstTy 0 T2 T12); split.
    + eauto 10 using TRedStar, TRed, K_App, K_Abs, QR_Refl.
    + eauto using QRS_Nil, subst_etvar_kinding.
  - eauto using QRS_Nil.
  - destruct_conjs; eauto.
  - destruct IHeq1 as [V1 [SV1 UV1]].
    destruct IHeq2 as [V2 [UV2 TV2]].
    destruct (tred_confluence UV1 UV2) as [V [V1V V2V]].
    eauto using QRS_Trans.
Qed.

(* Lemma 30.3.12.1 *)
Lemma tred_tarr_preservation {Γ S1 S2 T} (H : TRedStar Γ (tarr S1 S2) T star) :
  ∃ T1 T2, T = tarr T1 T2 ∧ TRedStar Γ S1 T1 star ∧ TRedStar Γ S2 T2 star.
Proof.
  depind H; simpl; intros.
  - dependent destruction H. eauto 10 using TRedStar.
  - destruct (IHTRedStar) as [T1 [T2 [Teq [S1T1 S2T2]]]]; subst.
    dependent destruction H0; eauto 10 using TRedStar.
Qed.

(* Lemma 30.3.12.2 *)
Lemma tred_tall_preservation {Γ K1 S2 T} (H : TRedStar Γ (tall K1 S2) T star) :
  ∃ T2, T = tall K1 T2 ∧ TRedStar (etvar Γ K1) S2 T2 star.
Proof.
  depind H; simpl; intros.
  - dependent destruction H.
    exists S2; repeat split; auto; constructor; auto.
  - destruct (IHTRedStar) as [T1 [Teq S2T2]]; subst.
    dependent destruction H0.
    exists T2; repeat split; auto.
    apply (QRS_Cons S2T2 H0).
Qed.

Lemma can_form_tarr' {t S T1 T2} (v: Value t) (wt: Typing empty t S) :
  TyEq empty S (tarr T1 T2) star → ∃ t' T1', t = abs T1' t'.
Proof.
  depind wt; intros; try contradiction; eauto using Q_Trans.
  - destruct (teq_tred H) as [V [H1 H2]].
    destruct (tred_tarr_preservation H2) as [T3 [T4 [Teq]]].
    destruct (tred_tall_preservation H1) as [T5 [Teq2]].
    subst; discriminate.
Qed.

Lemma can_form_tarr {t T1 T2} (v: Value t) (wt: Typing empty t (tarr T1 T2)) :
  ∃ t' T1', t = abs T1' t'.
Proof.
  eapply (can_form_tarr' v wt).
  eauto using Q_Refl, wf_empty, typing_kinding.
Qed.

Lemma can_form_tall' {t S} (v: Value t) (wt: Typing empty t S) :
  ∀ K1 T2, TyEq empty S (tall K1 T2) star →
  ∃ t' K1', t = tyabs K1' t'.
Proof.
  depind wt; intros; try contradiction; eauto using Q_Trans.
  - destruct (teq_tred H0) as [V [H1 H2]].
    destruct (tred_tarr_preservation H1) as [T3 [T4 [Teq]]].
    destruct (tred_tall_preservation H2) as [T5 [Teq2]].
    subst; discriminate.
Qed.

Lemma can_form_tall {t K1 T2} (v: Value t) (wt: Typing empty t (tall K1 T2)) :
  ∃ t' K1', t = tyabs K1' t'.
Proof.
  eapply (can_form_tall' v wt).
  eauto using Q_Refl, wf_empty, typing_kinding.
Qed.

Lemma progress {t U} (wt: Typing empty t U) :
  Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; eauto using red.
  depind wt; simpl; auto.
  - inversion H.
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [v1|[t1' r1]]...
    destruct (can_form_tall v1 wt)...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma tyeq_tarr_inversion {Γ S1 S2 T1 T2} :
  TyEq Γ (tarr S1 S2) (tarr T1 T2) star →
  TyEq Γ S1 T1 star ∧ TyEq Γ S2 T2 star.
Proof.
  intro q; destruct (teq_tred q) as [V [SV TV]].
  destruct (tred_tarr_preservation TV) as [V1' [V2' [Veq' [T1V1 T2V2]]]].
  destruct (tred_tarr_preservation SV) as [V1 [V2 [Veq [S1V1 S2V2]]]]; subst.
  dependent destruction Veq; split; eapply Q_Trans;
    eauto using tredstar_tyeq, Q_Symm.
Qed.

Lemma abs_inversion' {Γ S S1 s2} (wt: Typing Γ (abs S1 s2) S) :
  ∀ {T1 T2}, TyEq Γ S (tarr T1 T2) star →
        TyEq Γ T1 S1 star ∧ Typing (evar Γ S1) s2 T2.
Proof.
  depind wt; simpl; intros; eauto using Q_Trans.
  - destruct (tyeq_tarr_inversion H0);
      eauto using Q_Symm, T_Eq.
Qed.

Lemma abs_inversion {Γ S1 T1 T2 s2} (wΓ: wf_env Γ)
  (wt: Typing Γ (abs S1 s2) (tarr T1 T2)) :
  TyEq Γ T1 S1 star ∧ Typing (evar Γ S1) s2 T2.
Proof.
  apply abs_inversion' with (1 := wt);
    eauto using Q_Refl, typing_kinding.
Qed.

Lemma tyeq_tall_inversion {Γ J1 K1 S2 T2} :
  TyEq Γ (tall J1 S2) (tall K1 T2) star →
  J1 = K1 ∧ TyEq (etvar Γ K1) S2 T2 star.
Proof.
  intro q; destruct (teq_tred q) as [V [SV TV]].
  destruct (tred_tall_preservation TV) as [V2' [Veq' T2V2]].
  destruct (tred_tall_preservation SV) as [V2  [Veq S2V2]]; subst.
  dependent destruction Veq; split; auto; eapply Q_Trans;
    eauto using tredstar_tyeq, Q_Symm.
Qed.

Lemma tabs_inversion' {Γ S J1 s2} (wt: Typing Γ (tyabs J1 s2) S) :
  ∀ K1 T2, TyEq Γ S (tall K1 T2) star → J1 = K1 ∧ Typing (etvar Γ K1) s2 T2.
Proof.
  depind wt; simpl; intros.
  - destruct (tyeq_tall_inversion H); subst; eauto using T_Eq.
  - apply IHwt; eauto using Q_Trans.
Qed.

Lemma tabs_inversion {Γ J1 K1 T2 s2} (wΓ: wf_env Γ)
  (wt: Typing Γ (tyabs J1 s2) (tall K1 T2)) :
  J1 = K1 ∧ Typing (etvar Γ J1) s2 T2.
Proof.
  assert (J1 = K1 ∧ Typing (etvar Γ K1) s2 T2).
  apply (tabs_inversion' wt); eauto using Q_Refl, typing_kinding.
  destruct_conjs; subst; auto.
Qed.

Lemma preservation {Γ t U} (wΓ: wf_env Γ) (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt; intros t' r; inversion r; subst; eauto using Typing.
  - destruct (abs_inversion wΓ wt1) as [eq11 wt12].
    eauto using T_Eq.
  - destruct (tabs_inversion wΓ wt) as [e11 wt12]; subst; eauto.
Qed.

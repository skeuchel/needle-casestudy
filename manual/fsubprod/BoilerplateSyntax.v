Require Export BoilerplateFunctions.
Set Implicit Arguments.

(******************************************************************************)
(* Lemmas.                                                                    *)
(******************************************************************************)

Fixpoint size (T : Ty) : nat :=
  match T with
    | tvar _      => 0
    | top         => 0
    | tarr T1 T2  => 1 + size T1 + size T2
    | tall T1 T2  => 1 + size T1 + size T2
    | tprod T1 T2 => 1 + size T1 + size T2
  end.

Lemma tshift_preserves_size T : ∀ c, size (tshiftTy c T) = size T.
Proof.
  induction T; simpl; intuition.
Qed.

Lemma lengthExt_tshiftExt (c : nat) (Δ : Ext) :
  lengthExt (tshiftExt c Δ) = lengthExt Δ.
Proof.
  induction Δ; simpl; f_equal; auto.
Qed.

Lemma lengthExt_tsubstExt (X : nat) (T' : Ty) (Δ : Ext) :
  lengthExt (tsubstExt X T' Δ) = lengthExt Δ.
Proof.
  induction Δ; simpl; f_equal; auto.
Qed.

Ltac specialize_suc :=
  progress
    match goal with
      | [ H : forall _ : nat, _, k : nat |- _ ] => apply (H (S k))
    end.
Ltac var_case :=
  match goal with
    | [ |- forall v i, _ ] =>
      induction v; simpl; intros; destruct i; auto;
      try apply (f_equal (tshiftTy O)) with (y := tvar _); auto
  end.
Ltac ty_case T v :=
  induction T; simpl; intros;
  try solve [ try apply f_equal with (f := tvar); apply v
            | trivial
            | apply f_equal2 with (f := tarr); trivial
            | apply f_equal2 with (f := tall); try specialize_suc; trivial
            | apply f_equal2 with (f := tprod); trivial
            ].

Lemma shiftIndex_comm_ind :
  forall v i c,
    shiftIndex (v + S c) (shiftIndex (v + O) i) =
    shiftIndex (v + O  ) (shiftIndex (v + c) i).
Proof.
  var_case.
Qed.

Lemma tshiftTy_comm_ind (T : Ty) :
  forall v c,
    tshiftTy (v + S c) (tshiftTy (v + O) T) =
    tshiftTy (v + O  ) (tshiftTy (v + c) T).
Proof.
  ty_case T shiftIndex_comm_ind.
Qed.

Lemma tshiftTy_comm (c : nat) (T : Ty) :
    tshiftTy (S c) (tshiftTy O T)
  = tshiftTy O     (tshiftTy c T).
Proof.
  apply (tshiftTy_comm_ind _ 0).
Qed.

Lemma tsubstIndex_shiftIndex_reflection_ind :
  forall (k X : nat) (T : Ty),
    tsubstIndex (k + 0) T (shiftIndex (k + O) X) = tvar X.
Proof.
  var_case.
Qed.

Lemma tsubstTy_tshiftTy_reflection_ind (T : Ty) :
  forall k T',
    tsubstTy (k + 0) T' (tshiftTy (k + O) T) = T.
Proof.
  ty_case T tsubstIndex_shiftIndex_reflection_ind.
Qed.

Lemma tsubstTy_tshiftTy_reflection (T' T : Ty) :
  tsubstTy 0 T' (tshiftTy O T) = T.
Proof.
  apply (tsubstTy_tshiftTy_reflection_ind _ 0).
Qed.

Lemma tshiftTy_tsubstIndex_comm_ind :
  forall (k X c : nat) (T : Ty),
    tshiftTy (k + c) (tsubstIndex (k + 0) T X) =
    tsubstIndex (k + 0) (tshiftTy c T) (shiftIndex (k + S c) X).
Proof.
  var_case.
  rewrite tshiftTy_comm; f_equal; auto.
Qed.

Lemma tshiftTy_tsubstTy_comm_ind (T : Ty):
  forall (k c : nat) (T' : Ty),
    tshiftTy (k + c) (tsubstTy (k + 0) T' T) =
    tsubstTy (k + 0) (tshiftTy c T') (tshiftTy (k + S c) T).
Proof.
  ty_case T tshiftTy_tsubstIndex_comm_ind.
Qed.

Lemma tshiftTy_tsubstTy_comm c (T T2 : Ty) :
    tshiftTy c (tsubstTy O T T2)
  = tsubstTy O (tshiftTy c T) (tshiftTy (S c) T2).
Proof.
  apply (tshiftTy_tsubstTy_comm_ind _ 0).
Qed.

Lemma tsubstIndex_shiftIndex_comm_ind :
  forall k Y X T',
    tsubstIndex (k + S X) T' (shiftIndex (k + 0) Y) =
    tshiftTy (k + 0) (tsubstIndex (k + X) T' Y).
Proof.
  var_case.
  rewrite tshiftTy_comm; f_equal; auto.
Qed.

Lemma tsubstTy_tshiftTy_comm_ind (T : Ty) :
  forall k X T',
    tsubstTy (k + S X) T' (tshiftTy (k + 0) T) =
    tshiftTy (k + 0) (tsubstTy (k + X) T' T).
Proof.
  ty_case T tsubstIndex_shiftIndex_comm_ind.
Qed.

Lemma tsubstTy_tshiftTy_comm :
  forall X T' T,
    tsubstTy (S X) T' (tshiftTy 0 T) =
    tshiftTy 0 (tsubstTy X T' T).
Proof.
  intros; apply (tsubstTy_tshiftTy_comm_ind _ 0).
Qed.

Lemma tsubstTy_tsubstIndex_comm_ind :
  forall k Y T1 T2 X,
    tsubstTy (k + X) T1 (tsubstIndex (k + 0) T2 Y) =
    tsubstTy (k + 0) (tsubstTy X T1 T2) (tsubstIndex (k + S X) T1 Y).
Proof.
  var_case.
  rewrite tsubstTy_tshiftTy_reflection; auto.
  repeat rewrite tsubstTy_tshiftTy_comm; f_equal; auto.
Qed.

Lemma tsubstTy_tsubstTy_comm_ind (T : Ty) :
  forall k X T1 T2,
    tsubstTy (k + X) T1 (tsubstTy (k + 0) T2 T) =
    tsubstTy (k + 0) (tsubstTy X T1 T2) (tsubstTy (k + (S X)) T1 T).
Proof.
  ty_case T tsubstTy_tsubstIndex_comm_ind.
Qed.

Lemma tsubstTy_tsubstTy_comm :
  forall X T1 T2 T,
    tsubstTy X T1 (tsubstTy 0 T2 T) =
    tsubstTy 0 (tsubstTy X T1 T2) (tsubstTy (S X) T1 T).
Proof.
  intros; apply (tsubstTy_tsubstTy_comm_ind _ 0).
Qed.

(******************************************************************************)
(* Context extension                                                          *)
(******************************************************************************)

Lemma extend_append (Γ : Env) (Δ1 Δ2 : Ext) :
  extend Γ (append Δ1 Δ2) = extend (extend Γ Δ1) Δ2.
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.

Lemma lengthExt_append (Δ1 Δ2 : Ext) :
  lengthExt (append Δ1 Δ2) = lengthExt Δ2 + lengthExt Δ1.
Proof.
  induction Δ2; simpl; auto.
Qed.

Lemma tshiftExt_append (c : nat) (Δ1 Δ2 : Ext) :
  tshiftExt c (append Δ1 Δ2) = append (tshiftExt c Δ1) (tshiftExt c Δ2).
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.
Hint Rewrite tshiftExt_append : interaction.

Lemma tsubstExt_append (X : nat) (S : Ty) (Δ1 Δ2 : Ext) :
  tsubstExt X S (append Δ1 Δ2) = append (tsubstExt X S Δ1) (tsubstExt X S Δ2).
Proof.
  induction Δ2; simpl; f_equal; auto.
Qed.
Hint Rewrite tsubstExt_append : interaction.

(******************************************************************************)
(* Well-formed context lemmas                                                 *)
(******************************************************************************)

Inductive wf_env : Env → Prop :=
  | wf_empty                                     : wf_env empty
  | wf_evar {Γ T}  (wΓ: wf_env Γ) (wT: wfTy Γ T) : wf_env (evar Γ T)
  | wf_etvar {Γ T} (wΓ: wf_env Γ) (wT: wfTy Γ T) : wf_env (etvar Γ T).
Hint Constructors wf_env.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Lemma lookup_etvar_functional {Γ : Env} {X} {S T} :
  lookup_etvar Γ X S → lookup_etvar Γ X T → S = T.
Proof.
  intros gbS gbT; revert S gbS.
  induction gbT; inversion 1; subst; simpl; f_equal; auto.
Qed.

Lemma lookup_evar_functional {Γ : Env} {X} {S T} :
  lookup_evar Γ X S → lookup_evar Γ X T → S = T.
Proof.
  intros gvS gvT; revert S gvS.
  induction gvT; inversion 1; subst; simpl; f_equal; auto.
Qed.

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive shift_etvar : nat → Env → Env → Prop :=
  | shift_etvar_here {Γ T} :
      shift_etvar 0 Γ (etvar Γ T)
  | shift_etvar_there_evar {Γ1 Γ2 c T} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar c (evar Γ1 T) (evar Γ2 (tshiftTy c T))
  | shift_etvar_there_etvar {Γ1 Γ2 c T} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar (S c) (etvar Γ1 T) (etvar Γ2 (tshiftTy c T)).
Hint Constructors shift_etvar.

Lemma weaken_shift_etvar {Γ1 : Env} {Γ2 : Env} {Δ : Ext} {c} :
  shift_etvar c Γ1 Γ2 →
  shift_etvar c (extend Γ1 Δ) (extend Γ2 (tshiftExt c Δ)).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_shift_etvar.

Inductive shift_evar : nat → Env → Env → Prop :=
  | shift_evar_here {Γ T} :
      shift_evar 0 Γ (evar Γ T)
  | shift_evar_there_evar {Γ1 Γ2 c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar (S c) (evar Γ1 T) (evar Γ2 T)
  | shift_evar_there_etvar {Γ1 Γ2 c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar c (etvar Γ1 T) (etvar Γ2 T).
Hint Constructors shift_evar.

Lemma weaken_shift_evar {Γ1 : Env} {Γ2 : Env} (Δ : Ext) {c} :
  shift_evar c Γ1 Γ2 →
  shift_evar (lengthExt Δ + c) (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_shift_evar.

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_etvar_lookup_etvar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ X T, lookup_etvar Γ1 X T → lookup_etvar Γ2 (shiftIndex c X) (tshiftTy c T).
Proof.
  induction ib; inversion 1; subst; simpl; try rewrite tshiftTy_comm; eauto.
Qed.
Hint Resolve shift_etvar_lookup_etvar.

Lemma shift_etvar_lookup_evar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T → lookup_evar Γ2 x (tshiftTy c T).
Proof.
  induction ib; inversion 1; subst; simpl; try rewrite tshiftTy_comm; eauto.
Qed.
Hint Resolve shift_etvar_lookup_evar.

Lemma shift_evar_lookup_etvar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ X T, lookup_etvar Γ1 X T → lookup_etvar Γ2 X T.
Proof.
  induction iv; inversion 1; subst; simpl; eauto.
Qed.
Hint Resolve shift_evar_lookup_etvar.

Lemma shift_evar_lookup_evar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T → lookup_evar Γ2 (shiftIndex c x) T.
Proof.
  induction iv; inversion 1; subst; simpl; eauto.
Qed.
Hint Resolve shift_evar_lookup_evar.

(******************************************************************************)
(* Weakening lemmas for well-formedness                                       *)
(******************************************************************************)

Lemma shift_etvar_wftyp {Γ1 T} (wfT: wfTy Γ1 T) :
  ∀ {c Γ2}, shift_etvar c Γ1 Γ2 → wfTy Γ2 (tshiftTy c T).
Proof.
  induction wfT; simpl; econstructor; eauto.
Qed.
Hint Resolve shift_etvar_wftyp.

Lemma shift_evar_wftyp {Γ1 T} (wfT: wfTy Γ1 T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → wfTy Γ2 T.
Proof.
  induction wfT; simpl; econstructor; eauto.
Qed.
Hint Resolve shift_evar_wftyp.

(******************************************************************************)
(* Strengthening lemmas for well-formedness                                   *)
(******************************************************************************)

Lemma compatible_context_wfty {Γ1 Γ2}
  (ξ: ∀ {X T1}, lookup_etvar Γ1 X T1 → ∃ T2, lookup_etvar Γ2 X T2) :
  ∀ T, wfTy Γ1 T → wfTy Γ2 T.
Proof.
  intros T wT; revert Γ2 ξ.
  induction wT; simpl; intros; eauto.
  - destruct (ξ _ _ H); eauto.
  - econstructor; eauto.
    apply IHwT2.
    inversion 1; subst; simpl.
    + eauto.
    + destruct (ξ _ _ H4); eauto.
Qed.

Lemma replace_etvar_wfty {Γ B1 B2 T} :
  wfTy (etvar Γ B1) T → wfTy (etvar Γ B2) T.
Proof.
  apply compatible_context_wfty; inversion 1; eauto.
Qed.

Lemma strengthen_evar_wfty {Γ S T} :
  wfTy (evar Γ S) T → wfTy Γ T.
Proof.
  apply compatible_context_wfty; inversion 1; eauto.
Qed.

Lemma strengthen_extend_wfty {Γ Δ T} :
  wfTy (extend Γ Δ) T → wfTy Γ T.
Proof.
  apply compatible_context_wfty; clear.
  induction Δ; simpl; inversion 1; eauto.
Qed.

(******************************************************************************)
(* Forward reasoning about well-formedness                                    *)
(******************************************************************************)

Lemma lookup_etvar_wf {Γ} (wΓ: wf_env Γ) :
  ∀ {X T}, lookup_etvar Γ X T → wfTy Γ T.
Proof.
  induction wΓ; inversion 1; subst; simpl; eauto.
Qed.

Lemma lookup_evar_wf {Γ} (wΓ: wf_env Γ) :
  ∀ {X T}, lookup_evar Γ X T → wfTy Γ T.
Proof.
  induction wΓ; inversion 1; subst; simpl; eauto.
Qed.

Hint Extern 2 (wf_env _ _) =>
  match goal with
    | wG: wf_env (etvar _ _)                |- _ => inversion_clear wG; subst
    | wG: wf_env (evar _ _)                 |- _ => inversion_clear wG; subst
  end.

Hint Extern 2 (wfTy _ _) =>
  match goal with
    | wG: wf_env (etvar _ _)                |- _ => inversion_clear wG; subst
    | wG: wf_env (evar _ _)                 |- _ => inversion_clear wG; subst
    | wG: wf_env ?G, L: lookup_etvar ?G _ _ |- _ => apply (lookup_etvar_wf wG) in L
    | wG: wf_env ?G, L: lookup_evar ?G _ _  |- _ => apply (lookup_evar_wf wG) in L
    | w:  wfTy _ (tvar _)                  |- _ => inversion_clear w; subst
    | w:  wfTy _ top                       |- _ => inversion_clear w; subst
    | w:  wfTy _ (tarr _ _)                |- _ => inversion_clear w; subst
    | w:  wfTy _ (tall _ _)                |- _ => inversion_clear w; subst
    | H: wf_env ?G, IH : wf_env ?G -> _     |- _ => specialize (IH H); destruct_conjs
  end.

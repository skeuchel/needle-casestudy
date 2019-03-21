Require Export BoilerplateFunctions.
Set Implicit Arguments.

(******************************************************************************)
(* Lemmas.                                                                    *)
(******************************************************************************)

Fixpoint size (T : Ty) : nat :=
  match T with
    | tvar _     => 0
    | tabs _ T0  => S (size T0)
    | tapp T1 T2 => S (size T1 + size T2)
    | tarr T1 T2 => S (size T1 + size T2)
    | tall K T   => S (size T)
  end.

Lemma tshift_preserves_size T : ∀ c, size (tshiftTy c T) = size T.
Proof.
  induction T; simpl; intuition.
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
            | apply f_equal2 with (f := tabs); auto; specialize_suc; trivial
            | apply f_equal2 with (f := tapp); trivial
            | apply f_equal2 with (f := tarr); trivial
            | apply f_equal2 with (f := tall); auto; specialize_suc; trivial
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
(* Context lookups.                                                           *)
(******************************************************************************)

Lemma lookup_etvar_functional {Γ X K K'} :
  lookup_etvar Γ X K → lookup_etvar Γ X K' → K = K'.
Proof.
  intros gt gt'; revert K' gt'.
  induction gt; intros; dependent destruction gt'; simpl; f_equal; auto.
Qed.

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive shift_etvar : nat → Env → Env → Prop :=
  | it_here {Γ K} :
      shift_etvar 0 Γ (etvar Γ K)
  | it_var {Γ1 Γ2 c T} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar c (evar Γ1 T) (evar Γ2 (tshiftTy c T))
  | it_tvar {Γ1 Γ2 c K} :
      shift_etvar c Γ1 Γ2 →
      shift_etvar (S c) (etvar Γ1 K) (etvar Γ2 K).
Hint Constructors shift_etvar.

Inductive shift_evar : nat → Env → Env → Prop :=
  | iv_here {Γ T} :
      shift_evar 0 Γ (evar Γ T)
  | iv_var {Γ1 Γ2 : Env} {c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar (S c) (evar Γ1 T) (evar Γ2 T)
  | iv_tvar {Γ1 Γ2 c K} :
      shift_evar c Γ1 Γ2 →
      shift_evar c (etvar Γ1 K) (etvar Γ2 K).
Hint Constructors shift_evar.

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_etvar_lookup_etvar {Γ1 Γ2 c} (ib : shift_etvar c Γ1 Γ2) :
  ∀ X K, lookup_etvar Γ1 X K → lookup_etvar Γ2 (shiftIndex c X) K.
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
  ∀ X K, lookup_etvar Γ1 X K → lookup_etvar Γ2 X K.
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
(* Strengthening lemmas                                                       *)
(******************************************************************************)

Lemma shiftIndex_inj {c} :
  ∀ X Y, shiftIndex c X = shiftIndex c Y → X = Y.
Proof.
  induction c; simpl; intros.
  dependent destruction H; auto.
  destruct X, Y; simpl; try discriminate; auto.
Qed.

Lemma tshift_inj {c T U} :
  tshiftTy c T = tshiftTy c U → T = U.
Proof.
  revert c U; induction T; simpl; intros c U eq; destruct U; simpl in *;
    try discriminate; inversion eq; f_equal; eauto using shiftIndex_inj.
Qed.

Lemma remove_var_lookup_etvar {Γ1 Γ2 c} (iv : shift_evar c Γ2 Γ1) :
  ∀ X K, lookup_etvar Γ1 X K → lookup_etvar Γ2 X K.
Proof.
  induction iv; inversion 1; subst; simpl; eauto.
Qed.

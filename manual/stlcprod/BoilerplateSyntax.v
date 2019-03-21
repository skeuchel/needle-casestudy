Require Export SpecSyntax.
Require Export BoilerplateFunctions.
Set Implicit Arguments.

(******************************************************************************)
(* Context extension.                                                         *)
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

(******************************************************************************)
(* Context insertions.                                                        *)
(******************************************************************************)

Inductive shift_evar : nat → Env → Env → Prop :=
  | shift_evar_here {Γ T} :
      shift_evar 0 Γ (evar Γ T)
  | shift_evar_there_evar {Γ1 Γ2 c T} :
      shift_evar c Γ1 Γ2 →
      shift_evar (S c) (evar Γ1 T) (evar Γ2 T).
Hint Constructors shift_evar.

Lemma weaken_shift_evar {Γ1 : Env} {Γ2 : Env} (Δ : Ext) {c} :
  shift_evar c Γ1 Γ2 → shift_evar (lengthExt Δ + c) (extend Γ1 Δ) (extend Γ2 Δ).
Proof.
  revert c Γ2; induction Δ; simpl; intros; try constructor; auto.
Qed.
Hint Resolve weaken_shift_evar.

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_evar_lookup_evar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T → lookup_evar Γ2 (shiftIndex c x) T.
Proof.
  induction iv; inversion 1; simpl; eauto.
Qed.
Hint Resolve shift_evar_lookup_evar.

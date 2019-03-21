Require Export SpecSyntax.
Require Export BoilerplateFunctions.
Set Implicit Arguments.

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

(******************************************************************************)
(* Lemmas about shifting and context lookups.                                 *)
(******************************************************************************)

Lemma shift_evar_lookup_evar {Γ1 Γ2 c} (iv : shift_evar c Γ1 Γ2) :
  ∀ x T, lookup_evar Γ1 x T → lookup_evar Γ2 (shiftIndex c x) T.
Proof.
  induction iv; inversion 1; simpl; eauto.
Qed.
Hint Resolve shift_evar_lookup_evar.

(******************************************************************************)
(* Context substitutions                                                      *)
(******************************************************************************)

Inductive subst_evar (Γ: Env) (U : Ty) : nat → Env → Env → Prop :=
  | subst_evar_here :
      subst_evar Γ U 0 (evar Γ U) Γ
  | subst_evar_there_evar {Γ1 Γ2 : Env} {x T} :
      subst_evar Γ U x     Γ1           Γ2 →
      subst_evar Γ U (S x) (evar Γ1 T) (evar Γ2 T).
Hint Constructors subst_evar.

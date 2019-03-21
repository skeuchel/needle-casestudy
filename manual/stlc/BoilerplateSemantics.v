Require Export SpecSemantics.
Require Export BoilerplateSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma shift_evar_typing {Γ1 t T} (wt: Typing Γ1 t T) :
  ∀ {c Γ2}, shift_evar c Γ1 Γ2 → Typing Γ2 (shiftTm c t) T.
Proof.
  induction wt; simpl; econstructor; eauto.
Qed.

(******************************************************************************)
(* Substitution lemmas                                                        *)
(******************************************************************************)

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
  induction wt; simpl; intros;
    eauto using subst_evar_lookup_evar;
    econstructor; eauto.
Qed.

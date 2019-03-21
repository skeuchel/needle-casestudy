Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.
Require Export DeclarationEvaluation.
Set Implicit Arguments.

(******************************************************************************)
(* Weakening lemmas                                                           *)
(******************************************************************************)

Lemma value_shift c {t : Tm} :
  Value t → Value (shiftTm c t).
Proof.
  revert c; induction t; simpl; try contradiction; auto; intros.
Qed.

Lemma value_tshift c {t : Tm} :
  Value t → Value (tshiftTm c t).
Proof.
  revert c; induction t; simpl; try contradiction; auto; intros.
Qed.

Lemma weaken_value u :
  ∀ {t}, Value t → Value (weakenTm t u).
Proof.
  induction u as [|[]]; simpl; eauto using value_shift, value_tshift.
Qed.

(******************************************************************************)
(* Progress                                                                   *)
(******************************************************************************)

Lemma can_form_tarr {t : Tm} {T1 T2} :
  Value t → Typing empty t (tarr T1 T2) →
  exists t' T1', t = abs T1' t'.
Proof.
  intros val_t wt_t.
  depind wt_t; try contradiction.
  exists t, T1; reflexivity.
Qed.

Lemma can_form_tall {t : Tm} {T} :
  Value t → Typing empty t (tall T) →
  exists t', t = tabs t'.
Proof.
  intros val_t wt_t.
  depind wt_t; try contradiction.
  exists t; auto.
Qed.

Scheme ind_typing := Induction for Typing Sort Prop
with ind_dtyping := Induction for DTyping Sort Prop.

Combined Scheme ind_typing_dtyping from
  ind_typing, ind_dtyping.

Lemma progress {Γ t U} (wt: Typing Γ t U) :
  Γ = empty → Value t ∨ ∃ t', red t t'.
Proof with destruct_conjs; subst; simpl; eauto using red, redds'.
  induction wt using ind_typing with
  (P0 := fun Γ ds Δ wds => Γ = empty → ValueH ds ∨ ∃ ds', redds' ds ds');
    intros...
  - destruct IHwt1 as [v1|[t1' r1]]...
    destruct IHwt2 as [v2|[t2' r2]]...
    destruct (can_form_tarr v1 wt1)...
  - destruct IHwt as [vt|[t1' r1]]...
    destruct (can_form_tall vt wt)...
  - destruct IHwt as [v1|[t1' r1]]...
    dependent destruction d...
  - destruct IHwt as [vt|[t1' r1]]...
Qed.

(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma preservation {Γ t U} (wt: Typing Γ t U) :
  ∀ {t'}, red t t' → Typing Γ t' U.
Proof.
  induction wt using ind_typing
  with (P0 := fun Γ ds Δ wds => ∀ ds', redds' ds ds' → DTyping Γ ds' Δ);
    intros t' rd; inversion rd; subst; eauto using Typing, DTyping.
  - dependent destruction wt1; eauto using subst_evar_Typing with subst.
  - dependent destruction wt; eauto using subst_etvar_Typing with subst.
  - dependent destruction wd; auto.
  - dependent destruction wd; isimpl; eauto.
    eapply T_Let; repeat isimpl; rewrite <- (domain_DTyping_bind _ _ _ wd) in *;
      eauto using subst_evar_DTyping, subst_evar_Typing with infra.
  - econstructor; repeat isimpl; eauto with infra.
    specialize (IHwt _ H2); rewrite <- (domain_DTyping_bind _ _ _ wd),
      (domain_DTyping_bind _ _ _ IHwt) in *; eauto.
Qed.

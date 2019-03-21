Require Export SpecSyntax.
Require Export BoilerplateFunctions.
Set Implicit Arguments.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _  => True
    | tabs _   => True
    | _        => False
  end.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm sub_here t2 t12)
  | tapptabs {T2 t11} :
      red (tapp (tabs t11) T2) (tsubstTm 0 T2 t11)
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2).

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive Typing (Γ: Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} (wf_T1: wfTy Γ T1) :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_Tabs {t T} :
      Typing (etvar Γ) t T →  Typing Γ (tabs t) (tall T)
  | T_Tapp {t1 T12 T2} :
      Typing Γ t1 (tall T12) → wfTy Γ T2 →
      Typing Γ (tapp t1 T2) (tsubstTy 0 T2 T12).

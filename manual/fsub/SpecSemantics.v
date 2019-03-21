Require Export BoilerplateFunctions.
Set Implicit Arguments.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _  => True
    | tabs _ _ => True
    | _        => False
  end.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm sub_here t2 t12)
  | tapptabs {T11 T2 t12} :
      red (tapp (tabs T11 t12) T2) (tsubstTm 0 T2 t12)
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2).

(******************************************************************************)
(* Subtyping relation                                                         *)
(******************************************************************************)

Inductive Sub (Γ: Env) : Ty → Ty → Prop :=
  | SA_Top {S} (wf_S: wfTy Γ S) :
      Sub Γ S top
  | SA_Refl_TVar {X} :
      wfTy Γ (tvar X) → Sub Γ (tvar X) (tvar X)
  | SA_Trans_TVar {X T U} :
      lookup_etvar Γ X U → Sub Γ U T → Sub Γ (tvar X) T
  | SA_Arrow {T1 T2 S1 S2} :
      Sub Γ T1 S1 → Sub Γ S2 T2 → Sub Γ (tarr S1 S2) (tarr T1 T2)
  | SA_All {T1 T2 S1 S2} :
      Sub Γ T1 S1 → Sub (etvar Γ T1) S2 T2 → Sub Γ (tall S1 S2) (tall T1 T2).

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
  | T_Tabs {t T1 T2} (wf_T1: wfTy Γ T1) :
      Typing (etvar Γ T1) t T2 →
      Typing Γ (tabs T1 t) (tall T1 T2)
  | T_Tapp {t1 T11 T12 T2} :
      Typing Γ t1 (tall T11 T12) → Sub Γ T2 T11 →
      Typing Γ (tapp t1 T2) (tsubstTy 0 T2 T12)
  | T_Sub {t T1 T2} :
      Typing Γ t T1 → Sub Γ T1 T2 →
      Typing Γ t T2.

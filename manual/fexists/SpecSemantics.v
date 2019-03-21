Require Export BoilerplateFunctions.
Set Implicit Arguments.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _    => True
    | tabs _     => True
    | pack _ t _ => Value t
    | _          => False
  end.

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm hn0 t2 t12)
  | tapptabs {T2 t11} :
      red (tapp (tabs t11) T2) (tsubstTm 0 T2 t11)
  | unpackpack {T11 v12 T1 t2} :
      Value v12 →
      red (unpack (pack T11 v12 (texist T1)) t2)
          (tsubstTm 0 T11 (substTm hn0 (tshiftTm 0 v12) t2))
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | E_pack {T11 t12 t12' T1} :
      red t12 t12' → red (pack T11 t12 T1) (pack T11 t12' T1)
  | E_unpack {t1 t1' t2} :
      red t1 t1' → red (unpack t1 t2) (unpack t1' t2).

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
      Typing Γ (tapp t1 T2) (tsubstTy 0 T2 T12)
  | T_Pack {t2 U T2} :
      Typing Γ t2 (tsubstTy 0 U T2) →
      wfTy (etvar Γ) T2 → wfTy Γ U →
      Typing Γ (pack U t2 (texist T2)) (texist T2)
  | T_Unpack {t1 T12 t2 T2} :
      Typing Γ t1 (texist T12) →
      Typing (evar (etvar Γ) T12) t2 (tshiftTy 0 T2) →
      wfTy Γ T2 →
      Typing Γ (unpack t1 t2) T2.

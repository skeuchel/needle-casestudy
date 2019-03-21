Require Export BoilerplateFunctions.
Set Implicit Arguments.

(*************************************************************************)
(* Reduction relation                                                    *)
(*************************************************************************)

Fixpoint Value (t : Tm) : Prop :=
  match t with
    | abs _ _  => True
    | tabs _ _ => True
    | prod x y => Value x ∧ Value y
    | _        => False
  end.

Inductive Match : Pat → Tm → Tm → Tm → Prop :=
  | M_Var {v t} :
      Match pvar v t (substTm sub_here v t)
  | M_Prod {p1 p2 v1 v2 t t' t''} :
      Match p2 (weakenTm v2 (bindPat p1)) t t' → Match p1 v1 t' t'' →
      Match (pprod p1 p2) (prod v1 v2) t t''.

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
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | prodl {t1 t1' t2} :
      red t1 t1' → red (prod t1 t2) (prod t1' t2)
  | prodr {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (prod t1 t2) (prod t1 t2')
  | lettp {p t1 t1' t2} :
      red t1 t1' → red (lett p t1 t2) (lett p t1' t2)
  | lettv {p t1 t3 t2} :
      Value t1 → Match p t1 t2 t3 → red (lett p t1 t2) t3.

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
      Sub Γ T1 S1 → Sub (etvar Γ T1) S2 T2 → Sub Γ (tall S1 S2) (tall T1 T2)
  | SA_Prod {T1 T2 S1 S2} :
      Sub Γ S1 T1 → Sub Γ S2 T2 → Sub Γ (tprod S1 S2) (tprod T1 T2).

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive PTyping (Γ: Env) : Pat → Ty → Ext → Prop :=
  | P_Var {T} (wT: wfTy Γ T) :
      PTyping Γ pvar T (exvar exempty T)
  | P_Prod {p1 T1 Δ1 p2 T2 Δ2} :
      PTyping Γ p1 T1 Δ1 → PTyping (extend Γ Δ1) p2 T2 Δ2 →
      PTyping Γ (pprod p1 p2) (tprod T1 T2) (append Δ1 Δ2).

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
  | T_Prod {t1 T1 t2 T2} :
      Typing Γ t1 T1 → Typing Γ t2 T2 →
      Typing Γ (prod t1 t2) (tprod T1 T2)
  | T_Let {p t1 t2 T1 T2} {Δ : Ext} :
      Typing Γ t1 T1 → PTyping Γ p T1 Δ →
      Typing (extend Γ Δ) t2 T2 →
      Typing Γ (lett p t1 t2) T2
  | T_Sub {t T1 T2} :
      Typing Γ t T1 → Sub Γ T1 T2 →
      Typing Γ t T2.

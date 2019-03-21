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

Fixpoint ValueH (ds : Decls) : Prop :=
  match ds with
    | dnil       => True
    | dcons t ds => Value t
  end.

Inductive Match : Decls (* Γ,Δ *) → Tm (* Γ,Δ *) → Tm (* Γ *) → Prop :=
  | M_DNil {t} :
      Match dnil t t
  | M_DCons {v vs (* Γ,x,Δ *) t (* Γ,x,Δ *) t' (* Γ,x *)} :
      Match vs t t' →
      Match (dcons v vs) t (substTm sub_here v t').

Inductive red : Tm → Tm → Prop :=
  | appabs {T11 t12 t2} :
      Value t2 → red (app (abs T11 t12) t2) (substTm sub_here t2 t12)
  | tapptabs {T2 t12} :
      red (tapp (tabs t12) T2) (tsubstTm 0 T2 t12)
  | appfun {t1 t1' t2} :
      red t1 t1' → red (app t1 t2) (app t1' t2)
  | apparg {t1 t2 t2'} :
      Value t1 → red t2 t2' → red (app t1 t2) (app t1 t2')
  | typefun {t1 t1' T2} :
      red t1 t1' → red (tapp t1 T2) (tapp t1' T2)
  | lett_dnil {t1} :
      red (lett dnil t1) t1
  | lett_dconsv {ds t1 t2} :
      Value t1 →
      red
        (lett (dcons t1 ds) t2)
        (lett (substDecls sub_here t1 ds) (substTm (weakenSubst (bind ds) sub_here) t1 t2))
  | lett_dconsr {ds ds' t2} :
      redds' ds ds' → red (lett ds t2) (lett ds' t2)
with redds' : Decls → Decls → Prop :=
  | dconsr {t t' ds} :
      red t t' → redds' (dcons t ds) (dcons t' ds).

(******************************************************************************)
(* Typing relation.                                                           *)
(******************************************************************************)

Inductive Typing (Γ : Env) : Tm → Ty → Prop :=
  | T_Var {y T} :
      lookup_evar Γ y T → Typing Γ (var y) T
  | T_Abs {t T1 T2} (wT1: wfTy Γ T1) :
      Typing (evar Γ T1) t T2 →
      Typing Γ (abs T1 t) (tarr T1 T2)
  | T_App {t1 t2 T11 T12} :
      Typing Γ t1 (tarr T11 T12) → Typing Γ t2 T11 →
      Typing Γ (app t1 t2) T12
  | T_Tabs {t T} :
      Typing (etvar Γ) t T → Typing Γ (tabs t) (tall T)
  | T_Tapp {t1 T12 T2} :
      Typing Γ t1 (tall T12) → wfTy Γ T2 →
      Typing Γ (tapp t1 T2) (tsubstTy 0 T2 T12)
  | T_Let {ds t T Δ} :
      DTyping Γ ds Δ →
      Typing (extend Γ Δ) t T →
      Typing Γ (lett ds t) T
with DTyping (Γ : Env) : Decls → Ext → Prop :=
  | T_Dnil :
      DTyping Γ dnil exempty
  | T_DCons {Δ t T ds} :
      Typing Γ t T → DTyping (evar Γ T) ds Δ →
      DTyping Γ (dcons t ds) (append (exvar exempty T) Δ).

Scheme ind_typing := Induction for Typing Sort Prop
with ind_dtyping := Induction for DTyping Sort Prop.

Combined Scheme ind_typing_dtyping from
  ind_typing, ind_dtyping.

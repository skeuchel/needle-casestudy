Require Export SpecSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Shifting                                                                   *)
(******************************************************************************)

Fixpoint shiftIndex (c : nat) (i : nat) : nat :=
  match c with
    | O   => S i
    | S c =>
      match i with
        | O   => O
        | S i => S (shiftIndex c i)
      end
  end.

Fixpoint tshiftTy (c : nat) (T : Ty) : Ty :=
  match T with
    | tvar X      => tvar (shiftIndex c X)
    | top         => top
    | tarr T1 T2  => tarr (tshiftTy c T1) (tshiftTy c T2)
    | tall T1 T2  => tall (tshiftTy c T1) (tshiftTy (S c) T2)
  end.

Fixpoint tshiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var x
  | abs T1 t2    => abs (tshiftTy c T1) (tshiftTm c t2)
  | app t1 t2    => app (tshiftTm c t1) (tshiftTm c t2)
  | tabs T1 t2   => tabs (tshiftTy c T1) (tshiftTm (S c) t2)
  | tapp t1 T2   => tapp (tshiftTm c t1) (tshiftTy c T2)
  end.

Fixpoint shiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var (shiftIndex c x)
  | abs T1 t2    => abs T1 (shiftTm (S c) t2)
  | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  | tabs T1 t2   => tabs T1 (shiftTm c t2)
  | tapp t1 T2   => tapp (shiftTm c t1) T2
  end.

Fixpoint weakenTm (t : Tm) (k : nat) : Tm :=
  match k with
    | O   => t
    | S k => shiftTm O (weakenTm t k)
  end.

(******************************************************************************)
(* Type substitution.                                                         *)
(******************************************************************************)

Fixpoint tsubstIndex (X : nat) (T' : Ty) (Y : nat) : Ty :=
  match X , Y with
    | O   , O   => T'
    | O   , S Y => tvar Y
    | S X , O   => tvar O
    | S X , S Y => tshiftTy 0 (tsubstIndex X T' Y)
  end.

Fixpoint tsubstTy (X : nat) (T' : Ty) (T : Ty) : Ty :=
  match T with
    | tvar Y      => tsubstIndex X T' Y
    | top         => top
    | tarr T1 T2  => tarr (tsubstTy X T' T1) (tsubstTy X T' T2)
    | tall T1 T2  => tall (tsubstTy X T' T1) (tsubstTy (S X) T' T2)
  end.

Fixpoint tsubstTm (X : nat) (T' : Ty) (t : Tm) : Tm :=
  match t with
  | var x        => var x
  | abs T1 t2    => abs  (tsubstTy X T' T1) (tsubstTm X T' t2)
  | app t1 t2    => app  (tsubstTm X T' t1) (tsubstTm X T' t2)
  | tabs T1 t2   => tabs (tsubstTy X T' T1) (tsubstTm (S X) T' t2)
  | tapp t1 T2   => tapp (tsubstTm X T' t1) (tsubstTy X T' T2)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Inductive Subst : Set :=
  | sub_here  : Subst
  | sub_var   : Subst → Subst
  | sub_bound : Subst → Subst.

Fixpoint weakenSubst (sub : Subst) (k : nat) : Subst :=
  match k with
   | O   => sub
   | S k => sub_var (weakenSubst sub k)
  end.

Fixpoint substIndex (x : Subst) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | sub_here    , O   => t
    | sub_here    , S y => var y
    | sub_var x   , O   => var O
    | sub_var x   , S y => shiftTm O (substIndex x t y)
    | sub_bound x , y   => tshiftTm O (substIndex x t y)
  end.

Fixpoint substTm (x : Subst) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substIndex x t' y
    | abs T1 t2    => abs T1 (substTm (sub_var x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
    | tabs T1 t2   => tabs T1 (substTm (sub_bound x) t' t2)
    | tapp t1 T2   => tapp (substTm x t' t1) T2
  end.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Inductive lookup_etvar : Env → nat → Ty → Prop :=
  | gb_here {Γ T} :
      lookup_etvar (etvar Γ T) O (tshiftTy O T)
  | gb_var {Γ T T' X} :
      lookup_etvar Γ X T →
      lookup_etvar (evar Γ T') X T
  | gb_bound {Γ T T' X} :
      lookup_etvar Γ X T →
      lookup_etvar (etvar Γ T') (S X) (tshiftTy O T).
Hint Constructors lookup_etvar.

Inductive lookup_evar : Env → nat → Ty → Prop :=
  | gv_here {Γ T} :
      lookup_evar (evar Γ T) O T
  | gv_var {Γ T T' X} :
      lookup_evar Γ X T →
      lookup_evar (evar Γ T') (S X) T
  | gv_bound {Γ T T' X} :
      lookup_evar Γ X T →
      lookup_evar (etvar Γ T') X (tshiftTy O T).
Hint Constructors lookup_evar.

(******************************************************************************)
(* Well-formedness.                                                           *)
(******************************************************************************)

(* These LoC shouldn't be counted here.. *)
Inductive wfTy (Γ: Env) : Ty → Prop :=
  | wf_tvar {X T} :
      lookup_etvar Γ X T → wfTy Γ (tvar X)
  | wf_top :
      wfTy Γ top
  | wf_tarr {T1 T2}:
      wfTy Γ T1 → wfTy Γ T2 → wfTy Γ (tarr T1 T2)
  | wf_tall {T1 T2} :
      wfTy Γ T1 → wfTy (etvar Γ T1) T2 →
      wfTy Γ (tall T1 T2).
Hint Constructors wfTy.

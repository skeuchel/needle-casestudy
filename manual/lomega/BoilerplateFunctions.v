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
    | tvar X       => tvar (shiftIndex c X)
    | tabs K T     => tabs K (tshiftTy (S c) T)
    | tapp T1 T2   => tapp (tshiftTy c T1) (tshiftTy c T2)
    | tarr T1 T2   => tarr (tshiftTy c T1) (tshiftTy c T2)
  end.

Fixpoint tshiftTm (c : nat) (t : Tm) : Tm :=
  match t with
    | var x        => var x
    | abs T  t     => abs (tshiftTy c T) (tshiftTm c t)
    | app t1 t2    => app (tshiftTm c t1) (tshiftTm c t2)
  end.


Fixpoint shiftTm (c : nat) (t : Tm) : Tm :=
  match t with
    | var x        => var (shiftIndex c x)
    | abs T1 t2    => abs T1 (shiftTm (S c) t2)
    | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  end.

(******************************************************************************)
(* Type substitution.                                                         *)
(******************************************************************************)

Fixpoint tsubstIndex (X : nat) (T' : Ty) (Y : nat) : Ty :=
  match X , Y with
    | O   , O      => T'
    | O   , S Y    => tvar Y
    | S X , O      => tvar O
    | S X , S Y    => tshiftTy 0 (tsubstIndex X T' Y)
  end.

Fixpoint tsubstTy (X : nat) (T' : Ty) (T : Ty) : Ty :=
  match T with
    | tvar Y       => tsubstIndex X T' Y
    | tabs K T     => tabs K (tsubstTy (S X) T' T)
    | tapp T1 T2   => tapp (tsubstTy X T' T1) (tsubstTy X T' T2)
    | tarr T1 T2   => tarr (tsubstTy X T' T1) (tsubstTy X T' T2)
  end.

Fixpoint tsubstTm (X : nat) (T' : Ty) (t : Tm) : Tm :=
  match t with
    | var x        => var x
    | abs T1 t2    => abs  (tsubstTy X T' T1) (tsubstTm X T' t2)
    | app t1 t2    => app  (tsubstTm X T' t1) (tsubstTm X T' t2)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Inductive Trace : Set :=
  | I0
  | IV (i : Trace)
  | IT (i : Trace).

(*  means [x |-> t] y  *)
Fixpoint substIndex (x : Trace) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | I0   , O     => t
    | I0   , S y   => var y
    | IV x , O     => var O
    | IV x , S y   => shiftTm O (substIndex x t y)
    | IT x , y     => tshiftTm 0 (substIndex x t y)
  end.

(*  means [x |-> t'] t  *)
Fixpoint substTm (x : Trace) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substIndex x t' y
    | abs T1 t2    => abs T1 (substTm (IV x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
  end.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

(* lookup_evar Γ x T  means  x:T ∈ Γ  *)
Inductive lookup_evar : Env → nat → Ty → Prop :=
  | lookup_evar_here {Γ T} :
      lookup_evar (evar Γ T) 0 T
  | lookup_evar_there_evar {Γ T T' x} :
      lookup_evar Γ x T →
      lookup_evar (evar Γ T') (S x) T
  | lookup_evar_there_etvar {Γ T K x} :
      lookup_evar Γ x T →
      lookup_evar (etvar Γ K) x (tshiftTy 0 T).
Hint Constructors lookup_evar.

Inductive lookup_etvar : Env → nat → Kind → Prop :=
  | lookup_etvar_here {Γ K} :
      lookup_etvar (etvar Γ K) 0 K
  | lookup_etvar_there_evar {Γ T T' X} :
      lookup_etvar Γ X T →
      lookup_etvar (evar Γ T') X T
  | lookup_etvar_there_etvar {Γ K K' X} :
      lookup_etvar Γ X K →
      lookup_etvar (etvar Γ K') (S X) K.
Hint Constructors lookup_etvar.

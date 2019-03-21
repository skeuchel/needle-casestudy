Require Import SpecSyntax.
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

Fixpoint shiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var (shiftIndex c x)
  | tt           => tt
  | abs T1 t2    => abs T1 (shiftTm (S c) t2)
  | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Fixpoint substIndex (x : nat) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | 0   , 0   => t
    | 0   , S y => var y
    | S x , 0   => var 0
    | S x , S y => shiftTm 0 (substIndex x t y)
  end.

Fixpoint substTm (x : nat) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substIndex x t' y
    | tt           => tt
    | abs T1 t2    => abs T1 (substTm (S x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
  end.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Inductive lookup_evar : Env → nat → Ty → Prop :=
  | lookup_evar_here {Γ T} :
      lookup_evar (evar Γ T) O T
  | lookup_evar_there_evar {Γ T T' X} :
      lookup_evar Γ X T →
      lookup_evar (evar Γ T') (S X) T.
Hint Constructors lookup_evar.

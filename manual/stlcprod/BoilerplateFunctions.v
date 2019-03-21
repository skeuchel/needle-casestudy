Require Export SpecSyntax.
Set Implicit Arguments.

(******************************************************************************)
(* Context extensions.                                                        *)
(******************************************************************************)

(* A context extension holding the types of pattern variables. *)
Inductive Ext : Set :=
  | exempty
  | exvar   (Δ : Ext) (T : Ty).

Fixpoint extend (Γ : Env) (Δ : Ext) : Env :=
  match Δ with
    | exempty     => Γ
    | exvar Δ T   => evar (extend Γ Δ) T
  end.

Fixpoint append (Δ1 Δ2 : Ext) : Ext :=
  match Δ2 with
    | exempty    => Δ1
    | exvar Δ2 T => exvar (append Δ1 Δ2) T
  end.

Fixpoint lengthExt (Δ : Ext) : nat :=
  match Δ with
    | exempty   => 0
    | exvar Δ _ => 1 + lengthExt Δ
  end.

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
  | prod t1 t2   => prod (shiftTm c t1) (shiftTm c t2)
  | lett p t1 t2 => lett p (shiftTm c t1) (shiftTm (bindPat p + c) t2)
  end.

Fixpoint weakenTm (t : Tm) (k : nat) : Tm :=
  match k with
    | 0   => t
    | S k => shiftTm 0 (weakenTm t k)
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
    | prod t1 t2   => prod (substTm x t' t1) (substTm x t' t2)
    | lett p t1 t2 => lett p (substTm x t' t1)
                        (substTm (bindPat p + x) t' t2)
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

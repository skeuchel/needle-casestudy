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
    | tarr T1 T2  => tarr (tshiftTy c T1) (tshiftTy c T2)
    | tall T      => tall (tshiftTy (S c) T)
  end.

Fixpoint tshiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var x
  | abs T1 t2    => abs (tshiftTy c T1) (tshiftTm c t2)
  | app t1 t2    => app (tshiftTm c t1) (tshiftTm c t2)
  | tabs t2      => tabs (tshiftTm (S c) t2)
  | tapp t1 T2   => tapp (tshiftTm c t1) (tshiftTy c T2)
  | lett ds t1   => lett (tshiftDecls c ds) (tshiftTm c t1)
  end
with tshiftDecls (c : nat) (ds : Decls) : Decls :=
  match ds with
    | dnil  => dnil
    | dcons t ds => dcons (tshiftTm c t) (tshiftDecls c ds)
  end.

Fixpoint shiftTm (c : nat) (t : Tm) : Tm :=
  match t with
  | var x        => var (shiftIndex c x)
  | abs T1 t2    => abs T1 (shiftTm (S c) t2)
  | app t1 t2    => app (shiftTm c t1) (shiftTm c t2)
  | tabs t2      => tabs (shiftTm c t2)
  | tapp t1 T2   => tapp (shiftTm c t1) T2
  | lett ds t1   => lett (shiftDecls c ds) (shiftTm (bind ds + c) t1)
  end
with shiftDecls (c : nat) (ds : Decls) : Decls :=
  match ds with
    | dnil  => dnil
    | dcons t ds => dcons (shiftTm c t) (shiftDecls (S c) ds)
  end.

Fixpoint weakenTm (k : nat) (t : Tm) : Tm :=
  match k with
    | 0   => t
    | S k => shiftTm 0 (weakenTm k t)
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
    | tarr T1 T2  => tarr (tsubstTy X T' T1) (tsubstTy X T' T2)
    | tall T      => tall (tsubstTy (S X) T' T)
  end.

Fixpoint tsubstTm (X : nat) (T' : Ty) (t : Tm) : Tm :=
  match t with
  | var x        => var x
  | abs T1 t2    => abs  (tsubstTy X T' T1) (tsubstTm X T' t2)
  | app t1 t2    => app  (tsubstTm X T' t1) (tsubstTm X T' t2)
  | tabs t2      => tabs (tsubstTm (S X) T' t2)
  | tapp t1 T2   => tapp (tsubstTm X T' t1) (tsubstTy X T' T2)
  | lett ds t1   => lett (tsubstDecls X T' ds) (tsubstTm X T' t1)
  end
with tsubstDecls (X : nat) (T' : Ty) (ds : Decls) : Decls :=
  match ds with
    | dnil  => dnil
    | dcons t ds => dcons (tsubstTm X T' t) (tsubstDecls X T' ds)
  end.

(******************************************************************************)
(* Term substitutions.                                                        *)
(******************************************************************************)

Inductive Subst : Set :=
  | sub_here  : Subst
  | sub_var   : Subst → Subst
  | sub_tvar  : Subst → Subst.

Fixpoint weakenSubst (k : nat) (sub : Subst) : Subst :=
  match k with
   | O   => sub
   | S k => sub_var (weakenSubst k sub)
  end.

Fixpoint substIndex (x : Subst) (t : Tm) (y : nat) : Tm :=
  match x , y with
    | sub_here    , O   => t
    | sub_here    , S y => var y
    | sub_var x   , O   => var O
    | sub_var x   , S y => shiftTm O (substIndex x t y)
    | sub_tvar x  , y   => tshiftTm O (substIndex x t y)
  end.

Fixpoint substTm (x : Subst) (t' : Tm) (t : Tm) : Tm :=
  match t with
    | var y        => substIndex x t' y
    | abs T1 t2    => abs T1 (substTm (sub_var x) t' t2)
    | app t1 t2    => app (substTm x t' t1) (substTm x t' t2)
    | tabs t2      => tabs (substTm (sub_tvar x) t' t2)
    | tapp t1 T2   => tapp (substTm x t' t1) T2
    | lett ds t1   => lett (substDecls x t' ds)
                        (substTm (weakenSubst (bind ds) x) t' t1)
  end
with substDecls (x : Subst) (t' : Tm) (ds : Decls) : Decls :=
  match ds with
    | dnil => dnil
    | dcons t ds => dcons (substTm x t' t) (substDecls (sub_var x) t' ds)
  end.

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

Fixpoint tshiftExt (c : nat) (Δ : Ext) : Ext :=
  match Δ with
    | exempty    => exempty
    | exvar Δ T  => exvar (tshiftExt c Δ) (tshiftTy c T)
  end.

Fixpoint tsubstExt (X : nat) (T' : Ty) (Δ : Ext) : Ext :=
  match Δ with
    | exempty    => exempty
    | exvar Δ T  => exvar (tsubstExt X T' Δ) (tsubstTy X T' T)
  end.

(******************************************************************************)
(* Context lookups.                                                           *)
(******************************************************************************)

Inductive lookup_etvar : Env → nat → Prop :=
  | gb_here {Γ} :
      lookup_etvar (etvar Γ) O
  | gb_var {Γ T X} :
      lookup_etvar Γ X →
      lookup_etvar (evar Γ T) X
  | gb_tvar {Γ X} :
      lookup_etvar Γ X →
      lookup_etvar (etvar Γ) (S X).
Hint Constructors lookup_etvar.

Inductive lookup_evar : Env → nat → Ty → Prop :=
  | gv_here {Γ T} :
      lookup_evar (evar Γ T) O T
  | gv_var {Γ T T' X} :
      lookup_evar Γ X T →
      lookup_evar (evar Γ T') (S X) T
  | gv_tvar {Γ T X} :
      lookup_evar Γ X T →
      lookup_evar (etvar Γ) X (tshiftTy 0 T).
Hint Constructors lookup_evar.

(******************************************************************************)
(* Well-formed types                                                          *)
(******************************************************************************)

Inductive wfTy : Env → Ty → Prop :=
  | wf_tvar {Γ X} :
      lookup_etvar Γ X → wfTy Γ (tvar X)
  | wf_tarr {Γ T1 T2} :
      wfTy Γ T1 → wfTy Γ T2 → wfTy Γ (tarr T1 T2)
  | wf_tall {Γ T} :
      wfTy (etvar Γ) T → wfTy Γ (tall T).
Hint Constructors wfTy.

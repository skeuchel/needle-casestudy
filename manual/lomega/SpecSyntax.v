Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Kind : Set :=
  | star
  | karr (K1 K2 : Kind).

Inductive Ty : Set :=
  | tvar (X : nat)
  | tabs (K : Kind) (T : Ty)
  | tapp (T1 T2 : Ty)
  | tarr (T1 T2 : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Tm : Set :=
  | var   (x  : nat)
  | abs   (T  : Ty) (t  : Tm)
  | app   (t1 t2 : Tm).

(******************************************************************************)
(* Representation of contexts.                                                *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | evar  (Γ : Env) (T : Ty)
  | etvar (Γ : Env) (K : Kind).

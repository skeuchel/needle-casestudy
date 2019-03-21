Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tunit
  | tarr (T1 T2 : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Tm : Set :=
  | var  (x  : nat)
  | tt
  | abs  (T  : Ty) (t  : Tm)
  | app  (t1 : Tm) (t2 : Tm).

(******************************************************************************)
(* Representation of contexts, extensions.                                    *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | evar   (Γ : Env) (T : Ty).

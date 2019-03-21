Require Export Coq.Unicode.Utf8.
Require Export Coq.Program.Equality.
Require Export Coq.Program.Tactics.

(******************************************************************************)
(* Representation of types.                                                   *)
(******************************************************************************)

Inductive Ty : Set :=
  | tvar (X : nat)
  | tarr (T1 T2 : Ty)
  | tall (T : Ty).

(******************************************************************************)
(* Representation of terms.                                                   *)
(******************************************************************************)

Inductive Tm : Set :=
  | var  (x  : nat)
  | abs  (T  : Ty) (t  : Tm)
  | app  (t1 : Tm) (t2 : Tm)
  | tabs (t  : Tm)
  | tapp (t  : Tm) (T  : Ty).

(******************************************************************************)
(* Representation of contexts, extensions.                                    *)
(******************************************************************************)

Inductive Env : Set :=
  | empty
  | etvar (Γ : Env)
  | evar  (Γ : Env) (T : Ty).
